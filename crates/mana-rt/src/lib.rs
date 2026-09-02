//! mana runtime — SMP scheduler with per-scheduler nurseries and a shared
//! old generation.
//!
//! # Term representation (contract with mana-codegen)
//!
//! Terms are 64-bit words. The low 3 bits are the primary tag:
//!
//! | tag   | meaning                                                        |
//! |-------|----------------------------------------------------------------|
//! | 0b000 | boxed pointer (8-aligned). First word is a header (see below)  |
//! | 0b001 | small integer, value = word >> 3 (arithmetic)                  |
//! | 0b010 | atom: pointer to `{ len: u64, bytes: [u8; len] }` (static)     |
//! | 0b011 | nil `[]` (the whole word is 3)                                 |
//! | 0b100 | cons cell: pointer to `[head, tail]`                           |
//! | 0b101 | exception sentinel (never a term; see codegen)                 |
//! | 0b110 | pid (process id << 3)                                          |
//! | 0b111 | GC forwarding marker (never visible to compiled code)          |
//!
//! Boxed header word: low 8 bits = kind (0 tuple, 1 float, 2 fun); tuples
//! keep arity in bits 8+, funs keep arity in bits 8-15 and capture count in
//! bits 16+ (payload: code pointer, then captures).
//!
//! # Process context (ABI contract with mana-codegen)
//!
//! One ProcCtx per scheduler thread; compiled code reads/writes fixed word
//! offsets: 0 `heap_top` (nursery bump, inline fast path), 1 `heap_end`,
//! 2 `roots_head` (frame chain `[prev, len, slots...]`, zero = empty slot),
//! 3 `exc_class`, 4 `exc_reason`, 5 `reductions`.
//!
//! # Heap organization (SMP)
//!
//! Each scheduler owns a private nursery; the old generation is shared,
//! chunked, and non-moving between majors. The invariants that make this
//! work without barriers or hot-path locks:
//!
//! * Terms are immutable and only reference older terms — no old→young
//!   pointers, so **minor collections are entirely scheduler-local**.
//! * Anything that crosses processes (message payloads, spawn closures) is
//!   **promoted to the shared old space at send time** (young parts copied
//!   once; a long-lived payload becomes old at the sender's next minor and
//!   then transfers zero-copy forever; old parts always pass by pointer).
//!   Hence no scheduler ever holds references into another's nursery.
//! * Major collections (old space over limit) stop the world: schedulers
//!   park at safepoints (scheduler loop, allocation slow path); the
//!   requester evacuates all nurseries, then compacts the old space.
//!
//! Processes are corosensei coroutines **pinned to their home scheduler**;
//! only the home thread touches a process's coroutine/cursor/saved state.
//! Cross-thread interaction is limited to mailbox pushes, state flips, and
//! condvar wakes.
//!
//! TODO(stacks): process stacks are fixed (root 32MB, spawned 1MB).
//! TODO(split): this file wants to become term.rs / gc.rs / sched.rs.

use std::cell::UnsafeCell;
use std::collections::VecDeque;
use std::io::Write;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use crossbeam_queue::SegQueue;
use parking_lot::{Condvar, Mutex, RwLock};

use corosensei::stack::DefaultStack;
use corosensei::{Coroutine, CoroutineResult, Yielder};

pub const TAG_MASK: u64 = 0b111;
pub const TAG_BOXED: u64 = 0b000;
pub const TAG_SMALL: u64 = 0b001;
pub const TAG_ATOM: u64 = 0b010;
pub const NIL: u64 = 0b011;
pub const TAG_CONS: u64 = 0b100;
/// Identifier class: bit 3 discriminates — pid `id<<4|0110`, ref
/// `id<<4|1110`. Both immediates: raw-word equality and GC-transparent.
pub const TAG_PID: u64 = 0b110;
pub const PID_TAG4: u64 = 0b0110;
pub const REF_TAG4: u64 = 0b1110;
pub const TAG_FORWARD: u64 = 0b111;

/// Matches mana-codegen's exception sentinel (tag 0b101).
const EXC_SENTINEL: u64 = 0b101;

pub const KIND_TUPLE: u64 = 0;
pub const KIND_FLOAT: u64 = 1;
/// Fun object: `[header | code_ptr | captured terms...]`.
/// Header: bits 0-7 kind, bits 8-15 arity, bits 16+ number of captures.
pub const KIND_FUN: u64 = 2;
/// Flatmap: `[header(size<<8|4) | k1..kn | v1..vn]`, keys canonically
/// sorted (term order with an exactness tiebreak: 1 before 1.0).
pub const KIND_MAP: u64 = 4;
pub const KIND_BIN: u64 = 5;
/// Real bignum: `[header(limbs<<9 | sign<<8 | 3) | limbs (LE u64)...]`,
/// normalized (never a value that fits the 61-bit small range, no leading
/// zero limbs; sign bit set = negative). Allocated in the SHARED OLD SPACE
/// (alloc_shared: pure bump, never a GC point) so arithmetic keeps its
/// no-frame fast paths. No term fields — GC copies limbs verbatim.
pub const KIND_BIGNUM: u64 = 3;
/// Sub-binary view: `[header(len<<8|13) | parent_term | byte_offset]` — a
/// zero-copy slice of a ROOT KIND_BIN (never of another view; slicing a
/// view folds offsets). Same header convention as KIND_BIN so the inline
/// length preflight works for both; kinds 5 (0b0101) and 13 (0b1101)
/// differ only in bit 3, so `(kind | 8) == 13` accepts either. Kind 7 is
/// FORBIDDEN for heap objects: header low bits 0b111 collide with the
/// GC's TAG_FORWARD marker. The parent is a TERM (it moves under GC) —
/// data pointers are recomputed on every access, never cached.
pub const KIND_SUBBIN: u64 = 13;

mod bigint;

const NURSERY_WORDS: usize = 16 * 1024; // 128 KiB

/// MANA_NURSERY_WORDS overrides the initial nursery size AND pins it
/// (adaptive growth disabled) — a GC-stress knob for shaking out rooting
/// bugs: tiny nurseries make every allocation path face constant minors.
fn nursery_words_override() -> Option<usize> {
    std::env::var("MANA_NURSERY_WORDS").ok()?.parse().ok()
}

fn initial_nursery_words() -> usize {
    nursery_words_override().unwrap_or(NURSERY_WORDS)
}
const OLD_CHUNK_WORDS: usize = 64 * 1024;
const OLD_LIMIT_INIT: usize = 4 * OLD_CHUNK_WORDS;
/// Reservation only — anonymous pages commit lazily on first touch.
const STACK_BYTES: usize = 256 * 1024 * 1024; // lazy-commit reservation — TODO(stacks): growable
const ROOT_STACK_BYTES: usize = 512 * 1024 * 1024; // lazy-commit reservation
const REDUCTIONS_PER_SLICE: i64 = 4000;

// ---------------------------------------------------------------------------
// memory primitives

struct Chunk {
    start: *mut u64,
    top: *mut u64,
    end: *mut u64,
    words: usize,
}
unsafe impl Send for Chunk {}

fn alloc_space(words: usize) -> *mut u64 {
    let layout = std::alloc::Layout::from_size_align(words * 8, 8).expect("bad heap size");
    let p = unsafe { std::alloc::alloc(layout) } as *mut u64;
    if p.is_null() {
        eprintln!("mana: out of memory");
        std::process::exit(70);
    }
    p
}

unsafe fn free_space(p: *mut u64, words: usize) {
    let layout = std::alloc::Layout::from_size_align(words * 8, 8).unwrap();
    unsafe { std::alloc::dealloc(p as *mut u8, layout) };
}

fn payload_words(header: u64) -> usize {
    match header & 0xff {
        KIND_TUPLE => (header >> 8) as usize,
        KIND_FLOAT => 1,
        KIND_FUN => 1 + (header >> 16) as usize,
        KIND_MAP => 2 * (header >> 8) as usize,
        KIND_BIN => ((header >> 8) as usize + 7) / 8,
        KIND_SUBBIN => 2, // parent term + byte offset (len lives in the header)
        KIND_BIGNUM => (header >> 9) as usize,
        _ => 0,
    }
}

// ---------------------------------------------------------------------------
// global state

struct OldSpace {
    chunks: Vec<Chunk>,
}

impl OldSpace {
    /// Bump-allocate in the shared old space (caller holds the lock).
    fn alloc(&mut self, words: usize, used: &AtomicUsize) -> *mut u64 {
        if let Some(chunk) = self.chunks.last_mut() {
            unsafe {
                if chunk.top.add(words) <= chunk.end {
                    let p = chunk.top;
                    chunk.top = chunk.top.add(words);
                    used.fetch_add(words, Ordering::Relaxed);
                    return p;
                }
            }
        }
        let chunk_words = usize::max(
            self.chunks.last().map_or(OLD_CHUNK_WORDS, |c| c.words * 2),
            words,
        );
        let start = alloc_space(chunk_words);
        self.chunks.push(Chunk {
            start,
            top: unsafe { start.add(words) },
            end: unsafe { start.add(chunk_words) },
            words: chunk_words,
        });
        used.fetch_add(words, Ordering::Relaxed);
        start
    }
}

#[derive(Clone, Copy, PartialEq)]
enum PState {
    Runnable,
    Running,
    /// waiting for a message, with an optional wake deadline
    Waiting(Option<Instant>),
}

type ProcCoro = Coroutine<(), (), u64, DefaultStack>;

struct Process {
    home: usize,
    coro: Option<ProcCoro>,
    yielder: *const Yielder<(), ()>,
    saved_roots: u64,
    saved_exc_class: u64,
    saved_exc_reason: u64,
    /// lock-free sender-side queue. Cross-scheduler senders only ever push
    /// old-space/immediate terms (send promotes); same-scheduler pushes may
    /// be young (local minors drain + scan).
    ingress: SegQueue<u64>,
    /// receiver-private message list — home scheduler only, no lock
    private: Vec<u64>,
    /// receive cursor into `private` — home scheduler only
    cursor: usize,
    state: Mutex<PState>,
    /// spawn closure (old-space) until first resume
    pending_closure: u64,
    /// links/monitors/trap flag — mutated cross-thread under this lock
    lstate: Mutex<LinkState>,
    /// process dictionary. Values are promoted at put, so cross-thread
    /// readers (process_info) only ever see old-space/immediate terms.
    pdict: Mutex<Vec<(u64, u64)>>,
    /// may this process reference its home scheduler's CURRENT nursery?
    /// Set when it runs (swap-out) or receives any message; cleared by the
    /// minor that scans it. Clean parked processes are skipped by minors —
    /// a parked process only gains nursery refs by running or by a local
    /// send, and its previous refs were forwarded by the prior minor.
    dirty: std::sync::atomic::AtomicBool,
}

#[derive(Default)]
struct LinkState {
    links: Vec<usize>,
    /// (ref id, watcher pid) — processes monitoring me
    monitors_on_me: Vec<(u64, usize)>,
    /// (ref id, target pid) — processes I monitor
    monitoring: Vec<(u64, usize)>,
    trap_exit: bool,
    /// pending unhandled exit signal: reason term (old-space/eternal), 0 = none
    pending_kill: u64,
}

/// Home-scheduler pinning makes the interior safe: only the home thread (or
/// the STW requester while everyone is parked) touches non-Mutex fields.
struct ProcessCell(UnsafeCell<Process>);
unsafe impl Send for ProcessCell {}
unsafe impl Sync for ProcessCell {}

struct SchedShared {
    /// pids made runnable by other threads (lock-free)
    inject: SegQueue<usize>,
    /// wake signal for an idle scheduler; the bool defeats lost wakeups
    cv: Condvar,
    cv_m: Mutex<bool>,
    /// registered ProcCtx pointer (for the STW requester)
    ctx_addr: AtomicUsize,
}

struct StwState {
    collecting: bool,
    parked: usize,
    gen: u64,
}

struct Global {
    n_scheds: usize,
    /// fast-path flag mirroring StwState.collecting
    stw_flag: AtomicBool,
    scheds: Vec<SchedShared>,
    procs: RwLock<Vec<Option<&'static ProcessCell>>>,
    old: Mutex<OldSpace>,
    old_used: AtomicUsize,
    old_limit: AtomicUsize,
    eternal: Mutex<Vec<(usize, bool)>>,
    stw: Mutex<StwState>,
    stw_cv: Condvar,
    spawn_rr: AtomicUsize,
    shutdown: AtomicBool,
    gc_log: bool,
}

#[repr(C)]
pub struct ProcCtx {
    pub heap_top: *mut u64, // word 0 — codegen contract (nursery)
    pub heap_end: *mut u64, // word 1 — codegen contract (nursery)
    pub roots_head: u64,    // word 2 — codegen contract
    pub exc_class: u64,     // word 3 — codegen contract
    pub exc_reason: u64,    // word 4 — codegen contract
    pub reductions: i64,    // word 5 — codegen contract
    nursery_start: *mut u64,
    nursery_words: usize,
    global: &'static Global,
    sched_id: usize,
    run_q: VecDeque<usize>,
    current: usize,
    /// cached &ProcessCell of the running process (hot path: recv primops)
    current_cell: usize,
}

fn proc_ref(g: &Global, pid: usize) -> Option<&'static ProcessCell> {
    g.procs.read().get(pid).copied().flatten()
}

/// Home-thread (or STW-requester) access to a process's interior.
#[allow(clippy::mut_from_ref)]
unsafe fn proc_mut(cell: &ProcessCell) -> &mut Process {
    unsafe { &mut *cell.0.get() }
}

fn make_pid(id: usize) -> u64 {
    ((id as u64) << 4) | PID_TAG4
}

fn pid_id(t: u64) -> Option<usize> {
    (t & 0xF == PID_TAG4).then_some((t >> 4) as usize)
}

static REF_COUNTER: AtomicUsize = AtomicUsize::new(1);

/// Well-known atom terms registered by the generated main (atoms are
/// compiler statics; the runtime cannot mint them).
#[derive(Default)]
struct KnownAtoms {
    normal: u64,
    killed: u64,
    kill: u64,
    exit_up: u64,   // 'EXIT'
    down_up: u64,   // 'DOWN'
    process: u64,
    noproc: u64,
    true_a: u64,
    false_a: u64,
    badarg: u64,
    error_a: u64,
    badmap: u64,
    badkey: u64,
    undef: u64,
    ok: u64,
    module: u64,
    nofile: u64,
    value: u64,
    undefined: u64,
    badarith: u64,
}
static KNOWN: std::sync::OnceLock<KnownAtoms> = std::sync::OnceLock::new();

fn known() -> &'static KnownAtoms {
    KNOWN.get().expect("atom table not registered")
}

/// Called by the generated main before mana_rt_run.
#[no_mangle]
pub extern "C" fn mana_rt_register_atoms(
    normal: u64,
    killed: u64,
    kill: u64,
    exit_up: u64,
    down_up: u64,
    process: u64,
    noproc: u64,
    true_a: u64,
    false_a: u64,
    badarg: u64,
    error_a: u64,
    badmap: u64,
    badkey: u64,
    undef: u64,
    ok: u64,
    module: u64,
    nofile: u64,
    value: u64,
    undefined: u64,
    badarith: u64,
) {
    let _ = KNOWN.set(KnownAtoms {
        normal,
        killed,
        kill,
        exit_up,
        down_up,
        process,
        noproc,
        true_a,
        false_a,
        badarg,
        error_a,
        badmap,
        badkey,
        undef,
        ok,
        module,
        nofile,
        value,
        undefined,
        badarith,
    });
}

fn make_ref_term() -> u64 {
    ((REF_COUNTER.fetch_add(1, Ordering::Relaxed) as u64) << 4) | REF_TAG4
}

fn in_my_nursery(ctx: &ProcCtx, addr: u64) -> bool {
    let start = ctx.nursery_start as u64;
    addr >= start && addr < start + (ctx.nursery_words as u64) * 8
}

// ---------------------------------------------------------------------------
// initialization & scheduler loop

#[no_mangle]
pub extern "C" fn mana_rt_init() -> *mut ProcCtx {
    let n: usize = std::env::var("MANA_SCHEDULERS")
        .ok()
        .and_then(|s| s.parse().ok())
        .filter(|&n| (1..=1024).contains(&n))
        .unwrap_or(1);
    let global: &'static Global = Box::leak(Box::new(Global {
        n_scheds: n,
        stw_flag: AtomicBool::new(false),
        scheds: (0..n)
            .map(|_| SchedShared {
                inject: SegQueue::new(),
                cv: Condvar::new(),
                cv_m: Mutex::new(false),
                ctx_addr: AtomicUsize::new(0),
            })
            .collect(),
        procs: RwLock::new(Vec::new()),
        old: Mutex::new(OldSpace { chunks: Vec::new() }),
        old_used: AtomicUsize::new(0),
        old_limit: AtomicUsize::new(OLD_LIMIT_INIT),
        eternal: Mutex::new(Vec::new()),
        stw: Mutex::new(StwState {
            collecting: false,
            parked: 0,
            gen: 0,
        }),
        stw_cv: Condvar::new(),
        spawn_rr: AtomicUsize::new(1),
        shutdown: AtomicBool::new(false),
        gc_log: std::env::var_os("MANA_GC_LOG").is_some(),
    }));
    new_sched_ctx(global, 0)
}

fn new_sched_ctx(global: &'static Global, sched_id: usize) -> *mut ProcCtx {
    let nwords = initial_nursery_words();
    let nursery = alloc_space(nwords);
    let ctx = Box::into_raw(Box::new(ProcCtx {
        heap_top: nursery,
        heap_end: unsafe { nursery.add(nwords) },
        roots_head: 0,
        exc_class: 0,
        exc_reason: 0,
        reductions: REDUCTIONS_PER_SLICE,
        nursery_start: nursery,
        nursery_words: nwords,
        global,
        sched_id,
        run_q: VecDeque::new(),
        current: usize::MAX,
        current_cell: 0,
    }));
    global.scheds[sched_id]
        .ctx_addr
        .store(ctx as usize, Ordering::Release);
    ctx
}

fn wake_sched(g: &Global, id: usize) {
    let s = &g.scheds[id];
    let mut pending = s.cv_m.lock();
    *pending = true;
    s.cv.notify_all();
}

fn register_process(g: &Global, p: Process) -> usize {
    let cell: &'static ProcessCell = Box::leak(Box::new(ProcessCell(UnsafeCell::new(p))));
    let mut tab = g.procs.write();
    tab.push(Some(cell));
    tab.len() - 1
}

/// Coroutine for a spawned process: applies the (old-space) closure.
fn make_coroutine(global: &'static Global, home: usize) -> ProcCoro {
    let stack = DefaultStack::new(STACK_BYTES).expect("stack allocation failed");
    Coroutine::with_stack(stack, move |yielder, _| {
        let ctx = global.scheds[home].ctx_addr.load(Ordering::Acquire) as *mut ProcCtx;
        let ctx_ref = unsafe { &mut *ctx };
        let p = cur_proc(ctx_ref);
        p.yielder = yielder as *const _;
        // reload at start: a major may have moved the closure since spawn
        let cl = p.pending_closure;
        p.pending_closure = 0;
        let header = unsafe { *((cl & !TAG_MASK) as *const u64) };
        if header & 0xff == KIND_TUPLE {
            // MFA spawn (spawn_opt/proc_lib): {M, F, Args}
            let tp = cl as *const u64;
            let (m, f, a) = unsafe { (*tp.add(1), *tp.add(2), *tp.add(3)) };
            mana_rt_apply3(ctx, m, f, a)
        } else {
            unsafe {
                let code = *((cl & !TAG_MASK) as *const u64).add(1);
                let f: extern "C" fn(*mut ProcCtx, u64) -> u64 = std::mem::transmute(code);
                f(ctx, cl)
            }
        }
    })
}

/// Drive the schedulers until the root process (pid 0) returns; its result
/// (possibly the exception sentinel) becomes the program result.
#[no_mangle]
pub extern "C" fn mana_rt_run(
    ctx: *mut ProcCtx,
    entry: extern "C" fn(*mut ProcCtx) -> u64,
) -> u64 {
    let global = unsafe { (*ctx).global };

    // the root process: its coroutine calls `entry` directly
    {
        let stack = DefaultStack::new(ROOT_STACK_BYTES).expect("stack allocation failed");
        let coro = Coroutine::with_stack(stack, move |yielder, _| {
            let ctx = global.scheds[0].ctx_addr.load(Ordering::Acquire) as *mut ProcCtx;
            let ctx_ref = unsafe { &mut *ctx };
            cur_proc(ctx_ref).yielder = yielder as *const _;
            entry(ctx)
        });
        let pid = register_process(
            global,
            Process {
                home: 0,
                coro: Some(coro),
                yielder: std::ptr::null(),
                saved_roots: 0,
                saved_exc_class: 0,
                saved_exc_reason: 0,
                ingress: SegQueue::new(),
                private: Vec::new(),
                cursor: 0,
                state: Mutex::new(PState::Runnable),
                pending_closure: 0,
                lstate: Mutex::new(LinkState::default()),
                pdict: Mutex::new(Vec::new()),
            dirty: std::sync::atomic::AtomicBool::new(true),
            },
        );
        debug_assert_eq!(pid, 0);
        unsafe { (*ctx).run_q.push_back(0) };
    }

    for id in 1..global.n_scheds {
        std::thread::spawn(move || {
            let ctx = new_sched_ctx(global, id);
            scheduler_loop(unsafe { &mut *ctx }, None);
        });
    }

    let mut root_result: u64 = 0;
    scheduler_loop(unsafe { &mut *ctx }, Some(&mut root_result));
    global.shutdown.store(true, Ordering::Release);
    for id in 1..global.n_scheds {
        wake_sched(global, id);
    }
    root_result
}

fn scheduler_loop(ctx: &mut ProcCtx, mut root_result: Option<&mut u64>) {
    let global = ctx.global;
    loop {
        if global.shutdown.load(Ordering::Acquire) {
            return;
        }
        park_if_stw(ctx);
        drain_timer_deliveries(ctx);
        drain_io_wakes(ctx);
        drain_io_active(ctx);

        let pid = ctx
            .run_q
            .pop_front()
            .or_else(|| global.scheds[ctx.sched_id].inject.pop());
        let Some(pid) = pid else {
            idle_wait(ctx);
            continue;
        };
        let Some(cell) = proc_ref(global, pid) else {
            continue;
        };
        let p = unsafe { proc_mut(cell) };
        // an exit signal arrived while it was suspended: it never resumes
        {
            let reason = p.lstate.lock().pending_kill;
            if reason != 0 {
                process_death(ctx, pid, reason);
                if pid == 0 {
                    return; // root killed: program ends (result 0)
                }
                continue;
            }
        }
        *p.state.lock() = PState::Running;
        ctx.roots_head = p.saved_roots;
        ctx.exc_class = p.saved_exc_class;
        ctx.exc_reason = p.saved_exc_reason;
        ctx.reductions = REDUCTIONS_PER_SLICE;
        ctx.current = pid;
        ctx.current_cell = (cell as *const ProcessCell) as usize;

        let mut coro = p.coro.take().unwrap();
        match coro.resume(()) {
            CoroutineResult::Yield(()) => {
                p.coro = Some(coro);
                p.saved_roots = ctx.roots_head;
                p.saved_exc_class = ctx.exc_class;
                p.saved_exc_reason = ctx.exc_reason;
                // it ran: its roots/queues may reference the nursery
                p.dirty.store(true, Ordering::Release);
                let killed = p.lstate.lock().pending_kill;
                if killed != 0 {
                    process_death(ctx, pid, killed);
                    if pid == 0 {
                        return;
                    }
                } else {
                    let mut st = p.state.lock();
                    if *st == PState::Running {
                        *st = PState::Runnable;
                        drop(st);
                        ctx.run_q.push_back(pid);
                    }
                }
            }
            CoroutineResult::Return(v) => {
                let reason = if v == EXC_SENTINEL {
                    // an uncaught exit with reason normal/shutdown/{shutdown,_}
                    // is an orderly termination (gen_server stop, socket
                    // close) — silent, like BEAM
                    let quiet = ctx.exc_class == find_atom("exit").unwrap_or(0)
                        && exit_reason_is_quiet(ctx.exc_reason);
                    if pid != 0 && !quiet {
                        let mut class = String::new();
                        let mut reason = String::new();
                        write_term(ctx.exc_class, &mut class);
                        write_term(ctx.exc_reason, &mut reason);
                        eprintln!(
                            "mana: process <0.{}.0> exited: {} {}",
                            pid, class, reason
                        );
                    }
                    ctx.exc_reason // eternal/immediate: shared-safe
                } else {
                    known().normal
                };
                process_death(ctx, pid, reason);
                if pid == 0 {
                    if let Some(out) = root_result.as_deref_mut() {
                        *out = v;
                    }
                    return;
                }
            }
        }
        ctx.current = usize::MAX;
    }
}

/// No runnable process: wake due sleepers, or sleep until the nearest
/// deadline / an external wake.
fn idle_wait(ctx: &mut ProcCtx) {
    let global = ctx.global;
    let now = Instant::now();
    let mut nearest: Option<Instant> = None;
    {
        let tab = global.procs.read();
        for (id, slot) in tab.iter().enumerate() {
            let Some(cell) = slot else { continue };
            let p = unsafe { &*cell.0.get() };
            if p.home != ctx.sched_id {
                continue;
            }
            let mut st = p.state.lock();
            if let PState::Waiting(Some(dl)) = *st {
                if dl <= now {
                    *st = PState::Runnable;
                    ctx.run_q.push_back(id);
                } else if nearest.is_none_or(|n| dl < n) {
                    nearest = Some(dl);
                }
            }
        }
    }
    if !ctx.run_q.is_empty() {
        return;
    }
    let s = &global.scheds[ctx.sched_id];
    let mut pending = s.cv_m.lock();
    if *pending {
        *pending = false;
        return;
    }
    let timeout = nearest
        .map(|dl| dl.saturating_duration_since(Instant::now()))
        .unwrap_or(Duration::from_millis(100));
    s.cv.wait_for(&mut pending, timeout);
    *pending = false;
}

fn suspend_current(ctx: &mut ProcCtx) {
    let yielder = cur_proc(ctx).yielder;
    unsafe { (*yielder).suspend(()) };
}

// ---------------------------------------------------------------------------
// promotion: copy young parts of a term into the shared old space

fn term_in_nursery(ctx: &ProcCtx, t: u64) -> bool {
    match t & TAG_MASK {
        TAG_CONS => in_my_nursery(ctx, t & !TAG_MASK),
        TAG_BOXED if t != 0 => in_my_nursery(ctx, t),
        _ => false,
    }
}

/// Deep-copy every part of `t` living in this scheduler's nursery into the
/// shared old space. Old/eternal/immediate parts pass zero-copy. The source
/// is not mutated (no forwarding), so sharing within one message flattens —
/// the same trade BEAM's copying send makes. Iterative: payloads can be
/// arbitrarily deep and this runs on a small coroutine stack.
fn promote_term(ctx: &mut ProcCtx, t: u64) -> u64 {
    if !term_in_nursery(ctx, t) {
        return t;
    }
    let global = ctx.global;
    let mut old = global.old.lock();
    let root = promote_copy(ctx, &mut old, t);
    let mut scan: Vec<u64> = vec![root];
    while let Some(nt) = scan.pop() {
        unsafe {
            let (p, base, n) = match nt & TAG_MASK {
                TAG_CONS => ((nt & !TAG_MASK) as *mut u64, 0usize, 2usize),
                TAG_BOXED => {
                    let p = nt as *mut u64;
                    let header = *p;
                    match header & 0xff {
                        KIND_TUPLE => (p, 1, (header >> 8) as usize),
                        KIND_FUN => (p, 2, (header >> 16) as usize),
                        KIND_MAP => (p, 1, 2 * (header >> 8) as usize),
                        KIND_SUBBIN => (p, 1, 1),
                        _ => (p, 0, 0),
                    }
                }
                _ => continue,
            };
            for i in 0..n {
                let f = p.add(base + i);
                if term_in_nursery(ctx, *f) {
                    *f = promote_copy(ctx, &mut old, *f);
                    scan.push(*f);
                }
            }
        }
    }
    root
}

/// Copy one object (shallow) into old space, preserving the tag.
fn promote_copy(ctx: &ProcCtx, old: &mut OldSpace, t: u64) -> u64 {
    let g = ctx.global;
    unsafe {
        match t & TAG_MASK {
            TAG_CONS => {
                let p = (t & !TAG_MASK) as *const u64;
                let new = old.alloc(2, &g.old_used);
                *new = *p;
                *new.add(1) = *p.add(1);
                new as u64 | TAG_CONS
            }
            TAG_BOXED => {
                let p = t as *const u64;
                let words = 1 + payload_words(*p);
                let new = old.alloc(words, &g.old_used);
                std::ptr::copy_nonoverlapping(p, new, words);
                new as u64
            }
            _ => t,
        }
    }
}

// ---------------------------------------------------------------------------
// exit signals, links, monitors

/// Allocate `words` in the shared old space (visible to every process).
fn alloc_shared(ctx: &mut ProcCtx, words: usize) -> *mut u64 {
    let g = ctx.global;
    let mut old = g.old.lock();
    old.alloc(words, &g.old_used)
}

/// Build a tuple in shared space; items must be old/eternal/immediate.
fn shared_tuple(ctx: &mut ProcCtx, items: &[u64]) -> u64 {
    let p = alloc_shared(ctx, 1 + items.len());
    unsafe {
        *p = ((items.len() as u64) << 8) | KIND_TUPLE;
        for (i, v) in items.iter().enumerate() {
            *p.add(1 + i) = *v;
        }
    }
    p as u64
}

/// Push an (already shared-safe) message and wake the target.
fn push_and_wake(ctx: &mut ProcCtx, id: usize, msg: u64) {
    let global = ctx.global;
    let Some(cell) = proc_ref(global, id) else {
        return;
    };
    let p = unsafe { &*cell.0.get() };
    p.dirty.store(true, Ordering::Release);
    p.ingress.push(msg);
    let mut st = p.state.lock();
    if matches!(*st, PState::Waiting(_)) {
        *st = PState::Runnable;
        drop(st);
        if p.home == ctx.sched_id {
            ctx.run_q.push_back(id);
        } else {
            global.scheds[p.home].inject.push(id);
            wake_sched(global, p.home);
        }
    }
}

/// Deliver an exit signal to `target`. `forced` = exit(Pid, kill).
fn exit_signal(ctx: &mut ProcCtx, from_pid: usize, target: usize, reason: u64, forced: bool) {
    let g = ctx.global;
    // the reason lands in old-space tuples and cross-scheduler pending_kill:
    // young terms would be missed by minors (no remembered set)
    let reason = promote_term(ctx, reason);
    let Some(cell) = proc_ref(g, target) else {
        return;
    };
    let p = unsafe { proc_mut(cell) };
    let mut ls = p.lstate.lock();
    if ls.trap_exit && !forced {
        drop(ls);
        let msg = shared_tuple(ctx, &[known().exit_up, make_pid(from_pid), reason]);
        push_and_wake(ctx, target, msg);
        return;
    }
    if reason == known().normal && !forced {
        return;
    }
    ls.pending_kill = reason;
    drop(ls);
    // wake it so its home scheduler notices the pending kill
    let mut st = p.state.lock();
    if matches!(*st, PState::Waiting(_)) {
        *st = PState::Runnable;
        drop(st);
        if p.home == ctx.sched_id {
            ctx.run_q.push_back(target);
        } else {
            g.scheds[p.home].inject.push(target);
            wake_sched(g, p.home);
        }
    }
}

/// A process is gone: notify monitors, propagate to links, free the slot.
fn process_death(ctx: &mut ProcCtx, pid: usize, reason: u64) {
    let g = ctx.global;
    // the reason goes into old-space DOWN tuples and exit signals
    let reason = promote_term(ctx, reason);
    let Some(cell) = proc_ref(g, pid) else {
        return;
    };
    if let Some(map) = NAME_REGISTRY.lock().unwrap().as_mut() {
        map.retain(|_, &mut p| p != pid);
    }
    let ls = {
        let p = unsafe { proc_mut(cell) };
        std::mem::take(&mut *p.lstate.lock())
    };
    g.procs.write()[pid] = None;
    for (ref_id, watcher) in ls.monitors_on_me {
        let ref_term = (ref_id << 4) | REF_TAG4;
        let msg = shared_tuple(
            ctx,
            &[known().down_up, ref_term, known().process, make_pid(pid), reason],
        );
        push_and_wake(ctx, watcher, msg);
    }
    for linked in ls.links {
        if let Some(other) = proc_ref(g, linked) {
            let o = unsafe { proc_mut(other) };
            o.lstate.lock().links.retain(|&x| x != pid);
        }
        exit_signal(ctx, pid, linked, reason, false);
    }
    // drop stale monitoring entries on targets I watched
    for (ref_id, target) in ls.monitoring {
        if let Some(t) = proc_ref(g, target) {
            let t = unsafe { proc_mut(t) };
            t.lstate.lock().monitors_on_me.retain(|&(r, _)| r != ref_id);
        }
    }
}

#[no_mangle]
pub extern "C" fn mana_rt_make_ref(_ctx: *mut ProcCtx) -> u64 {
    make_ref_term()
}

/// erlang:link/1 — bidirectional; linking a dead pid delivers noproc.
#[no_mangle]
pub extern "C" fn mana_rt_link(ctx: *mut ProcCtx, pid: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some(id) = pid_id(pid) else { return 0 };
    let me = ctx.current;
    match proc_ref(ctx.global, id) {
        Some(cell) => {
            let p = unsafe { proc_mut(cell) };
            let mut ls = p.lstate.lock();
            if !ls.links.contains(&me) {
                ls.links.push(me);
            }
            drop(ls);
            let mecell = proc_ref(ctx.global, me).unwrap();
            let m = unsafe { proc_mut(mecell) };
            let mut mls = m.lstate.lock();
            if !mls.links.contains(&id) {
                mls.links.push(id);
            }
        }
        None => {
            exit_signal(ctx, id, me, known().noproc, false);
        }
    }
    1
}

#[no_mangle]
pub extern "C" fn mana_rt_unlink(ctx: *mut ProcCtx, pid: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some(id) = pid_id(pid) else { return 0 };
    let me = ctx.current;
    if let Some(cell) = proc_ref(ctx.global, id) {
        unsafe { proc_mut(cell) }.lstate.lock().links.retain(|&x| x != me);
    }
    if let Some(cell) = proc_ref(ctx.global, me) {
        unsafe { proc_mut(cell) }.lstate.lock().links.retain(|&x| x != id);
    }
    1
}

/// erlang:monitor(process, Pid) — returns the ref; dead target → immediate
/// noproc DOWN.
#[no_mangle]
pub extern "C" fn mana_rt_monitor(ctx: *mut ProcCtx, pid: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let r = make_ref_term();
    let ref_id = r >> 4;
    let me = ctx.current;
    let Some(id) = pid_id(pid) else { return r };
    match proc_ref(ctx.global, id) {
        Some(cell) => {
            unsafe { proc_mut(cell) }
                .lstate
                .lock()
                .monitors_on_me
                .push((ref_id, me));
            let mecell = proc_ref(ctx.global, me).unwrap();
            unsafe { proc_mut(mecell) }
                .lstate
                .lock()
                .monitoring
                .push((ref_id, id));
        }
        None => {
            let msg = shared_tuple(
                ctx,
                &[known().down_up, r, known().process, pid, known().noproc],
            );
            push_and_wake(ctx, me, msg);
        }
    }
    r
}

#[no_mangle]
pub extern "C" fn mana_rt_demonitor(ctx: *mut ProcCtx, r: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if r & 0xF != REF_TAG4 {
        return 0;
    }
    drop_alias(r);
    let ref_id = r >> 4;
    let me = ctx.current;
    let target = {
        let mecell = proc_ref(ctx.global, me).unwrap();
        let m = unsafe { proc_mut(mecell) };
        let mut ls = m.lstate.lock();
        let t = ls.monitoring.iter().find(|&&(rid, _)| rid == ref_id).map(|&(_, t)| t);
        ls.monitoring.retain(|&(rid, _)| rid != ref_id);
        t
    };
    if let Some(t) = target {
        if let Some(cell) = proc_ref(ctx.global, t) {
            unsafe { proc_mut(cell) }
                .lstate
                .lock()
                .monitors_on_me
                .retain(|&(rid, _)| rid != ref_id);
        }
    }
    1
}

/// Reply aliases (OTP 24 monitor opts): ref word → target pid. A send to
/// a ref consults this table; absent aliases drop silently (BEAM parity).
static ALIASES: std::sync::Mutex<Option<std::collections::HashMap<u64, usize>>> =
    std::sync::Mutex::new(None);

/// erlang:monitor/3 — monitor/2 plus options. Supported: {alias, _} (all
/// deactivation flavors behave like demonitor — TODO(alias-modes)); other
/// options are ignored.
#[no_mangle]
pub extern "C" fn mana_rt_monitor3(ctx: *mut ProcCtx, pid: u64, opts: u64) -> u64 {
    let r = mana_rt_monitor(ctx, pid);
    let ctxr = unsafe { &mut *ctx };
    let mut cur = opts;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctxr);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let opt = unsafe { *p };
        if opt & TAG_MASK == TAG_BOXED && opt != 0 {
            let hp = opt as *const u64;
            let h = unsafe { *hp };
            if h & 0xff == KIND_TUPLE
                && h >> 8 == 2
                && atom_bytes(unsafe { *hp.add(1) }) == b"alias"
            {
                let mut guard = ALIASES.lock().unwrap();
                guard
                    .get_or_insert_with(Default::default)
                    .insert(r, ctxr.current);
            }
        }
        cur = unsafe { *p.add(1) };
    }
    r
}

fn drop_alias(r: u64) {
    if let Some(map) = ALIASES.lock().unwrap().as_mut() {
        map.remove(&r);
    }
}

/// demonitor/2 with the flush option: also drop any already-delivered
/// {'DOWN', Ref, ...} message. The info option (return false if the DOWN
/// already fired) is approximated by whether a message was flushed.
#[no_mangle]
pub extern "C" fn mana_rt_demonitor_flush(ctx: *mut ProcCtx, r: u64) -> u64 {
    let res = mana_rt_demonitor(ctx, r);
    let ctx = unsafe { &mut *ctx };
    if res == 0 {
        return 0;
    }
    let me = ctx.current;
    let cell = proc_ref(ctx.global, me).unwrap();
    let p = unsafe { proc_mut(cell) };
    while let Some(m) = p.ingress.pop() {
        p.private.push(m);
    }
    let is_down_for = |msg: u64| -> bool {
        if msg & TAG_MASK != TAG_BOXED || msg == 0 {
            return false;
        }
        let tp = msg as *const u64;
        let h = unsafe { *tp };
        h & 0xff == KIND_TUPLE
            && h >> 8 == 5
            && unsafe { *tp.add(1) } == known().down_up
            && unsafe { *tp.add(2) } == r
    };
    let before = p.private.len();
    // removing before the cursor shifts it; adjust so the receive scan
    // position stays on the same message
    let mut removed_before_cursor = 0;
    let cursor = p.cursor;
    let mut i = 0;
    p.private.retain(|&m| {
        let keep = !is_down_for(m);
        if !keep && i < cursor {
            removed_before_cursor += 1;
        }
        i += 1;
        keep
    });
    p.cursor -= removed_before_cursor;
    if p.private.len() != before {
        2 // flushed
    } else {
        1
    }
}

/// erlang:exit/2 — kill is untrappable and propagates as killed.
#[no_mangle]
pub extern "C" fn mana_rt_exit2(ctx: *mut ProcCtx, pid: u64, reason: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some(id) = pid_id(pid) else { return 0 };
    let reason = promote_term(ctx, reason);
    if reason == known().kill {
        exit_signal(ctx, ctx.current, id, known().killed, true);
    } else {
        exit_signal(ctx, ctx.current, id, reason, false);
    }
    1
}

/// process_flag(trap_exit, Bool) — returns the previous value.
#[no_mangle]
pub extern "C" fn mana_rt_trap_exit(ctx: *mut ProcCtx, flag: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let cell = proc_ref(ctx.global, ctx.current).unwrap();
    let p = unsafe { proc_mut(cell) };
    let mut ls = p.lstate.lock();
    let prev = ls.trap_exit;
    ls.trap_exit = flag == known().true_a;
    if prev {
        known().true_a
    } else {
        known().false_a
    }
}

/// erlang:hibernate/3 — discard the (conceptual) stack, wait for a
/// message, then continue at apply(M, F, A). The applied function is not
/// expected to return; if it does, the process exits normally.
#[no_mangle]
pub extern "C" fn mana_rt_hibernate(ctx: *mut ProcCtx, m: u64, f: u64, a: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    // the args list is a heap term held across suspends — root it (the
    // parked coroutine's root-frame chain is scanned and updated by GC)
    let saved = ctxr.roots_head;
    let mut fr = [0u64, 1, a];
    fr[0] = saved;
    ctxr.roots_head = fr.as_ptr() as u64;
    loop {
        let p = cur_proc(ctxr);
        drain_ingress(p);
        if !p.private.is_empty() {
            break;
        }
        *p.state.lock() = PState::Waiting(None);
        suspend_current(ctxr);
    }
    let a = fr[2];
    ctxr.roots_head = saved;
    let r = mana_rt_apply3(ctx, m, f, a);
    if r == EXC_SENTINEL {
        return r;
    }
    let ctxr = unsafe { &mut *ctx };
    ctxr.exc_class = atom_intern(b"exit");
    ctxr.exc_reason = known().normal;
    EXC_SENTINEL
}

/// os:getenv/1 (nif_error stub in os.erl — real BIF on BEAM).
#[no_mangle]
pub extern "C" fn mana_rt_os_getenv(ctx: *mut ProcCtx, name: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut bytes = Vec::new();
    if chardata_flatten(name, &mut bytes).is_err() {
        return raise_badarg(ctx);
    }
    let Ok(name) = String::from_utf8(bytes) else {
        return raise_badarg(ctx);
    };
    match std::env::var(&name) {
        Ok(v) => bytes_to_byte_list(ctx, v.as_bytes()),
        Err(_) => known().false_a,
    }
}

// ---------------------------------------------------------------------------
// External Term Format (term_to_binary/binary_to_term) — the data subset:
// smalls, atoms, nil, lists (byte lists as STRING_EXT like BEAM), tuples,
// maps, floats, binaries. Pids/refs/funs are badarg (TODO(etf)); this
// encoder is also the wire format planned for mana_dist.

fn etf_encode(t: u64, out: &mut Vec<u8>) -> Result<(), ()> {
    match t & TAG_MASK {
        TAG_SMALL => {
            let v = t as i64 >> 3;
            if (0..=255).contains(&v) {
                out.push(97);
                out.push(v as u8);
            } else if (i32::MIN as i64..=i32::MAX as i64).contains(&v) {
                out.push(98);
                out.extend_from_slice(&(v as i32).to_be_bytes());
            } else {
                // SMALL_BIG_EXT for the 61-bit smalls beyond i32
                let (sign, mag) = if v < 0 { (1u8, (-(v as i128)) as u64) } else { (0, v as u64) };
                let bytes = mag.to_le_bytes();
                let n = bytes.iter().rposition(|&b| b != 0).map_or(1, |i| i + 1);
                out.push(110);
                out.push(n as u8);
                out.push(sign);
                out.extend_from_slice(&bytes[..n]);
            }
        }
        TAG_ATOM => {
            let b = atom_bytes(t);
            if b.len() <= 255 {
                out.push(119); // SMALL_ATOM_UTF8_EXT
                out.push(b.len() as u8);
            } else {
                out.push(118);
                out.extend_from_slice(&(b.len() as u16).to_be_bytes());
            }
            out.extend_from_slice(b);
        }
        _ if t == NIL => out.push(106),
        TAG_CONS => {
            // proper byte lists ≤ 65535 encode as STRING_EXT (BEAM parity)
            let mut bytes: Vec<u8> = Vec::new();
            let mut cur = t;
            let mut is_string = true;
            let mut len = 0usize;
            while cur & TAG_MASK == TAG_CONS {
                let p = (cur & !TAG_MASK) as *const u64;
                let h = unsafe { *p };
                len += 1;
                if is_string && h & TAG_MASK == TAG_SMALL && (0..=255).contains(&(h as i64 >> 3)) {
                    bytes.push((h as i64 >> 3) as u8);
                } else {
                    is_string = false;
                }
                cur = unsafe { *p.add(1) };
            }
            if is_string && cur == NIL && len <= 65535 {
                out.push(107);
                out.extend_from_slice(&(len as u16).to_be_bytes());
                out.extend_from_slice(&bytes);
                return Ok(());
            }
            out.push(108); // LIST_EXT
            out.extend_from_slice(&(len as u32).to_be_bytes());
            let mut cur = t;
            while cur & TAG_MASK == TAG_CONS {
                let p = (cur & !TAG_MASK) as *const u64;
                etf_encode(unsafe { *p }, out)?;
                cur = unsafe { *p.add(1) };
            }
            etf_encode(cur, out)?; // tail (NIL for proper lists)
        }
        TAG_BOXED if t != 0 => unsafe {
            let p = t as *const u64;
            match *p & 0xff {
                KIND_TUPLE => {
                    let n = (*p >> 8) as usize;
                    if n <= 255 {
                        out.push(104);
                        out.push(n as u8);
                    } else {
                        out.push(105);
                        out.extend_from_slice(&(n as u32).to_be_bytes());
                    }
                    for i in 1..=n {
                        etf_encode(*p.add(i), out)?;
                    }
                }
                KIND_MAP => {
                    let n = (*p >> 8) as usize;
                    out.push(116);
                    out.extend_from_slice(&(n as u32).to_be_bytes());
                    for i in 0..n {
                        etf_encode(*p.add(1 + i), out)?;
                        etf_encode(*p.add(1 + n + i), out)?;
                    }
                }
                KIND_FLOAT => {
                    out.push(70);
                    let bits = *p.add(1);
                    out.extend_from_slice(&bits.to_be_bytes());
                }
                KIND_BIGNUM => {
                    let (neg, mag) = bignum_parts(t).unwrap();
                    let bytes = bigint::mag_to_bytes_le(mag);
                    if bytes.len() <= 255 {
                        out.push(110); // SMALL_BIG_EXT
                        out.push(bytes.len() as u8);
                    } else {
                        out.push(111); // LARGE_BIG_EXT
                        out.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
                    }
                    out.push(neg as u8);
                    out.extend_from_slice(&bytes);
                }
                KIND_BIN | KIND_SUBBIN => {
                    let bytes = bin_bytes(t);
                    out.push(109);
                    out.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
                    out.extend_from_slice(bytes);
                }
                _ => return Err(()),
            }
        },
        _ => return Err(()), // pids/refs — TODO(etf)
    }
    Ok(())
}

struct EtfDec<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> EtfDec<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], ()> {
        if self.pos + n > self.buf.len() {
            return Err(());
        }
        let s = &self.buf[self.pos..self.pos + n];
        self.pos += n;
        Ok(s)
    }
    fn u8(&mut self) -> Result<u8, ()> {
        Ok(self.take(1)?[0])
    }
    fn u16(&mut self) -> Result<u16, ()> {
        Ok(u16::from_be_bytes(self.take(2)?.try_into().unwrap()))
    }
    fn u32(&mut self) -> Result<u32, ()> {
        Ok(u32::from_be_bytes(self.take(4)?.try_into().unwrap()))
    }
}

/// Decode one term. `safe` refuses atoms not already interned. All heap
/// results are built with the partial term rooted via a caller frame —
/// here we allocate bottom-up and root intermediates in Rust Vecs of
/// ETERNAL-safe? No: we allocate in the nursery; every recursive result
/// is immediately stored into its parent allocation, and parents are
/// allocated AFTER children — children must be rooted across the parent
/// alloc. We use a per-call stack frame for the child list.
fn etf_decode(ctx: &mut ProcCtx, d: &mut EtfDec, safe: bool) -> Result<u64, ()> {
    let tag = d.u8()?;
    match tag {
        97 => Ok(((d.u8()? as i64) << 3) as u64 | TAG_SMALL),
        98 => {
            let v = i32::from_be_bytes(d.take(4)?.try_into().unwrap()) as i64;
            Ok(((v << 3) as u64) | TAG_SMALL)
        }
        110 | 111 => {
            let n = if tag == 110 {
                d.u8()? as usize
            } else {
                u32::from_be_bytes(d.take(4)?.try_into().unwrap()) as usize
            };
            let sign = d.u8()?;
            let mag_bytes = d.take(n)?.to_vec();
            let mag = bigint::mag_from_bytes_le(&mag_bytes);
            Ok(make_int_mag(ctx, sign == 1 && !mag.is_empty(), &mag))
        }
        118 | 119 | 100 | 115 => {
            let n = if tag == 119 || tag == 115 {
                d.u8()? as usize
            } else {
                d.u16()? as usize
            };
            let name = d.take(n)?;
            if safe && !atom_exists(name) {
                return Err(());
            }
            Ok(atom_intern(name))
        }
        106 => Ok(NIL),
        107 => {
            let n = d.u16()? as usize;
            let bytes = d.take(n)?.to_vec();
            Ok(bytes_to_byte_list(ctx, &bytes))
        }
        108 => {
            let n = d.u32()? as usize;
            // per-call root frame: [prev, len, children...] in a Vec whose
            // capacity is fixed up front (the buffer must never move)
            let saved = ctx.roots_head;
            let mut fr: Vec<u64> = Vec::with_capacity(3 + n);
            fr.push(saved);
            fr.push(0);
            ctx.roots_head = fr.as_ptr() as u64;
            for _ in 0..n {
                let item = match etf_decode(ctx, d, safe) {
                    Ok(v) => v,
                    Err(()) => {
                        ctx.roots_head = saved;
                        return Err(());
                    }
                };
                fr.push(item);
                fr[1] += 1;
            }
            let tail = match etf_decode(ctx, d, safe) {
                Ok(v) => v,
                Err(()) => {
                    ctx.roots_head = saved;
                    return Err(());
                }
            };
            fr.push(tail);
            fr[1] += 1;
            let mut list = fr[2 + n];
            for i in (0..n).rev() {
                let cell = alloc_nursery(ctx, 2);
                unsafe {
                    *cell = fr[2 + i];
                    *cell.add(1) = list;
                }
                list = cell as u64 | TAG_CONS;
                fr[2 + n] = list; // keep the partial list rooted
            }
            ctx.roots_head = saved;
            Ok(list)
        }
        104 | 105 => {
            let n = if tag == 104 { d.u8()? as usize } else { d.u32()? as usize };
            let saved = ctx.roots_head;
            let mut fr: Vec<u64> = Vec::with_capacity(2 + n);
            fr.push(saved);
            fr.push(0);
            ctx.roots_head = fr.as_ptr() as u64;
            for _ in 0..n {
                let item = match etf_decode(ctx, d, safe) {
                    Ok(v) => v,
                    Err(()) => {
                        ctx.roots_head = saved;
                        return Err(());
                    }
                };
                fr.push(item);
                fr[1] += 1;
            }
            let t = alloc_nursery(ctx, 1 + n);
            unsafe {
                *t = ((n as u64) << 8) | KIND_TUPLE;
                for i in 0..n {
                    *t.add(1 + i) = fr[2 + i];
                }
            }
            ctx.roots_head = saved;
            Ok(t as u64)
        }
        116 => {
            let n = d.u32()? as usize;
            let saved = ctx.roots_head;
            let mut fr: Vec<u64> = Vec::with_capacity(2 + 2 * n);
            fr.push(saved);
            fr.push(0);
            ctx.roots_head = fr.as_ptr() as u64;
            for _ in 0..(2 * n) {
                let item = match etf_decode(ctx, d, safe) {
                    Ok(v) => v,
                    Err(()) => {
                        ctx.roots_head = saved;
                        return Err(());
                    }
                };
                fr.push(item);
                fr[1] += 1;
            }
            let m = alloc_nursery(ctx, 1 + 2 * n);
            unsafe {
                *m = ((n as u64) << 8) | KIND_MAP;
                for i in 0..n {
                    *m.add(1 + i) = fr[2 + 2 * i];
                    *m.add(1 + n + i) = fr[2 + 2 * i + 1];
                }
            }
            ctx.roots_head = saved;
            Ok(mana_rt_map_norm(m as u64))
        }
        70 => {
            let bits = u64::from_be_bytes(d.take(8)?.try_into().unwrap());
            let f = f64::from_bits(bits);
            let ctxp = ctx as *mut ProcCtx;
            Ok(box_float(unsafe { &mut *ctxp }, f))
        }
        109 => {
            let n = d.u32()? as usize;
            let bytes = d.take(n)?.to_vec();
            Ok(bytes_to_new_bin(ctx, &bytes))
        }
        _ => Err(()),
    }
}

fn atom_exists(name: &[u8]) -> bool {
    atom_table_lock().read().unwrap().contains_key(name)
}

#[no_mangle]
pub extern "C" fn mana_rt_term_to_binary(ctx: *mut ProcCtx, t: u64, _opts: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut out = vec![131u8];
    if etf_encode(t, &mut out).is_err() {
        return raise_badarg(ctx);
    }
    bytes_to_new_bin(ctx, &out)
}

#[no_mangle]
pub extern "C" fn mana_rt_binary_to_term(ctx: *mut ProcCtx, bin: u64, opts: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((bp, blen)) = bin_parts(bin) else {
        return raise_badarg(ctx);
    };
    let bytes: Vec<u8> = unsafe { std::slice::from_raw_parts(bp, blen) }.to_vec();
    let mut safe = false;
    let mut used = false;
    let mut cur = opts;
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        let o = unsafe { *p };
        if o & TAG_MASK == TAG_ATOM {
            match atom_bytes(o) {
                b"safe" => safe = true,
                b"used" => used = true,
                _ => {}
            }
        }
        cur = unsafe { *p.add(1) };
    }
    if bytes.first() != Some(&131) {
        return raise_badarg(ctx);
    }
    let mut d = EtfDec { buf: &bytes, pos: 1 };
    let r = etf_decode(ctx, &mut d, safe);
    let Ok(term) = r else {
        return raise_badarg(ctx);
    };
    if used {
        let saved = ctx.roots_head;
        let mut fr = [0u64, 1, term];
        fr[0] = saved;
        ctx.roots_head = fr.as_ptr() as u64;
        let t = alloc_nursery(ctx, 3);
        unsafe {
            *t = (2 << 8) | KIND_TUPLE;
            *t.add(1) = fr[2];
            *t.add(2) = ((d.pos as i64) << 3) as u64 | TAG_SMALL;
        }
        ctx.roots_head = saved;
        return t as u64;
    }
    term
}

// ---------------------------------------------------------------------------
// crypto (native cut: crypto.erl's NIF stubs are never compiled) — the
// subset Plug.Crypto/Phoenix sessions need.

pub const C_RAND: u64 = 0;
pub const C_HASH: u64 = 1;
pub const C_MAC: u64 = 2;
pub const C_EXOR: u64 = 3;
pub const C_PBKDF2: u64 = 4;
const C_HASH_EQUALS: u64 = 5;

fn crypto_bin_arg(t: u64) -> Result<Vec<u8>, ()> {
    let mut out = Vec::new();
    iolist_flatten(t, &mut out).map(|_| out)
}

fn crypto_hash(alg: &[u8], data: &[u8]) -> Option<Vec<u8>> {
    use sha1::Digest;
    match alg {
        b"sha" => Some(sha1::Sha1::digest(data).to_vec()),
        b"sha224" => Some(sha2::Sha224::digest(data).to_vec()),
        b"sha256" => Some(sha2::Sha256::digest(data).to_vec()),
        b"sha384" => Some(sha2::Sha384::digest(data).to_vec()),
        b"sha512" => Some(sha2::Sha512::digest(data).to_vec()),
        _ => None,
    }
}

fn crypto_hmac(alg: &[u8], key: &[u8], data: &[u8]) -> Option<Vec<u8>> {
    use hmac::{Hmac, Mac};
    macro_rules! mac {
        ($t:ty) => {{
            let mut m = <Hmac<$t> as Mac>::new_from_slice(key).ok()?;
            m.update(data);
            Some(m.finalize().into_bytes().to_vec())
        }};
    }
    match alg {
        b"sha" => mac!(sha1::Sha1),
        b"sha224" => mac!(sha2::Sha224),
        b"sha256" => mac!(sha2::Sha256),
        b"sha384" => mac!(sha2::Sha384),
        b"sha512" => mac!(sha2::Sha512),
        _ => None,
    }
}

/// RFC 2898 PBKDF2 over our HMAC.
fn crypto_pbkdf2(
    alg: &[u8],
    pass: &[u8],
    salt: &[u8],
    iters: u64,
    keylen: usize,
) -> Option<Vec<u8>> {
    let hlen = crypto_hmac(alg, pass, b"")?.len();
    let blocks = keylen.div_ceil(hlen);
    let mut out = Vec::with_capacity(blocks * hlen);
    for i in 1..=blocks as u32 {
        let mut block_in = salt.to_vec();
        block_in.extend_from_slice(&i.to_be_bytes());
        let mut u = crypto_hmac(alg, pass, &block_in)?;
        let mut t = u.clone();
        for _ in 1..iters {
            u = crypto_hmac(alg, pass, &u)?;
            for (ti, ui) in t.iter_mut().zip(u.iter()) {
                *ti ^= ui;
            }
        }
        out.extend_from_slice(&t);
    }
    out.truncate(keylen);
    Some(out)
}

#[no_mangle]
pub extern "C" fn mana_rt_crypto(
    ctx: *mut ProcCtx,
    op: u64,
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    match op {
        C_HASH_EQUALS => {
            // constant-time equality on equal-size binaries; badarg on
            // size mismatch or non-binaries, like OTP
            let (Some((ap, an)), Some((bp, bn))) = (bin_parts(a), bin_parts(b)) else {
                return raise_badarg(ctx);
            };
            if an != bn {
                return raise_badarg(ctx);
            }
            let (asl, bsl) = unsafe {
                (
                    std::slice::from_raw_parts(ap, an),
                    std::slice::from_raw_parts(bp, bn),
                )
            };
            let mut acc = 0u8;
            for i in 0..an {
                acc |= asl[i] ^ bsl[i];
            }
            if acc == 0 {
                known().true_a
            } else {
                known().false_a
            }
        }
        C_RAND => {
            if a & TAG_MASK != TAG_SMALL || (a as i64 >> 3) < 0 {
                return raise_badarg(ctx);
            }
            let n = (a as i64 >> 3) as usize;
            let mut buf = vec![0u8; n];
            if getrandom::getrandom(&mut buf).is_err() {
                return raise_badarg(ctx);
            }
            bytes_to_new_bin(ctx, &buf)
        }
        C_HASH => {
            if a & TAG_MASK != TAG_ATOM {
                return raise_badarg(ctx);
            }
            let Ok(data) = crypto_bin_arg(b) else { return raise_badarg(ctx) };
            match crypto_hash(atom_bytes(a), &data) {
                Some(h) => bytes_to_new_bin(ctx, &h),
                None => raise_badarg(ctx),
            }
        }
        C_MAC => {
            // mac(hmac, Alg, Key, Data)
            if a & TAG_MASK != TAG_ATOM
                || atom_bytes(a) != b"hmac"
                || b & TAG_MASK != TAG_ATOM
            {
                return raise_badarg(ctx);
            }
            let (Ok(key), Ok(data)) = (crypto_bin_arg(c), crypto_bin_arg(d)) else {
                return raise_badarg(ctx);
            };
            match crypto_hmac(atom_bytes(b), &key, &data) {
                Some(h) => bytes_to_new_bin(ctx, &h),
                None => raise_badarg(ctx),
            }
        }
        C_EXOR => {
            let (Ok(x), Ok(y)) = (crypto_bin_arg(a), crypto_bin_arg(b)) else {
                return raise_badarg(ctx);
            };
            if x.len() != y.len() {
                return raise_badarg(ctx);
            }
            let out: Vec<u8> = x.iter().zip(y.iter()).map(|(p, q)| p ^ q).collect();
            bytes_to_new_bin(ctx, &out)
        }
        C_PBKDF2 => {
            // pbkdf2_hmac(Alg, Pass, Salt, Iterations, KeyLen)
            if a & TAG_MASK != TAG_ATOM
                || d & TAG_MASK != TAG_SMALL
                || e & TAG_MASK != TAG_SMALL
            {
                return raise_badarg(ctx);
            }
            let (Ok(pass), Ok(salt)) = (crypto_bin_arg(b), crypto_bin_arg(c)) else {
                return raise_badarg(ctx);
            };
            let iters = (d as i64 >> 3).max(1) as u64;
            let keylen = (e as i64 >> 3).max(0) as usize;
            match crypto_pbkdf2(atom_bytes(a), &pass, &salt, iters, keylen) {
                Some(k) => bytes_to_new_bin(ctx, &k),
                None => raise_badarg(ctx),
            }
        }
        _ => raise_badarg(ctx),
    }
}

/// erlang:iolist_size/1.
#[no_mangle]
pub extern "C" fn mana_rt_iolist_size(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut out = Vec::new();
    if iolist_flatten(t, &mut out).is_err() {
        return raise_badarg(ctx);
    }
    ((out.len() as i64) << 3) as u64 | TAG_SMALL
}

/// erlang:phash2/1,2 — structural term hash. Values are STABLE for this
/// runtime but do NOT match BEAM's phash2 (documented divergence; callers
/// use it for sharding/ids, not persisted values).
fn phash2_term(t: u64, h: &mut u64) {
    fn mix(h: &mut u64, v: u64) {
        *h = (*h ^ v).wrapping_mul(0x100000001b3); // FNV-ish
    }
    match t & TAG_MASK {
        TAG_SMALL => mix(h, t),
        TAG_ATOM => {
            mix(h, 2);
            for &b in atom_bytes(t) {
                mix(h, b as u64);
            }
        }
        _ if t == NIL => mix(h, 3),
        TAG_CONS => {
            let mut cur = t;
            while cur & TAG_MASK == TAG_CONS {
                let p = (cur & !TAG_MASK) as *const u64;
                phash2_term(unsafe { *p }, h);
                cur = unsafe { *p.add(1) };
            }
            mix(h, 4);
            if cur != NIL {
                phash2_term(cur, h);
            }
        }
        TAG_BOXED if t != 0 => unsafe {
            let p = t as *const u64;
            let kind = *p & 0xff;
            // views hash as binaries: equal bytes must hash equal
            mix(h, 5 + if kind == KIND_SUBBIN { KIND_BIN } else { kind });
            match kind {
                KIND_TUPLE | KIND_MAP => {
                    let words = payload_words(*p);
                    for i in 1..=words {
                        phash2_term(*p.add(i), h);
                    }
                }
                KIND_FLOAT => mix(h, *p.add(1)),
                KIND_BIN | KIND_SUBBIN => {
                    for &b in bin_bytes(t) {
                        mix(h, b as u64);
                    }
                }
                KIND_BIGNUM => {
                    let (neg, mag) = bignum_parts(t).unwrap();
                    mix(h, neg as u64);
                    for &l in mag {
                        mix(h, l);
                    }
                }
                _ => mix(h, *p),
            }
        },
        _ => mix(h, t), // pids etc: identity word
    }
}

#[no_mangle]
pub extern "C" fn mana_rt_phash2(ctx: *mut ProcCtx, t: u64, range: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let modulus = if range == 0 {
        1u64 << 27 // phash2/1 default range
    } else {
        if range & TAG_MASK != TAG_SMALL || (range as i64 >> 3) <= 0 {
            return raise_badarg(ctx);
        }
        (range as i64 >> 3) as u64
    };
    let mut h: u64 = 0xcbf29ce484222325;
    phash2_term(t, &mut h);
    (((h % modulus) as i64) << 3) as u64 | TAG_SMALL
}

/// erlang:unique_integer/0,1 — a global counter (uniqueness only; the
/// positive/monotonic option atoms are all satisfied by counting up).
static UNIQUE_INTEGER: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(1);

#[no_mangle]
pub extern "C" fn mana_rt_unique_integer(_ctx: *mut ProcCtx) -> u64 {
    let v = UNIQUE_INTEGER.fetch_add(1, Ordering::Relaxed);
    ((v << 3) as u64) | TAG_SMALL
}

/// erlang:is_record/3 — tuple whose first element is Tag with Size arity.
#[no_mangle]
pub extern "C" fn mana_rt_is_record(t: u64, tag: u64, size: u64) -> u64 {
    if size & TAG_MASK != TAG_SMALL || t & TAG_MASK != TAG_BOXED || t == 0 {
        return known().false_a;
    }
    let want = (size as i64 >> 3) as usize;
    unsafe {
        let p = t as *const u64;
        if *p & 0xff != KIND_TUPLE || (*p >> 8) as usize != want || want == 0 {
            return known().false_a;
        }
        if *p.add(1) == tag {
            known().true_a
        } else {
            known().false_a
        }
    }
}

/// erlang:process_flag/2 — trap_exit is real; the scheduler-tuning flags
/// are accepted no-ops with plausible old values; unknown flags badarg.
#[no_mangle]
pub extern "C" fn mana_rt_process_flag(ctx: *mut ProcCtx, flag: u64, value: u64) -> u64 {
    let ctxp = ctx;
    let ctx = unsafe { &mut *ctx };
    if flag & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    match atom_bytes(flag) {
        b"trap_exit" => mana_rt_trap_exit(ctxp, value),
        b"priority" => atom_intern(b"normal"),
        b"message_queue_data" => atom_intern(b"off_heap"),
        b"min_heap_size" | b"min_bin_vheap_size" | b"max_heap_size"
        | b"fullsweep_after" => (0 << 3) | TAG_SMALL,
        b"sensitive" | b"error_handler" => known().false_a,
        _ => raise_badarg(ctx),
    }
}

/// erlang:system_flag/2 — accepted no-ops returning plausible old values
/// (VM tuning knobs that have no meaning here; Phoenix sets
/// backtrace_depth at application start).
#[no_mangle]
pub extern "C" fn mana_rt_system_flag(ctx: *mut ProcCtx, flag: u64, _value: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if flag & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    match atom_bytes(flag) {
        b"backtrace_depth" | b"fullsweep_after" | b"min_heap_size"
        | b"min_bin_vheap_size" | b"max_heap_size" => (8 << 3) | TAG_SMALL,
        _ => raise_badarg(ctx),
    }
}

/// persistent_term:info/0 — #{count => N, memory => bytes-ish}.
#[no_mangle]
pub extern "C" fn mana_rt_pt_info(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let count = PERSISTENT_TERMS
        .lock()
        .unwrap()
        .as_ref()
        .map(|m| m.len() as u64)
        .unwrap_or(0);
    let t = alloc_nursery(ctx, 5);
    unsafe {
        *t = (2 << 8) | KIND_MAP;
        // sorted flatmap: atom order is by name — count < memory
        *t.add(1) = atom_intern(b"count");
        *t.add(2) = (count << 3) | TAG_SMALL;
        *t.add(3) = atom_intern(b"memory");
        *t.add(4) = ((count * 64) << 3) | TAG_SMALL;
    }
    t as u64
}

/// erlang:memory/0 — allocator stats mapped onto BEAM's key set. Values
/// come from OUR heaps (old space + nurseries), so absolute numbers
/// diverge from BEAM (documented; consumers chart trends, not identities).
#[no_mangle]
pub extern "C" fn mana_rt_memory(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let g = ctx.global;
    let old_bytes = g.old_used.load(Ordering::Relaxed) as u64 * 8;
    let nursery_bytes = g.n_scheds as u64 * ctx.nursery_words as u64 * 8;
    let processes = old_bytes + nursery_bytes;
    let atom = interned_atom_count() * 64;
    let system = atom + 1_048_576;
    let total = processes + system;
    let pairs: [(&[u8], u64); 9] = [
        (b"total", total),
        (b"processes", processes),
        (b"processes_used", processes),
        (b"system", system),
        (b"atom", atom),
        (b"atom_used", atom),
        (b"binary", 0),
        (b"code", 0),
        (b"ets", 0),
    ];
    // build [{k, v} | ...] back-to-front; BOTH the list and the fresh
    // tuple are frame-rooted across the cons allocation (a Rust local is
    // not a GC root — the cons alloc can move the tuple)
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for (k, v) in pairs.iter().rev() {
        let t = alloc_nursery(ctx, 3);
        unsafe {
            *t = (2 << 8) | KIND_TUPLE;
            *t.add(1) = atom_intern(k);
            *t.add(2) = (v << 3) | TAG_SMALL;
        }
        fr[3] = t as u64;
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = fr[3];
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
        fr[3] = NIL;
    }
    ctx.roots_head = saved;
    fr[2]
}

/// erlang:statistics/1 — the telemetry_poller keys only.
#[no_mangle]
pub extern "C" fn mana_rt_statistics(ctx: *mut ProcCtx, item: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if item & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    match atom_bytes(item) {
        // run queues are drained at safepoints; a snapshot of 0 is honest
        // enough for poller charts
        b"total_run_queue_lengths" | b"total_run_queue_lengths_all" | b"run_queue" => TAG_SMALL,
        _ => raise_badarg(ctx),
    }
}

/// spawn_link/1 — link is established before the child first runs.
#[no_mangle]
pub extern "C" fn mana_rt_spawn_link(ctx: *mut ProcCtx, closure: u64) -> u64 {
    let pid = mana_rt_spawn(ctx, closure);
    if pid == 0 {
        return 0;
    }
    mana_rt_link(ctx, pid);
    pid
}

/// spawn_monitor/1 — returns the {Pid, Ref} tuple.
#[no_mangle]
pub extern "C" fn mana_rt_spawn_monitor(ctx: *mut ProcCtx, closure: u64) -> u64 {
    let pid = mana_rt_spawn(ctx, closure);
    if pid == 0 {
        return 0;
    }
    let ctxr = unsafe { &mut *ctx };
    let r = mana_rt_monitor(ctx, pid);
    shared_tuple(ctxr, &[pid, r])
}

/// Shared spawn machinery for MFA-shaped spawns: builds the {M, F, Args}
/// pending tuple in the shared old space and registers the process.
fn spawn_mfa_inner(ctx: &mut ProcCtx, m: u64, f: u64, args: u64) -> u64 {
    let global = ctx.global;
    // deep-promote the args first: shared_tuple requires old/eternal/immediate
    // items, and a young args list referenced from the old-space pending tuple
    // would be missed by minors (no remembered set) and dangle.
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, m, f, args];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    fr[2] = promote_term(ctx, fr[2]);
    fr[3] = promote_term(ctx, fr[3]);
    fr[4] = promote_term(ctx, fr[4]);
    let pending = shared_tuple(ctx, &[fr[2], fr[3], fr[4]]);
    ctx.roots_head = saved;
    let home = if global.n_scheds == 1 {
        0
    } else {
        global.spawn_rr.fetch_add(1, Ordering::Relaxed) % global.n_scheds
    };
    let pid = register_process(
        global,
        Process {
            home,
            coro: Some(make_coroutine(global, home)),
            yielder: std::ptr::null(),
            saved_roots: 0,
            saved_exc_class: 0,
            saved_exc_reason: 0,
            ingress: SegQueue::new(),
            private: Vec::new(),
            cursor: 0,
            state: Mutex::new(PState::Runnable),
            pending_closure: pending,
            lstate: Mutex::new(LinkState::default()),
            pdict: Mutex::new(Vec::new()),
            dirty: std::sync::atomic::AtomicBool::new(true),
        },
    );
    if home == ctx.sched_id {
        ctx.run_q.push_back(pid);
    } else {
        global.scheds[home].inject.push(pid);
        wake_sched(global, home);
    }
    make_pid(pid)
}

/// erlang:spawn_opt/4 (and spawn/3, spawn_link/3 with fixed opts).
/// Understood options: link, monitor, {monitor, _}; sizing/priority hints
/// are ignored. Returns pid, or {Pid, Ref} when monitoring.
#[no_mangle]
pub extern "C" fn mana_rt_spawn_opt_mfa(
    ctx: *mut ProcCtx,
    m: u64,
    f: u64,
    args: u64,
    opts: u64,
) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    if m & TAG_MASK != TAG_ATOM || f & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctxr);
    }
    let (mut link, mut monitor) = (false, false);
    let mut cur = opts;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctxr);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let opt = unsafe { *p };
        if opt & TAG_MASK == TAG_ATOM {
            match atom_bytes(opt) {
                b"link" => link = true,
                b"monitor" => monitor = true,
                _ => {} // priority etc. — hints we ignore
            }
        } else if opt & TAG_MASK == TAG_BOXED && opt != 0 {
            let hp = opt as *const u64;
            let h = unsafe { *hp };
            if h & 0xff == KIND_TUPLE && h >> 8 == 2 {
                let tag = unsafe { *hp.add(1) };
                if tag & TAG_MASK == TAG_ATOM && atom_bytes(tag) == b"monitor" {
                    monitor = true;
                }
            }
        }
        cur = unsafe { *p.add(1) };
    }
    let pid = spawn_mfa_inner(ctxr, m, f, args);
    if link {
        mana_rt_link(ctx, pid);
    }
    if monitor {
        let r = mana_rt_monitor(ctx, pid);
        return shared_tuple(unsafe { &mut *ctx }, &[pid, r]);
    }
    pid
}

// ---------------------------------------------------------------------------
// bignums (KIND_BIGNUM) — limb math lives in mod bigint

/// (negative, limbs) of a bignum term.
fn bignum_parts(t: u64) -> Option<(bool, &'static [u64])> {
    if t & TAG_MASK != TAG_BOXED || t == 0 {
        return None;
    }
    let p = t as *const u64;
    let h = unsafe { *p };
    if h & 0xff != KIND_BIGNUM {
        return None;
    }
    Some((
        h & 0x100 != 0,
        unsafe { std::slice::from_raw_parts(p.add(1), (h >> 9) as usize) },
    ))
}

/// Is this term an integer (small or bignum)?
fn is_int_term(t: u64) -> bool {
    t & TAG_MASK == TAG_SMALL || bignum_parts(t).is_some()
}

/// (negative, magnitude) of any integer term.
fn int_mag(t: u64) -> Option<(bool, Vec<u64>)> {
    if t & TAG_MASK == TAG_SMALL {
        let v = t as i64 >> 3;
        return Some(if v < 0 {
            (true, bigint::normalize(vec![v.unsigned_abs()]))
        } else {
            (false, bigint::normalize(vec![v as u64]))
        });
    }
    bignum_parts(t).map(|(neg, l)| (neg, l.to_vec()))
}

/// THE integer constructor: small when it fits (the small range is
/// -2^60 ..= 2^60-1), shared-old-space bignum otherwise. Never a GC point.
fn make_int_mag(ctx: &mut ProcCtx, negative: bool, mag: &[u64]) -> u64 {
    if mag.is_empty() {
        return TAG_SMALL; // zero
    }
    if mag.len() == 1 {
        let v = mag[0];
        if (!negative && v <= (1u64 << 60) - 1) || (negative && v <= 1u64 << 60) {
            let sv = if negative { -(v as i64) } else { v as i64 };
            return ((sv << 3) as u64) | TAG_SMALL;
        }
    }
    let p = alloc_shared(ctx, 1 + mag.len());
    unsafe {
        *p = ((mag.len() as u64) << 9) | ((negative as u64) << 8) | KIND_BIGNUM;
        for (i, &l) in mag.iter().enumerate() {
            *p.add(1 + i) = l;
        }
    }
    p as u64
}

/// Eternal bignum (literals, no ctx available).
fn make_int_mag_eternal(negative: bool, mag: &[u64]) -> u64 {
    debug_assert!(!mag.is_empty());
    let p = alloc_space(1 + mag.len());
    unsafe {
        *p = ((mag.len() as u64) << 9) | ((negative as u64) << 8) | KIND_BIGNUM;
        for (i, &l) in mag.iter().enumerate() {
            *p.add(1 + i) = l;
        }
    }
    p as u64
}

/// Interned eternal big-literal terms, keyed by their decimal text.
#[no_mangle]
pub extern "C" fn mana_rt_big_literal(ptr: *const u8, len: u64) -> u64 {
    static TABLE: std::sync::Mutex<
        Option<std::collections::HashMap<&'static [u8], u64>>,
    > = std::sync::Mutex::new(None);
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len as usize) };
    let mut guard = TABLE.lock().unwrap();
    let map = guard.get_or_insert_with(Default::default);
    if let Some(&t) = map.get(bytes) {
        return t;
    }
    let (neg, digits) = match bytes.strip_prefix(b"-") {
        Some(rest) => (true, rest),
        None => (false, bytes),
    };
    let mag = bigint::mag_from_decimal(digits).expect("invalid big literal");
    let t = make_int_mag_eternal(neg, &mag);
    let key: &'static [u8] = Box::leak(bytes.to_vec().into_boxed_slice());
    map.insert(key, t);
    t
}

/// Exact comparison of two INTEGER terms (small or bignum).
fn int_cmp_exact(a: u64, b: u64) -> i64 {
    if a & TAG_MASK == TAG_SMALL && b & TAG_MASK == TAG_SMALL {
        let (x, y) = (a as i64 >> 3, b as i64 >> 3);
        return (x > y) as i64 - (x < y) as i64;
    }
    let (na, ma) = int_mag(a).expect("int_cmp_exact: not an integer");
    let (nb, mb) = int_mag(b).expect("int_cmp_exact: not an integer");
    // normalized zero has an empty magnitude and negative=false
    if na != nb {
        return if na { -1 } else { 1 };
    }
    let r = match bigint::mag_cmp(&ma, &mb) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    };
    if na { -r } else { r }
}

// ---------------------------------------------------------------------------
// :re — regular expressions on the `regex` crate. `:re.version/0` returns
// "mana" so Elixir's Regex always recompiles from source at runtime
// (sigil literals carry opaque BEAM-compiled PCRE blobs we can't read).
// Known divergences: no backreferences/lookaround (crate limitation),
// firstline/ungreedy options ignored.

struct ReTable {
    by_key: std::collections::HashMap<String, usize>,
    regexes: Vec<regex::Regex>,
}

static RE_TABLE: std::sync::Mutex<Option<ReTable>> = std::sync::Mutex::new(None);

#[derive(Default, Clone, Copy)]
struct ReFlags {
    caseless: bool,
    multiline: bool,
    dotall: bool,
    extended: bool,
}

struct ReRunOpts {
    global: bool,
    offset: usize,
    capture_spec: u64,   // term: atom all/first/none/all_but_first/all_names or list
    capture_type: u8,    // 0 index, 1 binary, 2 list
}

fn term_to_source(t: u64) -> Option<Vec<u8>> {
    if bin_parts(t).is_some() {
        return Some(bin_bytes(t).to_vec());
    }
    // charlist
    let mut out = Vec::new();
    let mut cur = t;
    loop {
        if cur == NIL {
            return Some(out);
        }
        if cur & TAG_MASK != TAG_CONS {
            return None;
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK != TAG_SMALL {
            return None;
        }
        let cp = h as i64 >> 3;
        let c = u32::try_from(cp).ok().and_then(char::from_u32)?;
        let mut buf = [0u8; 4];
        out.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
        cur = unsafe { *p.add(1) };
    }
}

/// Intern (or fetch) a compiled regex; Err(msg) on bad pattern.
fn re_intern(source: &str, fl: ReFlags) -> Result<usize, String> {
    let key = format!(
        "{}{}{}{}\0{}",
        fl.caseless as u8, fl.multiline as u8, fl.dotall as u8, fl.extended as u8, source
    );
    let mut guard = RE_TABLE.lock().unwrap();
    let tab = guard.get_or_insert_with(|| ReTable {
        by_key: Default::default(),
        regexes: Vec::new(),
    });
    if let Some(&i) = tab.by_key.get(&key) {
        return Ok(i);
    }
    let re = regex::RegexBuilder::new(source)
        .case_insensitive(fl.caseless)
        .multi_line(fl.multiline)
        .dot_matches_new_line(fl.dotall)
        .ignore_whitespace(fl.extended)
        .build()
        .map_err(|e| e.to_string())?;
    tab.regexes.push(re);
    let idx = tab.regexes.len() - 1;
    tab.by_key.insert(key, idx);
    Ok(idx)
}

/// Options list → (compile flags, run opts). Unknown atoms are ignored
/// (BEAM accepts many run options that don't apply here).
fn parse_re_opts(opts: u64) -> Result<(ReFlags, ReRunOpts), ()> {
    let mut fl = ReFlags::default();
    let mut run = ReRunOpts {
        global: false,
        offset: 0,
        capture_spec: 0,
        capture_type: 0,
    };
    let mut cur = opts;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return Err(());
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let opt = unsafe { *p };
        if opt & TAG_MASK == TAG_ATOM {
            match atom_bytes(opt) {
                b"caseless" => fl.caseless = true,
                b"multiline" => fl.multiline = true,
                b"dotall" => fl.dotall = true,
                b"extended" => fl.extended = true,
                b"global" => run.global = true,
                // unicode/ucp are the crate default; the rest are accepted
                // and ignored (firstline, ungreedy, anchored variations...)
                _ => {}
            }
        } else if opt & TAG_MASK == TAG_BOXED && opt != 0 {
            let hp = opt as *const u64;
            let h = unsafe { *hp };
            if h & 0xff == KIND_TUPLE {
                let arity = h >> 8;
                let tag = unsafe { *hp.add(1) };
                match (atom_bytes(tag), arity) {
                    (b"capture", 2) => {
                        run.capture_spec = unsafe { *hp.add(2) };
                        run.capture_type = 0;
                    }
                    (b"capture", 3) => {
                        run.capture_spec = unsafe { *hp.add(2) };
                        let ty = unsafe { *hp.add(3) };
                        run.capture_type = match atom_bytes(ty) {
                            b"binary" => 1,
                            b"list" => 2,
                            _ => 0,
                        };
                    }
                    (b"offset", 2) => {
                        let off = unsafe { *hp.add(2) };
                        if off & TAG_MASK != TAG_SMALL {
                            return Err(());
                        }
                        run.offset = (off as i64 >> 3).max(0) as usize;
                    }
                    (b"newline", _) => {}
                    _ => {}
                }
            }
        }
        cur = unsafe { *p.add(1) };
    }
    Ok((fl, run))
}

/// The subject pattern argument of run/compile: an interned handle
/// {mana_re, Idx} or a source binary/charlist compiled with `fl`.
fn re_resolve(pat: u64, fl: ReFlags) -> Result<usize, String> {
    if pat & TAG_MASK == TAG_BOXED && pat != 0 {
        let hp = pat as *const u64;
        let h = unsafe { *hp };
        if h & 0xff == KIND_TUPLE && h >> 8 == 2 {
            let tag = unsafe { *hp.add(1) };
            if tag & TAG_MASK == TAG_ATOM && atom_bytes(tag) == b"mana_re" {
                let idx = unsafe { *hp.add(2) };
                return Ok((idx as i64 >> 3) as usize);
            }
        }
    }
    let src = term_to_source(pat).ok_or_else(|| "bad pattern".to_string())?;
    let s = String::from_utf8(src).map_err(|e| e.to_string())?;
    re_intern(&s, fl)
}

/// One capture group as a term per capture_type. Unmatched: {-1,0} / <<>> / [].
fn cap_term(ctx: &mut ProcCtx, hay: &[u8], g: Option<(usize, usize)>, ty: u8) -> u64 {
    match ty {
        0 => {
            let (s, l) = match g {
                Some((a, b)) => (a as i64, (b - a) as i64),
                None => (-1, 0),
            };
            let t = alloc_nursery(ctx, 3);
            unsafe {
                *t = (2 << 8) | KIND_TUPLE;
                *t.add(1) = ((s << 3) as u64) | TAG_SMALL;
                *t.add(2) = ((l << 3) as u64) | TAG_SMALL;
            }
            t as u64
        }
        1 => match g {
            Some((a, b)) => bytes_to_new_bin(ctx, &hay[a..b]),
            None => bytes_to_new_bin(ctx, b""),
        },
        _ => match g {
            Some((a, b)) => bytes_to_charlist(ctx, &hay[a..b]),
            None => NIL,
        },
    }
}

/// :re.run/3. Returns {match, Caps} | {match, [Caps]} (global) | match |
/// nomatch, or raises badarg on bad patterns/options.
#[no_mangle]
pub extern "C" fn mana_rt_re_run(ctx: *mut ProcCtx, subject: u64, pat: u64, opts: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some(hay) = term_to_source(subject) else {
        return raise_badarg(ctx);
    };
    let Ok((fl, run)) = parse_re_opts(opts) else {
        return raise_badarg(ctx);
    };
    let idx = match re_resolve(pat, fl) {
        Ok(i) => i,
        Err(_) => return raise_badarg(ctx),
    };
    let re = {
        let guard = RE_TABLE.lock().unwrap();
        guard.as_ref().unwrap().regexes[idx].clone()
    };
    let hay_str = match std::str::from_utf8(&hay) {
        Ok(s) => s,
        Err(_) => return raise_badarg(ctx),
    };
    let none_a = || find_atom("none").unwrap_or(NIL);
    let _ = none_a;
    // collect matches
    let mut all: Vec<Vec<Option<(usize, usize)>>> = Vec::new();
    let mut pos = run.offset.min(hay_str.len());
    loop {
        let Some(caps) = re.captures_at(hay_str, pos) else {
            break;
        };
        let whole = caps.get(0).unwrap();
        let groups: Vec<Option<(usize, usize)>> = (0..caps.len())
            .map(|i| caps.get(i).map(|m| (m.start(), m.end())))
            .collect();
        all.push(groups);
        if !run.global {
            break;
        }
        pos = if whole.end() > whole.start() {
            whole.end()
        } else {
            // empty match: advance one char
            match hay_str[whole.end()..].chars().next() {
                Some(c) => whole.end() + c.len_utf8(),
                None => break,
            }
        };
    }
    if all.is_empty() {
        return find_atom("nomatch").expect("nomatch atom");
    }
    // capture :none → bare 'match'
    if run.capture_spec & TAG_MASK == TAG_ATOM && atom_bytes(run.capture_spec) == b"none" {
        return find_atom("match").expect("match atom");
    }
    // select groups per spec
    let names: Vec<Option<String>> = re
        .capture_names()
        .map(|n| n.map(|s| s.to_string()))
        .collect();
    let select = |groups: &Vec<Option<(usize, usize)>>| -> Vec<Option<(usize, usize)>> {
        let spec = run.capture_spec;
        if spec & TAG_MASK == TAG_ATOM {
            match atom_bytes(spec) {
                b"first" => vec![groups[0]],
                b"all_but_first" => groups[1..].to_vec(),
                b"all_names" => {
                    let mut named: Vec<(String, Option<(usize, usize)>)> = names
                        .iter()
                        .enumerate()
                        .filter_map(|(i, n)| n.clone().map(|n| (n, groups.get(i).copied().flatten())))
                        .collect();
                    named.sort_by(|a, b| a.0.cmp(&b.0));
                    named.into_iter().map(|(_, g)| g).collect()
                }
                _ => groups.clone(), // all (and default)
            }
        } else if spec == 0 {
            groups.clone()
        } else {
            // list of names (binaries/atoms) or indices
            let mut out = Vec::new();
            let mut cur = spec;
            while cur != NIL && cur & TAG_MASK == TAG_CONS {
                let p = (cur & !TAG_MASK) as *const u64;
                let item = unsafe { *p };
                let g = if item & TAG_MASK == TAG_SMALL {
                    groups.get((item as i64 >> 3) as usize).copied().flatten()
                } else {
                    let want: Vec<u8> = if item & TAG_MASK == TAG_ATOM {
                        atom_bytes(item).to_vec()
                    } else {
                        bin_bytes(item).to_vec()
                    };
                    names
                        .iter()
                        .position(|n| n.as_deref().map(|s| s.as_bytes()) == Some(&want[..]))
                        .and_then(|i| groups.get(i).copied().flatten())
                };
                out.push(g);
                cur = unsafe { *p.add(1) };
            }
            out
        }
    };
    // build result list(s) back-to-front with rooting
    let build_caps = |ctx: &mut ProcCtx, groups: &Vec<Option<(usize, usize)>>| -> u64 {
        let sel = select(groups);
        let saved = ctx.roots_head;
        let mut fr = [0u64, 2, NIL, 0];
        fr[0] = saved;
        ctx.roots_head = fr.as_ptr() as u64;
        for g in sel.iter().rev() {
            fr[3] = cap_term(ctx, &hay, *g, run.capture_type);
            let cell = alloc_nursery(ctx, 2);
            unsafe {
                *cell = fr[3];
                *cell.add(1) = fr[2];
            }
            fr[2] = cell as u64 | TAG_CONS;
            fr[3] = 0;
        }
        ctx.roots_head = saved;
        fr[2]
    };
    let payload = if run.global {
        let lists: Vec<u64> = Vec::new();
        let _ = lists;
        let saved = ctx.roots_head;
        let mut fr = [0u64, 2, NIL, 0];
        fr[0] = saved;
        ctx.roots_head = fr.as_ptr() as u64;
        for groups in all.iter().rev() {
            fr[3] = build_caps(ctx, groups);
            let cell = alloc_nursery(ctx, 2);
            unsafe {
                *cell = fr[3];
                *cell.add(1) = fr[2];
            }
            fr[2] = cell as u64 | TAG_CONS;
            fr[3] = 0;
        }
        ctx.roots_head = saved;
        fr[2]
    } else {
        build_caps(ctx, &all[0])
    };
    // {match, Payload}
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, payload];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let t = alloc_nursery(ctx, 3);
    ctx.roots_head = saved;
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = find_atom("match").expect("match atom");
        *t.add(2) = fr[2];
    }
    t as u64
}

/// :re.compile/2 → {ok, {mana_re, Idx}} | {error, {Reason, 0}}.
#[no_mangle]
pub extern "C" fn mana_rt_re_compile(ctx: *mut ProcCtx, pat: u64, opts: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Ok((fl, _)) = parse_re_opts(opts) else {
        return raise_badarg(ctx);
    };
    let Some(srcb) = term_to_source(pat) else {
        return raise_badarg(ctx);
    };
    let Ok(srcs) = String::from_utf8(srcb) else {
        return raise_badarg(ctx);
    };
    match re_intern(&srcs, fl) {
        Ok(idx) => {
            // {ok, {mana_re, Idx}}
            let inner = alloc_nursery(ctx, 3);
            unsafe {
                *inner = (2 << 8) | KIND_TUPLE;
                *inner.add(1) = atom_intern(b"mana_re");
                *inner.add(2) = ((idx as u64) << 3) | TAG_SMALL;
            }
            let saved = ctx.roots_head;
            let mut fr = [0u64, 1, inner as u64];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            let t = alloc_nursery(ctx, 3);
            ctx.roots_head = saved;
            unsafe {
                *t = (2 << 8) | KIND_TUPLE;
                *t.add(1) = known().ok;
                *t.add(2) = fr[2];
            }
            t as u64
        }
        Err(msg) => {
            // {error, {ErrString(charlist), 0}}
            let saved = ctx.roots_head;
            let mut fr = [0u64, 2, 0, 0];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            fr[2] = bytes_to_charlist(ctx, msg.as_bytes());
            let inner = alloc_nursery(ctx, 3);
            unsafe {
                *inner = (2 << 8) | KIND_TUPLE;
                *inner.add(1) = fr[2];
                *inner.add(2) = TAG_SMALL; // 0
            }
            fr[3] = inner as u64;
            let t = alloc_nursery(ctx, 3);
            ctx.roots_head = saved;
            unsafe {
                *t = (2 << 8) | KIND_TUPLE;
                *t.add(1) = atom_error();
                *t.add(2) = fr[3];
            }
            t as u64
        }
    }
}

/// :re.inspect/2 (:namelist) → {namelist, [<<name>>]} sorted.
#[no_mangle]
pub extern "C" fn mana_rt_re_inspect(ctx: *mut ProcCtx, pat: u64, _what: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let idx = match re_resolve(pat, ReFlags::default()) {
        Ok(i) => i,
        Err(_) => return raise_badarg(ctx),
    };
    let names: Vec<String> = {
        let guard = RE_TABLE.lock().unwrap();
        guard.as_ref().unwrap().regexes[idx]
            .capture_names()
            .flatten()
            .map(|s| s.to_string())
            .collect()
    };
    let mut sorted = names;
    sorted.sort();
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, 0];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for n in sorted.iter().rev() {
        fr[3] = bytes_to_new_bin(ctx, n.as_bytes());
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = fr[3];
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
        fr[3] = 0;
    }
    let t = alloc_nursery(ctx, 3);
    ctx.roots_head = saved;
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = atom_intern(b"namelist");
        *t.add(2) = fr[2];
    }
    t as u64
}

// ---------------------------------------------------------------------------
// floats & arithmetic

fn raise_badarith(ctx: &mut ProcCtx) -> u64 {
    ctx.exc_class = atom_error();
    ctx.exc_reason = known().badarith;
    EXC_SENTINEL
}

/// Box an f64 WITHOUT ever triggering a collection: nursery bump if there
/// is room, otherwise the shared old space (non-moving; majors only run at
/// safepoints, which a BIF call is not). This keeps arithmetic out of the
/// may-GC effect set — integer loops stay frameless. Cost: floats born
/// while the nursery is full live until the next major.
fn box_float(ctx: &mut ProcCtx, f: f64) -> u64 {
    let p = unsafe {
        if ctx.heap_top.add(2) <= ctx.heap_end {
            let p = ctx.heap_top;
            ctx.heap_top = ctx.heap_top.add(2);
            p
        } else {
            let g = ctx.global;
            let mut old = g.old.lock();
            old.alloc(2, &g.old_used)
        }
    };
    unsafe {
        *p = (1 << 8) | KIND_FLOAT;
        *p.add(1) = f.to_bits();
    }
    p as u64
}

/// Float literal pattern test: is `t` a float with exactly these bits?
/// Non-allocating (safe inside match contexts).
#[no_mangle]
pub extern "C" fn mana_rt_float_pat(t: u64, bits: u64) -> u64 {
    if t & TAG_MASK != TAG_BOXED || t == 0 {
        return 0;
    }
    let p = t as *const u64;
    unsafe { (*p & 0xff == KIND_FLOAT && *p.add(1) == bits) as u64 }
}

/// Numeric coercion for arithmetic; None = not a number → badarith.
/// Bignums coerce to their (possibly rounded) f64 for float-mixed ops.
fn num_of(t: u64) -> Option<(f64, bool)> {
    if t & TAG_MASK == TAG_SMALL {
        return Some(((t as i64 >> 3) as f64, true));
    }
    if t & TAG_MASK == TAG_BOXED && t != 0 {
        let p = t as *const u64;
        if unsafe { *p } & 0xff == KIND_FLOAT {
            return Some((f64::from_bits(unsafe { *p.add(1) }), false));
        }
        if let Some((neg, mag)) = bignum_parts(t) {
            let v = bigint::mag_to_f64(mag);
            return Some((if neg { -v } else { v }, true));
        }
    }
    None
}

// arithmetic opcodes for mana_rt_arith
fn abort_bignum(what: &str) -> ! {
    eprintln!("mana: TODO(bignum): {}", what);
    std::process::exit(1);
}

pub const AR_ADD: u64 = 0;
pub const AR_SUB: u64 = 1;
pub const AR_MUL: u64 = 2;
pub const AR_FDIV: u64 = 3;
pub const AR_IDIV: u64 = 4;
pub const AR_REM: u64 = 5;
pub const AR_NEG: u64 = 6;
pub const AR_ABS: u64 = 7;
pub const AR_BAND: u64 = 8;
pub const AR_BOR: u64 = 9;
pub const AR_BXOR: u64 = 10;
pub const AR_BSL: u64 = 11;
pub const AR_BSR: u64 = 12;
pub const AR_BNOT: u64 = 13;

/// Signed magnitude addition helper: (na, ma) + (nb, mb).
fn int_signed_add(na: bool, ma: &[u64], nb: bool, mb: &[u64]) -> (bool, Vec<u64>) {
    if na == nb {
        return (na, bigint::mag_add(ma, mb));
    }
    match bigint::mag_cmp(ma, mb) {
        std::cmp::Ordering::Equal => (false, Vec::new()),
        std::cmp::Ordering::Greater => (na, bigint::mag_sub(ma, mb)),
        std::cmp::Ordering::Less => (nb, bigint::mag_sub(mb, ma)),
    }
}

/// Integer arithmetic (small or bignum operands) with promotion/demotion.
/// Results allocate in shared old space — never a GC point.
fn int_arith(ctx: &mut ProcCtx, op: u64, a: u64, b: u64) -> u64 {
    let (na, ma) = int_mag(a).unwrap();
    match op {
        AR_NEG => return make_int_mag(ctx, !na && !ma.is_empty(), &ma),
        AR_ABS => return make_int_mag(ctx, false, &ma),
        AR_BNOT => {
            // bnot(x) = -x - 1
            return if na {
                make_int_mag(ctx, false, &bigint::mag_sub(&ma, &[1]))
            } else {
                make_int_mag(ctx, true, &bigint::mag_add(&ma, &[1]))
            };
        }
        _ => {}
    }
    let (nb, mb) = int_mag(b).unwrap();
    match op {
        AR_ADD => {
            let (n, m) = int_signed_add(na, &ma, nb, &mb);
            make_int_mag(ctx, n, &m)
        }
        AR_SUB => {
            let (n, m) = int_signed_add(na, &ma, !nb && !mb.is_empty(), &mb);
            make_int_mag(ctx, n, &m)
        }
        AR_MUL => {
            let m = bigint::mag_mul(&ma, &mb);
            make_int_mag(ctx, na != nb && !m.is_empty(), &m)
        }
        AR_IDIV | AR_REM => {
            if mb.is_empty() {
                return raise_badarith(ctx);
            }
            // truncating division; rem takes the dividend's sign (Erlang)
            let (q, r) = bigint::mag_divrem(&ma, &mb);
            if op == AR_IDIV {
                make_int_mag(ctx, (na != nb) && !q.is_empty(), &q)
            } else {
                make_int_mag(ctx, na && !r.is_empty(), &r)
            }
        }
        AR_FDIV => {
            let (x, y) = (num_val(a), num_val(b));
            if y == 0.0 {
                return raise_badarith(ctx);
            }
            box_float(ctx, x / y)
        }
        AR_BAND | AR_BOR | AR_BXOR => {
            if a & TAG_MASK == TAG_SMALL && b & TAG_MASK == TAG_SMALL {
                // exact for all smalls (results never leave the small range)
                let (x, y) = (a as i64 >> 3, b as i64 >> 3);
                let r = match op {
                    AR_BAND => x & y,
                    AR_BOR => x | y,
                    _ => x ^ y,
                };
                return ((r << 3) as u64) | TAG_SMALL;
            }
            if na || nb {
                // infinite-two's-complement on negative bignums: the fiddly
                // corner nothing on our paths needs yet
                abort_bignum("bit op on a negative bignum (TODO(bignum-bitops))");
            }
            let n = std::cmp::max(ma.len(), mb.len());
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                let (x, y) = (*ma.get(i).unwrap_or(&0), *mb.get(i).unwrap_or(&0));
                out.push(match op {
                    AR_BAND => x & y,
                    AR_BOR => x | y,
                    _ => x ^ y,
                });
            }
            make_int_mag(ctx, false, &bigint::normalize(out))
        }
        AR_BSL | AR_BSR => {
            // shift counts must be smalls (a bignum-sized shift would be an
            // absurd allocation; BEAM raises system_limit far earlier)
            if b & TAG_MASK != TAG_SMALL {
                return raise_badarith(ctx);
            }
            let y = b as i64 >> 3;
            // Erlang: a negative count reverses direction
            let n = if op == AR_BSR { -y } else { y };
            if n >= 0 {
                let m = bigint::mag_shl(&ma, n as u64);
                make_int_mag(ctx, na && !m.is_empty(), &m)
            } else {
                let k = (-n) as u64;
                if na {
                    // floor semantics: x >> k = -((|x| - 1) >> k) - 1
                    let m = bigint::mag_shr(&bigint::mag_sub(&ma, &[1]), k);
                    make_int_mag(ctx, true, &bigint::mag_add(&m, &[1]))
                } else {
                    let m = bigint::mag_shr(&ma, k);
                    make_int_mag(ctx, false, &m)
                }
            }
        }
        _ => raise_badarith(ctx),
    }
}

/// Arithmetic slow path: anything that isn't the inline both-small-int
/// fast case (including small overflow, which promotes to bignums here).
/// Mixed/float ops produce boxed floats; non-numbers and integer-only ops
/// on floats raise badarith like BEAM.
#[no_mangle]
pub extern "C" fn mana_rt_arith(ctx: *mut ProcCtx, op: u64, a: u64, b: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let unary = matches!(op, AR_NEG | AR_ABS | AR_BNOT);
    if is_int_term(a) && (unary || is_int_term(b)) {
        return int_arith(ctx, op, a, b);
    }
    // bit ops are integer-only: no float coercion
    if let AR_BAND | AR_BOR | AR_BXOR | AR_BSL | AR_BSR | AR_BNOT = op {
        return raise_badarith(ctx);
    }
    let Some((x, _)) = num_of(a) else {
        return raise_badarith(ctx);
    };
    match op {
        AR_NEG => return box_float(ctx, -x),
        AR_ABS => return box_float(ctx, x.abs()),
        _ => {}
    }
    let Some((y, _)) = num_of(b) else {
        return raise_badarith(ctx);
    };
    match op {
        AR_ADD => box_float(ctx, x + y),
        AR_SUB => box_float(ctx, x - y),
        AR_MUL => box_float(ctx, x * y),
        AR_FDIV => {
            if y == 0.0 {
                return raise_badarith(ctx);
            }
            box_float(ctx, x / y)
        }
        // div/rem are integer-only → at least one float here → badarith
        AR_IDIV | AR_REM => raise_badarith(ctx),
        _ => raise_badarith(ctx),
    }
}

/// math module (all f64; domain errors are badarith like BEAM).
#[no_mangle]
pub extern "C" fn mana_rt_math(ctx: *mut ProcCtx, op: u64, a: u64, b: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((x, _)) = num_of(a) else {
        return raise_badarith(ctx);
    };
    let y = match num_of(b) {
        Some((y, _)) => y,
        None => 0.0, // unary ops pass a dummy small 0
    };
    let r = match op {
        0 => x.sqrt(),
        1 => x.powf(y),
        2 => x.ln(),
        3 => x.log2(),
        4 => x.log10(),
        5 => x.exp(),
        6 => x.sin(),
        7 => x.cos(),
        8 => x.tan(),
        9 => x.asin(),
        10 => x.acos(),
        11 => x.atan(),
        12 => x.atan2(y),
        13 => x % y,                     // fmod
        14 => std::f64::consts::PI,     // pi/0
        15 => x.floor(),
        16 => x.ceil(),
        _ => return raise_badarith(ctx),
    };
    if r.is_nan() || r.is_infinite() {
        return raise_badarith(ctx);
    }
    box_float(ctx, r)
}

/// erlang:float/1.
#[no_mangle]
pub extern "C" fn mana_rt_to_float(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    match num_of(t) {
        Some((x, true)) => box_float(ctx, x),
        Some((_, false)) => t,
        None => raise_badarg(ctx),
    }
}

/// trunc/round/floor/ceil → integers (mode 0..3).
#[no_mangle]
pub extern "C" fn mana_rt_f2i(ctx: *mut ProcCtx, mode: u64, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((x, xi)) = num_of(t) else {
        return raise_badarg(ctx);
    };
    if xi {
        return t;
    }
    let r = match mode {
        0 => x.trunc(),
        1 => x.round(),
        2 => x.floor(),
        _ => x.ceil(),
    };
    if !r.is_finite() {
        return raise_badarg(ctx);
    }
    let mag = bigint::f64_to_mag(r.abs());
    make_int_mag(ctx, r < 0.0 && !mag.is_empty(), &mag)
}

/// Elixir.Float round/ceil/floor with decimal precision (mode 0/1/2).
/// Elixir operates on the shortest decimal representation of the float;
/// formatting at the target precision reproduces that (half-to-even ties,
/// matching Rust's formatter and Elixir's documented behavior).
#[no_mangle]
pub extern "C" fn mana_rt_float_prec(ctx: *mut ProcCtx, t: u64, prec: u64, mode: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((x, is_int)) = num_of(t) else {
        return raise_badarg(ctx);
    };
    if is_int || prec & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let p = prec as i64 >> 3;
    if !(0..=15).contains(&p) {
        return raise_badarg(ctx);
    }
    let r = match mode {
        0 => {
            let s = format!("{:.*}", p as usize, x);
            s.parse::<f64>().unwrap_or(x)
        }
        1 => {
            let shift = 10f64.powi(p as i32);
            (x * shift).ceil() / shift
        }
        _ => {
            let shift = 10f64.powi(p as i32);
            (x * shift).floor() / shift
        }
    };
    box_float(ctx, r)
}

/// erlang:display's float format: C-style %e with 6 fractional digits and
/// a signed two-digit exponent (1.000000e+00, 1.234568e+05, 1.000000e-05).
fn display_float(f: f64) -> String {
    let s = format!("{:.6e}", f); // Rust: "1.000000e0" / "1.234568e5"
    match s.split_once('e') {
        Some((mant, exp)) => {
            let (sign, digits) = match exp.strip_prefix('-') {
                Some(d) => ('-', d),
                None => ('+', exp),
            };
            format!("{}e{}{:0>2}", mant, sign, digits)
        }
        None => s,
    }
}

/// BEAM-parity float text: shortest round-trip with a mandatory decimal
/// point, exponent form matching OTP's Ryu-based printer (1.0, 0.1,
/// 1.0e20, 1.0e-5, -0.0).
fn fmt_float(f: f64) -> String {
    if f == f64::INFINITY || f == f64::NEG_INFINITY || f.is_nan() {
        return "nan_or_inf".into(); // unreachable: terms never hold these
    }
    let s = format!("{:?}", f); // Rust shortest round-trip
    if let Some(epos) = s.find(['e', 'E']) {
        // Rust: "1e20"; Erlang: "1.0e20"
        let (m, e) = s.split_at(epos);
        let mant = if m.contains('.') { m.to_string() } else { format!("{}.0", m) };
        return format!("{}{}", mant, e);
    }
    if !s.contains('.') {
        return format!("{}.0", s);
    }
    s
}

/// erlang:float_to_binary/1,2 and float_to_list — options: [:short]
/// (shortest round-trip), {:decimals, N} (+ :compact trims zeros); no
/// options = %e like BEAM.
#[no_mangle]
pub extern "C" fn mana_rt_float_to_binary(ctx: *mut ProcCtx, t: u64, opts: u64, as_list: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((x, false)) = num_of(t) else {
        return raise_badarg(ctx);
    };
    let (mut decimals, mut compact, mut short) = (None::<usize>, false, false);
    let mut cur = opts;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let opt = unsafe { *p };
        if opt & TAG_MASK == TAG_ATOM {
            match atom_bytes(opt) {
                b"short" => short = true,
                b"compact" => compact = true,
                _ => {}
            }
        } else if opt & TAG_MASK == TAG_BOXED && opt != 0 {
            let hp = opt as *const u64;
            let h = unsafe { *hp };
            if h & 0xff == KIND_TUPLE
                && h >> 8 == 2
                && atom_bytes(unsafe { *hp.add(1) }) == b"decimals"
            {
                let d = unsafe { *hp.add(2) };
                if d & TAG_MASK == TAG_SMALL {
                    decimals = Some((d as i64 >> 3).clamp(0, 253) as usize);
                }
            }
        }
        cur = unsafe { *p.add(1) };
    }
    let s = if short {
        fmt_float(x)
    } else if let Some(d) = decimals {
        let mut s = format!("{:.*}", d, x);
        if compact && s.contains('.') {
            while s.ends_with('0') {
                s.pop();
            }
            if s.ends_with('.') {
                s.push('0');
            }
        }
        s
    } else {
        display_float(x)
    };
    if as_list != 0 {
        utf8_to_codepoint_list(ctx, s.as_bytes())
    } else {
        bytes_to_new_bin(ctx, s.as_bytes())
    }
}

/// erlang:binary_to_float/1 and list_to_float/1 (bytes pre-flattened).
#[no_mangle]
pub extern "C" fn mana_rt_parse_float(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let bytes: Vec<u8> = if bin_parts(t).is_some() {
        bin_bytes(t).to_vec()
    } else {
        let mut out = Vec::new();
        let mut cur = t;
        loop {
            if cur == NIL {
                break;
            }
            if cur & TAG_MASK != TAG_CONS {
                return raise_badarg(ctx);
            }
            let p = (cur & !TAG_MASK) as *const u64;
            let h = unsafe { *p };
            if h & TAG_MASK != TAG_SMALL {
                return raise_badarg(ctx);
            }
            out.push((h as i64 >> 3) as u8);
            cur = unsafe { *p.add(1) };
        }
        out
    };
    let s = match std::str::from_utf8(&bytes) {
        Ok(s) => s,
        Err(_) => return raise_badarg(ctx),
    };
    // BEAM requires a decimal point ("1" is badarg for binary_to_float)
    if !s.contains('.') {
        return raise_badarg(ctx);
    }
    match s.parse::<f64>() {
        Ok(f) if f.is_finite() => box_float(ctx, f),
        _ => raise_badarg(ctx),
    }
}

// ---------------------------------------------------------------------------
// time

fn monotonic_epoch() -> std::time::Instant {
    static EPOCH: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
    *EPOCH.get_or_init(std::time::Instant::now)
}

/// Convert nanoseconds to the requested unit term (atom or integer hertz).
fn in_time_unit(ctx: &mut ProcCtx, nanos: i128, unit: u64) -> u64 {
    let v: i128 = if unit & TAG_MASK == TAG_SMALL {
        let hz = unit as i64 >> 3;
        if hz <= 0 {
            return raise_badarg(ctx);
        }
        nanos * hz as i128 / 1_000_000_000
    } else if unit & TAG_MASK == TAG_ATOM {
        match atom_bytes(unit) {
            b"native" | b"nanosecond" | b"nano_seconds" => nanos,
            b"microsecond" | b"micro_seconds" => nanos / 1_000,
            b"millisecond" | b"milli_seconds" => nanos / 1_000_000,
            b"second" | b"seconds" => nanos / 1_000_000_000,
            b"perf_counter" => nanos,
            _ => return raise_badarg(ctx),
        }
    } else {
        return raise_badarg(ctx);
    };
    let neg = v < 0;
    let uv = v.unsigned_abs();
    let mag = bigint::normalize(vec![uv as u64, (uv >> 64) as u64]);
    make_int_mag(ctx, neg && !mag.is_empty(), &mag)
}

/// erlang:fun_info/2 — closures carry no module/name metadata; arity and
/// env answer truthfully, the rest is undefined (callers only thread the
/// {Item, Value} shape through — Agent's initial_call bookkeeping).
#[no_mangle]
pub extern "C" fn mana_rt_fun_info(ctx: *mut ProcCtx, fun: u64, item: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if fun & TAG_MASK != TAG_BOXED || fun == 0 || item & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let header = unsafe { *(fun as *const u64) };
    if header & 0xff != KIND_FUN {
        return raise_badarg(ctx);
    }
    let value = match atom_bytes(item) {
        b"arity" => ((((header >> 8) & 0xff) << 3) as u64) | TAG_SMALL,
        b"env" => NIL,
        // closures carry no MFA metadata — every fun reports as local
        // (telemetry:attach warns-and-proceeds on local; BEAM would say
        // external for `fun M:F/A` captures — documented divergence)
        b"type" => atom_intern(b"local"),
        _ => known().undefined,
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, item, value];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let t = alloc_nursery(ctx, 3);
    ctx.roots_head = saved;
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = fr[2];
        *t.add(2) = fr[3];
    }
    t as u64
}

/// erlang:fun_info_mfa/1 — closures carry no MFA metadata; arity is real,
/// module/name are undefined (callers only display them).
#[no_mangle]
pub extern "C" fn mana_rt_fun_info_mfa(ctx: *mut ProcCtx, fun: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if fun & TAG_MASK != TAG_BOXED || fun == 0 {
        return raise_badarg(ctx);
    }
    let header = unsafe { *(fun as *const u64) };
    if header & 0xff != KIND_FUN {
        return raise_badarg(ctx);
    }
    let arity = (header >> 8) & 0xff;
    let t = alloc_nursery(ctx, 4);
    unsafe {
        *t = (3 << 8) | KIND_TUPLE;
        *t.add(1) = known().undefined;
        *t.add(2) = known().undefined;
        *t.add(3) = (arity << 3) | TAG_SMALL;
    }
    t as u64
}

/// erlang:is_process_alive/1.
#[no_mangle]
pub extern "C" fn mana_rt_is_process_alive(ctx: *mut ProcCtx, pid: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if pid & 0xF != PID_TAG4 {
        return raise_badarg(ctx);
    }
    if proc_ref(ctx.global, (pid >> 4) as usize).is_some() {
        known().true_a
    } else {
        known().false_a
    }
}

/// erlang:monotonic_time/1 (unit 'native' == nanosecond here).
#[no_mangle]
pub extern "C" fn mana_rt_monotonic_time(ctx: *mut ProcCtx, unit: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let nanos = monotonic_epoch().elapsed().as_nanos() as i128;
    in_time_unit(ctx, nanos, unit)
}

/// erlang:system_time/1 — true Unix epoch; nanosecond magnitudes come
/// back as bignums.
#[no_mangle]
pub extern "C" fn mana_rt_system_time(ctx: *mut ProcCtx, unit: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    // true Unix epoch: absolute nanoseconds exceed the small range and
    // come back as bignums (the old 2020-offset hack put every absolute
    // wall-clock reading 50 years in the past — the famous 1976 Date
    // header)
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos() as i128)
        .unwrap_or(0);
    in_time_unit(ctx, nanos, unit)
}

/// erlang:convert_time_unit/3 — from/to as unit terms.
#[no_mangle]
pub extern "C" fn mana_rt_convert_time_unit(
    ctx: *mut ProcCtx,
    t: u64,
    from: u64,
    to: u64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let v: i128 = if t & TAG_MASK == TAG_SMALL {
        (t as i64 >> 3) as i128
    } else if let Some((neg, mag)) = bignum_parts(t) {
        // wall-clock magnitudes fit two limbs comfortably
        if mag.len() > 2 {
            return raise_badarg(ctx);
        }
        let uv = mag[0] as i128
            | ((*mag.get(1).unwrap_or(&0) as i128) << 64);
        if neg { -uv } else { uv }
    } else {
        return raise_badarg(ctx);
    };
    let nanos: i128 = if from & TAG_MASK == TAG_SMALL {
        let hz = from as i64 >> 3;
        if hz <= 0 {
            return raise_badarg(ctx);
        }
        v * 1_000_000_000 / hz as i128
    } else {
        match atom_bytes(from) {
            b"native" | b"nanosecond" | b"nano_seconds" => v,
            b"microsecond" | b"micro_seconds" => v * 1_000,
            b"millisecond" | b"milli_seconds" => v * 1_000_000,
            b"second" | b"seconds" => v * 1_000_000_000,
            _ => return raise_badarg(ctx),
        }
    };
    in_time_unit(ctx, nanos, to)
}

/// erlang:system_info/1 — the closed-world answer sheet. Extend as
/// callers appear; unknown items raise badarg (loud).
#[no_mangle]
pub extern "C" fn mana_rt_system_info(ctx: *mut ProcCtx, item: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if item & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let cpus = || {
        std::thread::available_parallelism()
            .map(|n| n.get() as u64)
            .unwrap_or(1)
    };
    match atom_bytes(item) {
        b"endian" => find_atom("little").unwrap_or(NIL),
        b"otp_release" => bytes_to_charlist(ctx, b"26"),
        b"system_version" => bytes_to_charlist(ctx, b"mana\n"),
        b"version" => bytes_to_charlist(ctx, b"14.0"),
        b"emu_flavor" => atom_intern(b"emu"),
        b"os_type" => {
            let t = alloc_nursery(ctx, 3);
            unsafe {
                *t = (2 << 8) | KIND_TUPLE;
                *t.add(1) = atom_intern(b"unix");
                *t.add(2) = atom_intern(b"linux");
            }
            t as u64
        }
        b"logical_processors" | b"logical_processors_available"
        | b"logical_processors_online" => ((cpus() << 3) as u64) | TAG_SMALL,
        b"schedulers" | b"schedulers_online" => {
            let n = ctx.global.n_scheds as u64;
            ((n << 3) as u64) | TAG_SMALL
        }
        // telemetry_poller system_counts — real where cheap, plausible
        // constants for the BEAM-only limits
        b"process_count" => {
            let n = ctx.global.procs.read().iter().filter(|s| s.is_some()).count() as u64;
            ((n << 3) as u64) | TAG_SMALL
        }
        b"atom_count" => ((interned_atom_count() << 3) as u64) | TAG_SMALL,
        b"port_count" => TAG_SMALL, // 0
        b"process_limit" => ((262_144u64 << 3) as u64) | TAG_SMALL,
        b"atom_limit" => ((1_048_576u64 << 3) as u64) | TAG_SMALL,
        b"port_limit" => ((65_536u64 << 3) as u64) | TAG_SMALL,
        b"os_monotonic_time_source" => {
            // property list benchee's repeated_measurement reads
            let cell = alloc_nursery(ctx, 2);
            let t = alloc_nursery(ctx, 3);
            unsafe {
                *t = (2 << 8) | KIND_TUPLE;
                *t.add(1) = atom_intern(b"resolution");
                *t.add(2) = ((1_000_000_000u64) << 3) | TAG_SMALL;
                *cell = t as u64;
                *cell.add(1) = NIL;
            }
            cell as u64 | TAG_CONS
        }
        _ => raise_badarg(ctx),
    }
}

/// Elixir.System.cmd/2,3 (native override): run a command, capture stdout,
/// return {Output, ExitCode}. Synchronous on the calling scheduler thread —
/// fine for system probing; real port support is TODO(port).
#[no_mangle]
pub extern "C" fn mana_rt_system_cmd(ctx: *mut ProcCtx, cmd: u64, args: u64, _opts: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some(cmd_b) = term_to_source(cmd) else {
        return raise_badarg(ctx);
    };
    let Ok(cmd_s) = String::from_utf8(cmd_b) else {
        return raise_badarg(ctx);
    };
    let mut argv: Vec<String> = Vec::new();
    let mut cur = args;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        let Some(b) = term_to_source(h) else {
            return raise_badarg(ctx);
        };
        let Ok(s) = String::from_utf8(b) else {
            return raise_badarg(ctx);
        };
        argv.push(s);
        cur = unsafe { *p.add(1) };
    }
    let out = std::process::Command::new(&cmd_s).args(&argv).output();
    let (bytes, code): (Vec<u8>, i64) = match out {
        Ok(o) => (o.stdout, o.status.code().unwrap_or(1) as i64),
        Err(_) => (Vec::new(), 127),
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, 0];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    fr[2] = bytes_to_new_bin(ctx, &bytes);
    let t = alloc_nursery(ctx, 3);
    ctx.roots_head = saved;
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = fr[2];
        *t.add(2) = ((code << 3) as u64) | TAG_SMALL;
    }
    t as u64
}

/// timer:tc — time a fun application in microseconds → {Us, Result}.
#[no_mangle]
pub extern "C" fn mana_rt_timer_tc(ctx: *mut ProcCtx, fun: u64, args: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    let t0 = monotonic_epoch().elapsed();
    let v = mana_rt_apply_fun(ctx, fun, args);
    if v == EXC_SENTINEL {
        return v;
    }
    let us = (monotonic_epoch().elapsed() - t0).as_micros() as i64;
    let ctxr = unsafe { &mut *ctx };
    let saved = ctxr.roots_head;
    let mut fr = [0u64, 1, v];
    fr[0] = saved;
    ctxr.roots_head = fr.as_ptr() as u64;
    let t = alloc_nursery(ctxr, 3);
    ctxr.roots_head = saved;
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = ((us << 3) as u64) | TAG_SMALL;
        *t.add(2) = fr[2];
    }
    let _ = ctxr;
    t as u64
}

// ---------------------------------------------------------------------------
// timers (send_after / start_timer / cancel_timer)
//
// A dedicated timer thread sleeps until the nearest deadline and delivers
// by pushing to the target's ingress + waking its scheduler (the same
// cross-thread path sends use). Messages are eternal deep copies —
// immortal, so the timer heap needs no GC integration; timer volume is
// low on our paths — TODO(timer-gc).

struct TimerEntry {
    deadline: std::time::Instant,
    ref_id: u64,
    dest_pid: Option<usize>,
    dest_name: Option<u64>, // registered-name atom, resolved at fire time
    msg: u64,               // eternal
}

struct Timers {
    entries: Vec<TimerEntry>,
    global: &'static Global,
    thread_started: bool,
}

static TIMERS: std::sync::Mutex<Option<Timers>> = std::sync::Mutex::new(None);
static TIMER_CV: std::sync::Condvar = std::sync::Condvar::new();

/// The timer thread is OUTSIDE the STW protocol, so it must not mutate
/// process/scheduler state directly (a state flip mid-major corrupts the
/// run queues). It only enqueues (pid, msg) here and wakes a scheduler;
/// schedulers drain at their loop top — a safepoint.
static TIMER_DELIVERIES: SegQueue<(usize, u64)> = SegQueue::new();

fn deliver_cross_thread(g: &'static Global, id: usize, msg: u64) {
    TIMER_DELIVERIES.push((id, msg));
    for s in 0..g.n_scheds {
        wake_sched(g, s);
    }
}

/// Called from the scheduler loop (a safepoint-adjacent context).
fn drain_timer_deliveries(ctx: &mut ProcCtx) {
    while let Some((id, msg)) = TIMER_DELIVERIES.pop() {
        push_and_wake(ctx, id, msg);
    }
}

fn timer_thread() {
    loop {
        let mut guard = TIMERS.lock().unwrap();
        loop {
            let now = std::time::Instant::now();
            let t = guard.as_mut().unwrap();
            let g = t.global;
            // fire everything due
            let mut i = 0;
            while i < t.entries.len() {
                if t.entries[i].deadline <= now {
                    let e = t.entries.swap_remove(i);
                    let pid = e.dest_pid.or_else(|| {
                        e.dest_name.and_then(|name| {
                            NAME_REGISTRY
                                .lock()
                                .unwrap()
                                .as_ref()
                                .and_then(|m| m.get(&name).copied())
                        })
                    });
                    if let Some(pid) = pid {
                        deliver_cross_thread(g, pid, e.msg);
                    }
                } else {
                    i += 1;
                }
            }
            let next = t.entries.iter().map(|e| e.deadline).min();
            match next {
                Some(dl) => {
                    let wait = dl.saturating_duration_since(std::time::Instant::now());
                    let (g2, _) = TIMER_CV.wait_timeout(guard, wait).unwrap();
                    guard = g2;
                }
                None => {
                    guard = TIMER_CV.wait(guard).unwrap();
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// io reactor (mio) — sockets only; files are direct syscalls (TODO(io-pool)).
//
// Same discipline as the timer thread: the reactor is OUTSIDE the STW
// protocol and never mutates process/scheduler state. It pushes (pid, sock,
// kind) wake tokens to IO_WAKES and pokes the scheduler condvars; schedulers
// drain at their loop top — a safepoint. Blocking syscalls MUST NOT run on
// scheduler threads (the STW requester waits for every scheduler to reach a
// safepoint — a blocked syscall deadlocks GC). Sockets are nonblocking:
// scheduler threads only ever issue nonblocking syscalls and park the
// process on WouldBlock.
//
// Wake protocol (no lost wakeups): a parker first writes itself into the
// socket entry's waiter slot, ensures the socket is registered, retries the
// syscall, and only then parks (Waiting + suspend). The reactor takes the
// waiter and pushes a wake. If the wake arrives while the parker is still
// Running (the tiny pre-suspend window), drain_io_wakes re-pushes the token
// as long as the waiter slot still names that pid — it converges as soon as
// the parker either suspends (flip succeeds) or completes and clears the
// slot (token dropped as stale).

enum SockSource {
    Listener(mio::net::TcpListener),
    Stream(mio::net::TcpStream),
}

/// {active, false | once | true}
#[derive(Clone, Copy, PartialEq)]
enum ActiveMode {
    Passive,
    Once,
    Always,
}

struct SockEntry {
    source: SockSource,
    /// pid parked waiting for readability (recv/accept), if any
    read_waiter: Option<usize>,
    /// pid parked waiting for writability (send/connect), if any
    write_waiter: Option<usize>,
    /// registered with the reactor's poll (edge-triggered readiness is
    /// re-armed by the kernel on new activity, and parkers only park after
    /// WouldBlock, so edges are never missed)
    registered: bool,
    owner: usize,
    active: ActiveMode,
    /// binary (true) vs charlist (false) delivery
    binary: bool,
    /// passive-recv buffer (exact-length recv accumulates here)
    rbuf: Vec<u8>,
    /// byte counters for inet:getstat
    recv_oct: u64,
    send_oct: u64,
}

struct SocketTable {
    slots: Vec<Option<SockEntry>>,
    free: Vec<usize>,
}

impl SocketTable {
    fn insert(&mut self, e: SockEntry) -> usize {
        match self.free.pop() {
            Some(i) => {
                self.slots[i] = Some(e);
                i
            }
            None => {
                self.slots.push(Some(e));
                self.slots.len() - 1
            }
        }
    }
}

static SOCKETS: std::sync::Mutex<SocketTable> = std::sync::Mutex::new(SocketTable {
    slots: Vec::new(),
    free: Vec::new(),
});

/// (pid, socket idx, wanted-read) wake tokens from the reactor thread.
static IO_WAKES: SegQueue<(usize, usize, bool)> = SegQueue::new();
/// socket indices whose sources the reactor should register with its poll.
static REACTOR_CMDS: SegQueue<usize> = SegQueue::new();
static REACTOR_WAKER: std::sync::OnceLock<mio::Waker> = std::sync::OnceLock::new();
static REACTOR_STARTED: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

const REACTOR_WAKE_TOKEN: mio::Token = mio::Token(usize::MAX);

fn ensure_reactor(g: &'static Global) {
    if REACTOR_STARTED.swap(true, Ordering::AcqRel) {
        return;
    }
    std::thread::Builder::new()
        .name("mana-reactor".into())
        .spawn(move || reactor_thread(g))
        .expect("reactor thread");
    // wait for the waker to exist so callers can always poke the reactor
    while REACTOR_WAKER.get().is_none() {
        std::thread::yield_now();
    }
}

fn reactor_wake() {
    if let Some(w) = REACTOR_WAKER.get() {
        let _ = w.wake();
    }
}

fn reactor_thread(g: &'static Global) {
    let mut poll = mio::Poll::new().expect("mio poll");
    let waker = mio::Waker::new(poll.registry(), REACTOR_WAKE_TOKEN).expect("mio waker");
    REACTOR_WAKER.set(waker).ok();
    let mut events = mio::Events::with_capacity(256);
    loop {
        // (re)register sources requested since the last pass
        while let Some(idx) = REACTOR_CMDS.pop() {
            let mut tab = SOCKETS.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                continue; // closed before we got to it
            };
            let interests = mio::Interest::READABLE | mio::Interest::WRITABLE;
            let res = match &mut entry.source {
                SockSource::Listener(l) => {
                    poll.registry().register(l, mio::Token(idx), interests)
                }
                SockSource::Stream(s) => {
                    poll.registry().register(s, mio::Token(idx), interests)
                }
            };
            let _ = res; // AlreadyExists on a duplicate request is fine
        }
        if poll.poll(&mut events, None).is_err() {
            continue; // EINTR
        }
        let mut woke = false;
        for ev in events.iter() {
            if ev.token() == REACTOR_WAKE_TOKEN {
                continue; // command pass runs at loop top
            }
            let idx = ev.token().0;
            let mut tab = SOCKETS.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                continue;
            };
            let closed = ev.is_read_closed() || ev.is_write_closed() || ev.is_error();
            if ev.is_readable() || closed {
                if let Some(pid) = entry.read_waiter.take() {
                    IO_WAKES.push((pid, idx, true));
                    woke = true;
                } else if entry.active != ActiveMode::Passive {
                    // no parked reader: schedule an active-mode pump
                    IO_ACTIVE.push(idx);
                    woke = true;
                }
            }
            if ev.is_writable() || closed {
                if let Some(pid) = entry.write_waiter.take() {
                    IO_WAKES.push((pid, idx, false));
                    woke = true;
                }
            }
        }
        if woke {
            for s in 0..g.n_scheds {
                wake_sched(g, s);
            }
        }
    }
}

/// Scheduler-side drain (loop-top safepoint, like timer deliveries).
/// Wake-only: no mailbox message — the woken BIF retries its nonblocking
/// syscall.
fn drain_io_wakes(ctx: &mut ProcCtx) {
    let global = ctx.global;
    let n = IO_WAKES.len();
    for _ in 0..n {
        let Some((pid, idx, is_read)) = IO_WAKES.pop() else { break };
        let Some(cell) = proc_ref(global, pid) else {
            continue;
        };
        let p = unsafe { &*cell.0.get() };
        let mut st = p.state.lock();
        if matches!(*st, PState::Waiting(_)) {
            *st = PState::Runnable;
            drop(st);
            if p.home == ctx.sched_id {
                ctx.run_q.push_back(pid);
            } else {
                global.scheds[p.home].inject.push(pid);
                wake_sched(global, p.home);
            }
            continue;
        }
        drop(st);
        // parker not suspended yet: keep the token alive while the waiter
        // slot still names it; drop once the op completed (stale wake)
        let tab = SOCKETS.lock().unwrap();
        let still_waiting = tab.slots.get(idx).and_then(|s| s.as_ref()).is_some_and(|e| {
            if is_read {
                e.read_waiter == Some(pid)
            } else {
                e.write_waiter == Some(pid)
            }
        });
        drop(tab);
        if still_waiting {
            IO_WAKES.push((pid, idx, is_read));
        }
    }
}

// ---------------------------------------------------------------------------
// file (native cut: OTP's file.erl/prim_file are never compiled)
//
// Direct blocking syscalls on the scheduler thread — same as stdout today.
// Local-disk ops are µs-scale; the honest fix is a blocking pool
// (TODO(io-pool)): a scheduler stuck in a slow syscall (NFS...) stalls STW
// for its duration.

struct FileEntry {
    file: std::fs::File,
    binary: bool,
}

struct FileTable {
    slots: Vec<Option<FileEntry>>,
    free: Vec<usize>,
}

static FILES: std::sync::Mutex<FileTable> = std::sync::Mutex::new(FileTable {
    slots: Vec::new(),
    free: Vec::new(),
});

/// Raw byte list (no utf8 decoding — file:read in list mode is bytes).
fn bytes_to_byte_list(ctx: &mut ProcCtx, bytes: &[u8]) -> u64 {
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &b in bytes.iter().rev() {
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = ((b as u64) << 3) | TAG_SMALL;
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[2]
}

/// posix error atom for an io::Error (BEAM's file:posix() names).
fn posix_atom(e: &std::io::Error) -> u64 {
    let name: &[u8] = match e.raw_os_error() {
        Some(libc) => match libc {
            1 => b"eperm",
            2 => b"enoent",
            9 => b"ebadf",
            13 => b"eacces",
            17 => b"eexist",
            18 => b"exdev",
            20 => b"enotdir",
            21 => b"eisdir",
            22 => b"einval",
            28 => b"enospc",
            36 => b"enametoolong",
            // BEAM's efile maps ENOTEMPTY to eexist (ancient compat quirk)
            39 => b"eexist",
            _ => b"einval",
        },
        None => match e.kind() {
            std::io::ErrorKind::NotFound => b"enoent",
            std::io::ErrorKind::PermissionDenied => b"eacces",
            std::io::ErrorKind::AlreadyExists => b"eexist",
            _ => b"einval",
        },
    };
    atom_intern(name)
}

/// Extract a filesystem path from chardata / an atom.
fn path_of(t: u64) -> Result<std::path::PathBuf, ()> {
    let mut bytes = Vec::new();
    if t & TAG_MASK == TAG_ATOM {
        bytes.extend_from_slice(atom_bytes(t));
    } else {
        chardata_flatten(t, &mut bytes)?;
    }
    let s = String::from_utf8(bytes).map_err(|_| ())?;
    Ok(std::path::PathBuf::from(s))
}

/// {Tag, Value} in the nursery, rooting Value across the alloc.
fn pair_term(ctx: &mut ProcCtx, tag: &[u8], v: u64) -> u64 {
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, v];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let p = alloc_nursery(ctx, 3);
    unsafe {
        *p = (2 << 8) | KIND_TUPLE;
        *p.add(1) = atom_intern(tag);
        *p.add(2) = fr[2];
    }
    ctx.roots_head = saved;
    p as u64
}

fn err_tuple(ctx: &mut ProcCtx, e: &std::io::Error) -> u64 {
    let a = posix_atom(e);
    pair_term(ctx, b"error", a)
}

fn file_handle(ctx: &mut ProcCtx, idx: usize) -> u64 {
    let p = alloc_nursery(ctx, 3);
    unsafe {
        *p = (2 << 8) | KIND_TUPLE;
        *p.add(1) = atom_intern(b"mana_file");
        *p.add(2) = ((idx as u64) << 3) | TAG_SMALL;
    }
    p as u64
}

fn file_resolve(t: u64) -> Option<usize> {
    if t & TAG_MASK != TAG_BOXED || t == 0 {
        return None;
    }
    unsafe {
        let p = t as *const u64;
        if *p != (2 << 8) | KIND_TUPLE {
            return None;
        }
        let tag = *p.add(1);
        if tag & TAG_MASK != TAG_ATOM || atom_bytes(tag) != b"mana_file" {
            return None;
        }
        let idx = *p.add(2);
        if idx & TAG_MASK != TAG_SMALL {
            return None;
        }
        Some((idx as i64 >> 3) as usize)
    }
}

/// posix seconds → {{Y,M,D},{H,Mi,S}} (UTC; 'local' is answered as UTC —
/// documented divergence, conformance uses {time, posix}).
fn civil_datetime(ctx: &mut ProcCtx, secs: i64) -> u64 {
    let days = secs.div_euclid(86400);
    let rem = secs.rem_euclid(86400);
    let (h, mi, s) = (rem / 3600, (rem % 3600) / 60, rem % 60);
    // Howard Hinnant's civil_from_days
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    let small = |v: i64| ((v << 3) as u64) | TAG_SMALL;
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let dt = alloc_nursery(ctx, 4);
    unsafe {
        *dt = (3 << 8) | KIND_TUPLE;
        *dt.add(1) = small(y);
        *dt.add(2) = small(m);
        *dt.add(3) = small(d);
    }
    fr[2] = dt as u64;
    let tm = alloc_nursery(ctx, 4);
    unsafe {
        *tm = (3 << 8) | KIND_TUPLE;
        *tm.add(1) = small(h);
        *tm.add(2) = small(mi);
        *tm.add(3) = small(s);
    }
    fr[3] = tm as u64;
    let pair = alloc_nursery(ctx, 3);
    unsafe {
        *pair = (2 << 8) | KIND_TUPLE;
        *pair.add(1) = fr[2];
        *pair.add(2) = fr[3];
    }
    ctx.roots_head = saved;
    pair as u64
}

// file op codes (codegen compile_file_bif mirrors these)
pub const F_READ_FILE: u64 = 0;
pub const F_WRITE_FILE: u64 = 1;
pub const F_WRITE_FILE3: u64 = 2;
pub const F_OPEN: u64 = 3;
pub const F_CLOSE: u64 = 4;
pub const F_READ: u64 = 5;
pub const F_WRITE: u64 = 6;
pub const F_POSITION: u64 = 7;
pub const F_DELETE: u64 = 8;
pub const F_RENAME: u64 = 9;
pub const F_MAKE_DIR: u64 = 10;
pub const F_DEL_DIR: u64 = 11;
pub const F_LIST_DIR: u64 = 12;
pub const F_FILE_INFO: u64 = 13;
pub const F_FILE_INFO2: u64 = 14;
pub const F_COPY: u64 = 15;
pub const F_GET_CWD: u64 = 16;

#[no_mangle]
pub extern "C" fn mana_rt_file(ctx: *mut ProcCtx, op: u64, a: u64, b: u64, c: u64) -> u64 {
    use std::io::{Read, Seek, Write};
    let ctx = unsafe { &mut *ctx };
    let ok_atom = || atom_intern(b"ok");
    match op {
        F_READ_FILE => {
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            match std::fs::read(&path) {
                Ok(bytes) => {
                    let bin = bytes_to_new_bin(ctx, &bytes);
                    pair_term(ctx, b"ok", bin)
                }
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_WRITE_FILE | F_WRITE_FILE3 => {
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            let mut data = Vec::new();
            if iolist_flatten(b, &mut data).is_err() {
                return raise_badarg(ctx);
            }
            let mut append = false;
            if op == F_WRITE_FILE3 {
                let mut cur = c;
                while cur & TAG_MASK == TAG_CONS {
                    let p = (cur & !TAG_MASK) as *const u64;
                    let m = unsafe { *p };
                    if m & TAG_MASK == TAG_ATOM && atom_bytes(m) == b"append" {
                        append = true;
                    }
                    cur = unsafe { *p.add(1) };
                }
            }
            let res = if append {
                std::fs::OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(&path)
                    .and_then(|mut f| f.write_all(&data))
            } else {
                std::fs::write(&path, &data)
            };
            match res {
                Ok(()) => ok_atom(),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_OPEN => {
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            // modes list: read | write | append | exclusive | binary
            // (raw/read_ahead/delayed_write accepted and ignored)
            let (mut read, mut write, mut append, mut excl, mut binary) =
                (false, false, false, false, false);
            let mut cur = b;
            while cur & TAG_MASK == TAG_CONS {
                let p = (cur & !TAG_MASK) as *const u64;
                let m = unsafe { *p };
                if m & TAG_MASK == TAG_ATOM {
                    match atom_bytes(m) {
                        b"read" => read = true,
                        b"write" => write = true,
                        b"append" => append = true,
                        b"exclusive" => excl = true,
                        b"binary" => binary = true,
                        _ => {}
                    }
                }
                cur = unsafe { *p.add(1) };
            }
            if !read && !write && !append {
                read = true;
            }
            let mut o = std::fs::OpenOptions::new();
            o.read(read || (!write && !append));
            if append {
                o.append(true).create(true);
            } else if write {
                o.write(true).create(true);
                if !read {
                    o.truncate(true);
                }
            }
            if excl {
                o.create_new(true);
            }
            match o.open(&path) {
                Ok(file) => {
                    let idx = FILES.lock().unwrap().insert(FileEntry { file, binary });
                    let h = file_handle(ctx, idx);
                    pair_term(ctx, b"ok", h)
                }
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_CLOSE => {
            let Some(idx) = file_resolve(a) else { return raise_badarg(ctx) };
            let mut tab = FILES.lock().unwrap();
            if idx < tab.slots.len() && tab.slots[idx].take().is_some() {
                tab.free.push(idx);
                ok_atom()
            } else {
                drop(tab);
                pair_term(ctx, b"error", atom_intern(b"ebadf"))
            }
        }
        F_READ => {
            let Some(idx) = file_resolve(a) else { return raise_badarg(ctx) };
            if b & TAG_MASK != TAG_SMALL || (b as i64 >> 3) < 0 {
                return raise_badarg(ctx);
            }
            let n = (b as i64 >> 3) as usize;
            let mut buf = vec![0u8; n];
            let mut tab = FILES.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                drop(tab);
                return pair_term(ctx, b"error", atom_intern(b"ebadf"));
            };
            let mut got = 0usize;
            let res = loop {
                match entry.file.read(&mut buf[got..]) {
                    Ok(0) => break Ok(got),
                    Ok(k) => {
                        got += k;
                        if got == n {
                            break Ok(got);
                        }
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                    Err(e) => break Err(e),
                }
            };
            let binary = entry.binary;
            drop(tab);
            match res {
                Ok(0) if n > 0 => atom_intern(b"eof"),
                Ok(got) => {
                    let data = if binary {
                        bytes_to_new_bin(ctx, &buf[..got])
                    } else {
                        bytes_to_byte_list(ctx, &buf[..got])
                    };
                    pair_term(ctx, b"ok", data)
                }
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_WRITE => {
            let Some(idx) = file_resolve(a) else { return raise_badarg(ctx) };
            let mut data = Vec::new();
            if iolist_flatten(b, &mut data).is_err() {
                return raise_badarg(ctx);
            }
            let mut tab = FILES.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                drop(tab);
                return pair_term(ctx, b"error", atom_intern(b"ebadf"));
            };
            let res = entry.file.write_all(&data);
            drop(tab);
            match res {
                Ok(()) => ok_atom(),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_POSITION => {
            let Some(idx) = file_resolve(a) else { return raise_badarg(ctx) };
            // N | bof | cur | eof | {bof, N} | {cur, N} | {eof, N}
            let seek = |whence: &[u8], n: i64| -> Option<std::io::SeekFrom> {
                match whence {
                    b"bof" => u64::try_from(n).ok().map(std::io::SeekFrom::Start),
                    b"cur" => Some(std::io::SeekFrom::Current(n)),
                    b"eof" => Some(std::io::SeekFrom::End(n)),
                    _ => None,
                }
            };
            let loc = if b & TAG_MASK == TAG_SMALL {
                seek(b"bof", b as i64 >> 3)
            } else if b & TAG_MASK == TAG_ATOM {
                seek(atom_bytes(b), 0)
            } else if b & TAG_MASK == TAG_BOXED && b != 0 {
                unsafe {
                    let p = b as *const u64;
                    if *p == (2 << 8) | KIND_TUPLE
                        && *p.add(1) & TAG_MASK == TAG_ATOM
                        && *p.add(2) & TAG_MASK == TAG_SMALL
                    {
                        seek(atom_bytes(*p.add(1)), *p.add(2) as i64 >> 3)
                    } else {
                        None
                    }
                }
            } else {
                None
            };
            let Some(loc) = loc else { return raise_badarg(ctx) };
            let mut tab = FILES.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                drop(tab);
                return pair_term(ctx, b"error", atom_intern(b"ebadf"));
            };
            let res = entry.file.seek(loc);
            drop(tab);
            match res {
                Ok(pos) => pair_term(ctx, b"ok", ((pos as i64) << 3) as u64 | TAG_SMALL),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_DELETE => {
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            match std::fs::remove_file(&path) {
                Ok(()) => ok_atom(),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_RENAME => {
            let (Ok(from), Ok(to)) = (path_of(a), path_of(b)) else {
                return raise_badarg(ctx);
            };
            match std::fs::rename(&from, &to) {
                Ok(()) => ok_atom(),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_MAKE_DIR => {
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            match std::fs::create_dir(&path) {
                Ok(()) => ok_atom(),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_DEL_DIR => {
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            match std::fs::remove_dir(&path) {
                Ok(()) => ok_atom(),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        F_LIST_DIR => {
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            let rd = match std::fs::read_dir(&path) {
                Ok(rd) => rd,
                Err(e) => return err_tuple(ctx, &e),
            };
            let mut names: Vec<Vec<u8>> = Vec::new();
            for ent in rd {
                match ent {
                    Ok(ent) => names.push(ent.file_name().as_encoded_bytes().to_vec()),
                    Err(e) => return err_tuple(ctx, &e),
                }
            }
            // charlists, list built back-to-front with the acc rooted
            let saved = ctx.roots_head;
            let mut fr = [0u64, 2, NIL, NIL];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            for name in names.iter().rev() {
                fr[3] = utf8_to_codepoint_list(ctx, name);
                let cell = alloc_nursery(ctx, 2);
                unsafe {
                    *cell = fr[3];
                    *cell.add(1) = fr[2];
                }
                fr[2] = cell as u64 | TAG_CONS;
            }
            let list = fr[2];
            ctx.roots_head = saved;
            pair_term(ctx, b"ok", list)
        }
        F_FILE_INFO | F_FILE_INFO2 => {
            use std::os::unix::fs::MetadataExt;
            let Ok(path) = path_of(a) else { return raise_badarg(ctx) };
            // {time, posix} is the only option honored; universal/local
            // answer UTC calendar tuples (local-as-UTC is a documented
            // divergence)
            let mut posix_time = false;
            if op == F_FILE_INFO2 {
                let mut cur = b;
                while cur & TAG_MASK == TAG_CONS {
                    let p = (cur & !TAG_MASK) as *const u64;
                    let o = unsafe { *p };
                    if o & TAG_MASK == TAG_BOXED && o != 0 {
                        unsafe {
                            let t = o as *const u64;
                            if *t == (2 << 8) | KIND_TUPLE
                                && *t.add(1) & TAG_MASK == TAG_ATOM
                                && atom_bytes(*t.add(1)) == b"time"
                                && *t.add(2) & TAG_MASK == TAG_ATOM
                                && atom_bytes(*t.add(2)) == b"posix"
                            {
                                posix_time = true;
                            }
                        }
                    }
                    cur = unsafe { *p.add(1) };
                }
            }
            let md = match std::fs::metadata(&path) {
                Ok(md) => md,
                Err(e) => return err_tuple(ctx, &e),
            };
            let ftype: &[u8] = if md.is_dir() {
                b"directory"
            } else if md.is_file() {
                b"regular"
            } else if md.file_type().is_symlink() {
                b"symlink"
            } else {
                b"other"
            };
            let access: &[u8] = if md.permissions().readonly() {
                b"read"
            } else {
                b"read_write"
            };
            let small = |v: i64| ((v << 3) as u64) | TAG_SMALL;
            let mut time_term = |ctx: &mut ProcCtx, secs: i64| -> u64 {
                if posix_time {
                    small(secs)
                } else {
                    civil_datetime(ctx, secs)
                }
            };
            // root the three time terms across the record alloc
            let saved = ctx.roots_head;
            let mut fr = [0u64, 3, NIL, NIL, NIL];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            fr[2] = time_term(ctx, md.atime());
            fr[3] = time_term(ctx, md.mtime());
            fr[4] = time_term(ctx, md.ctime());
            let p = alloc_nursery(ctx, 15);
            unsafe {
                *p = (14 << 8) | KIND_TUPLE;
                *p.add(1) = atom_intern(b"file_info");
                *p.add(2) = small(md.size() as i64);
                *p.add(3) = atom_intern(ftype);
                *p.add(4) = atom_intern(access);
                *p.add(5) = fr[2];
                *p.add(6) = fr[3];
                *p.add(7) = fr[4];
                *p.add(8) = small((md.mode() & 0o7777) as i64);
                *p.add(9) = small(md.nlink() as i64);
                *p.add(10) = small(0); // major_device
                *p.add(11) = small(0); // minor_device
                *p.add(12) = small(md.ino() as i64 & (i64::MAX >> 3));
                *p.add(13) = small(md.uid() as i64);
                *p.add(14) = small(md.gid() as i64);
            }
            ctx.roots_head = saved;
            pair_term(ctx, b"ok", p as u64)
        }
        F_GET_CWD => match std::env::current_dir() {
            Ok(p) => {
                let bytes = p.as_os_str().as_encoded_bytes().to_vec();
                let l = bytes_to_byte_list(ctx, &bytes);
                pair_term(ctx, b"ok", l)
            }
            Err(e) => err_tuple(ctx, &e),
        },
        F_COPY => {
            let (Ok(from), Ok(to)) = (path_of(a), path_of(b)) else {
                return raise_badarg(ctx);
            };
            match std::fs::copy(&from, &to) {
                Ok(n) => pair_term(ctx, b"ok", ((n as i64) << 3) as u64 | TAG_SMALL),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        _ => raise_badarg(ctx),
    }
}

impl FileTable {
    fn insert(&mut self, e: FileEntry) -> usize {
        match self.free.pop() {
            Some(i) => {
                self.slots[i] = Some(e);
                i
            }
            None => {
                self.slots.push(Some(e));
                self.slots.len() - 1
            }
        }
    }
}

// ---------------------------------------------------------------------------
// gen_tcp / inet (native cut: OTP's inet stack is never compiled)
//
// All syscalls are NONBLOCKING and run on the scheduler thread; WouldBlock
// parks the process (Waiting) after arming a waiter slot + reactor
// registration, and the reactor wakes it via IO_WAKES (see the reactor
// section for the lost-wakeup protocol). All term arguments are converted
// to native values BEFORE any park: a suspended coroutine's Rust locals are
// not GC roots, so term pointers must never be used across a suspend.

fn sock_handle(ctx: &mut ProcCtx, idx: usize) -> u64 {
    let p = alloc_nursery(ctx, 3);
    unsafe {
        *p = (2 << 8) | KIND_TUPLE;
        *p.add(1) = atom_intern(b"mana_socket");
        *p.add(2) = ((idx as u64) << 3) | TAG_SMALL;
    }
    p as u64
}

fn sock_resolve(t: u64) -> Option<usize> {
    if t & TAG_MASK != TAG_BOXED || t == 0 {
        return None;
    }
    unsafe {
        let p = t as *const u64;
        if *p != (2 << 8) | KIND_TUPLE {
            return None;
        }
        let tag = *p.add(1);
        if tag & TAG_MASK != TAG_ATOM || atom_bytes(tag) != b"mana_socket" {
            return None;
        }
        let idx = *p.add(2);
        if idx & TAG_MASK != TAG_SMALL {
            return None;
        }
        Some((idx as i64 >> 3) as usize)
    }
}

/// Options both connect/listen accept; active semantics land in Phase D.
#[derive(Clone, Copy)]
struct TcpOpts {
    binary: bool,
    active: ActiveMode,
}

fn parse_tcp_opts(mut cur: u64) -> Result<TcpOpts, ()> {
    let mut o = TcpOpts { binary: false, active: ActiveMode::Always };
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK == TAG_ATOM {
            match atom_bytes(h) {
                b"binary" => o.binary = true,
                b"list" => o.binary = false,
                _ => {} // reuseaddr etc. accepted as bare atoms too
            }
        } else if h & TAG_MASK == TAG_BOXED && h != 0 {
            unsafe {
                let t = h as *const u64;
                if *t == (2 << 8) | KIND_TUPLE && *t.add(1) & TAG_MASK == TAG_ATOM {
                    let v = *t.add(2);
                    match atom_bytes(*t.add(1)) {
                        b"mode" => {
                            if v & TAG_MASK == TAG_ATOM {
                                match atom_bytes(v) {
                                    b"binary" => o.binary = true,
                                    b"list" => o.binary = false,
                                    _ => return Err(()),
                                }
                            }
                        }
                        b"active" => {
                            o.active = if v & TAG_MASK == TAG_ATOM {
                                match atom_bytes(v) {
                                    b"false" => ActiveMode::Passive,
                                    b"once" => ActiveMode::Once,
                                    b"true" => ActiveMode::Always,
                                    _ => return Err(()),
                                }
                            } else {
                                return Err(());
                            }
                        }
                        b"packet" => {
                            // raw/0 only — TODO(packet)
                            let raw = (v & TAG_MASK == TAG_SMALL && v >> 3 == 0)
                                || (v & TAG_MASK == TAG_ATOM
                                    && matches!(atom_bytes(v), b"raw" | b"0"));
                            if !raw {
                                return Err(());
                            }
                        }
                        // reuseaddr/backlog/nodelay/mode etc: accepted
                        _ => {}
                    }
                }
            }
        }
        cur = unsafe { *p.add(1) };
    }
    Ok(o)
}

/// {A,B,C,D} tuple | binary | charlist | atom 'localhost' → IpAddr.
fn ip_of(t: u64) -> Result<std::net::IpAddr, ()> {
    use std::net::{IpAddr, Ipv4Addr};
    if t & TAG_MASK == TAG_BOXED && t != 0 {
        unsafe {
            let p = t as *const u64;
            if *p == (4 << 8) | KIND_TUPLE {
                let mut o = [0u8; 4];
                for (i, b) in o.iter_mut().enumerate() {
                    let v = *p.add(1 + i);
                    if v & TAG_MASK != TAG_SMALL {
                        return Err(());
                    }
                    let v = v as i64 >> 3;
                    if !(0..=255).contains(&v) {
                        return Err(());
                    }
                    *b = v as u8;
                }
                return Ok(IpAddr::V4(Ipv4Addr::new(o[0], o[1], o[2], o[3])));
            }
        }
    }
    // hostname as chardata/atom: numeric or localhost only stays
    // nonblocking; general getaddrinfo blocks (documented)
    let mut bytes = Vec::new();
    if t & TAG_MASK == TAG_ATOM {
        bytes.extend_from_slice(atom_bytes(t));
    } else if chardata_flatten(t, &mut bytes).is_err() {
        return Err(());
    }
    let s = std::str::from_utf8(&bytes).map_err(|_| ())?;
    if s == "localhost" {
        return Ok(IpAddr::V4(Ipv4Addr::LOCALHOST));
    }
    s.parse().map_err(|_| ())
}

fn timeout_deadline(t: u64) -> Result<Option<std::time::Instant>, ()> {
    if t & TAG_MASK == TAG_ATOM && atom_bytes(t) == b"infinity" {
        return Ok(None);
    }
    if t & TAG_MASK == TAG_SMALL && (t as i64 >> 3) >= 0 {
        let ms = (t as i64 >> 3) as u64;
        return Ok(Some(std::time::Instant::now() + std::time::Duration::from_millis(ms)));
    }
    Err(())
}

fn closed_err(ctx: &mut ProcCtx) -> u64 {
    pair_term(ctx, b"error", atom_intern(b"closed"))
}

/// Arm the read/write waiter + registration, then park until the reactor
/// (or the deadline via idle_wait) wakes us. Returns false on timeout.
/// The SOCKETS lock must NOT be held by the caller.
fn park_on_socket(
    ctx: &mut ProcCtx,
    idx: usize,
    want_read: bool,
    deadline: Option<std::time::Instant>,
) -> bool {
    let pid = ctx.current;
    {
        let mut tab = SOCKETS.lock().unwrap();
        let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
            return true; // closed under us: let the caller's retry observe it
        };
        if want_read {
            entry.read_waiter = Some(pid);
        } else {
            entry.write_waiter = Some(pid);
        }
        if !entry.registered {
            entry.registered = true;
            REACTOR_CMDS.push(idx);
        }
    }
    ensure_reactor(ctx.global);
    reactor_wake();
    if let Some(dl) = deadline {
        if std::time::Instant::now() >= dl {
            clear_waiter(idx, pid, want_read);
            return false;
        }
    }
    {
        let p = cur_proc(ctx);
        *p.state.lock() = PState::Waiting(deadline);
    }
    suspend_current(ctx);
    if let Some(dl) = deadline {
        if std::time::Instant::now() >= dl {
            clear_waiter(idx, pid, want_read);
            return false;
        }
    }
    true
}

fn clear_waiter(idx: usize, pid: usize, want_read: bool) {
    let mut tab = SOCKETS.lock().unwrap();
    if let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) {
        if want_read && entry.read_waiter == Some(pid) {
            entry.read_waiter = None;
        }
        if !want_read && entry.write_waiter == Some(pid) {
            entry.write_waiter = None;
        }
    }
}

// tcp op codes (codegen compile dispatch mirrors these)
pub const T_CONNECT: u64 = 0;
pub const T_LISTEN: u64 = 1;
pub const T_ACCEPT: u64 = 2;
pub const T_RECV: u64 = 3;
/// file:sendfile/5 (RawFile, Socket, Offset, Bytes, _Opts) — read-at +
/// parking send loop; Bytes == 0 streams to EOF. Returns {ok, Sent}.
#[no_mangle]
pub extern "C" fn mana_rt_sendfile(
    ctx: *mut ProcCtx,
    fd_t: u64,
    sock: u64,
    off_t: u64,
    len_t: u64,
    _opts: u64,
) -> u64 {
    use std::os::unix::fs::FileExt;
    let ctx = unsafe { &mut *ctx };
    let Some(fidx) = file_resolve(fd_t) else { return raise_badarg(ctx) };
    let Some(sidx) = sock_resolve(sock) else { return raise_badarg(ctx) };
    if off_t & TAG_MASK != TAG_SMALL
        || len_t & TAG_MASK != TAG_SMALL
        || (off_t as i64 >> 3) < 0
        || (len_t as i64 >> 3) < 0
    {
        return raise_badarg(ctx);
    }
    let base = (off_t as i64 >> 3) as u64;
    let want = (len_t as i64 >> 3) as u64; // 0 = to EOF
    let mut sent = 0u64;
    let mut buf = vec![0u8; 64 * 1024];
    loop {
        if want > 0 && sent == want {
            break;
        }
        let cap = if want > 0 {
            std::cmp::min(buf.len() as u64, want - sent) as usize
        } else {
            buf.len()
        };
        let n = {
            let tab = FILES.lock().unwrap();
            let Some(entry) = tab.slots.get(fidx).and_then(|s| s.as_ref()) else {
                return pair_term(ctx, b"error", atom_intern(b"ebadf"));
            };
            match entry.file.read_at(&mut buf[..cap], base + sent) {
                Ok(n) => n,
                Err(e) => {
                    drop(tab);
                    return err_tuple(ctx, &e);
                }
            }
        };
        if n == 0 {
            break; // EOF: {ok, actually_sent}, like BEAM
        }
        // socket send with partial-write parking (the T_SEND discipline)
        let mut off = 0usize;
        while off < n {
            let step: Result<Option<usize>, std::io::Error> = {
                let mut tab = SOCKETS.lock().unwrap();
                let Some(entry) = tab.slots.get_mut(sidx).and_then(|s| s.as_mut()) else {
                    drop(tab);
                    return closed_err(ctx);
                };
                let SockSource::Stream(st) = &mut entry.source else {
                    drop(tab);
                    return raise_badarg(ctx);
                };
                match st.write(&buf[off..n]) {
                    Ok(k) => {
                        entry.send_oct += k as u64;
                        Ok(Some(k))
                    }
                    Err(e)
                        if e.kind() == std::io::ErrorKind::WouldBlock
                            || e.kind() == std::io::ErrorKind::Interrupted =>
                    {
                        Ok(None)
                    }
                    Err(e) => Err(e),
                }
            };
            match step {
                Ok(Some(k)) => off += k,
                Ok(None) => {
                    park_on_socket(ctx, sidx, false, None);
                }
                Err(e) => {
                    clear_waiter(sidx, ctx.current, false);
                    if e.kind() == std::io::ErrorKind::BrokenPipe
                        || e.kind() == std::io::ErrorKind::ConnectionReset
                    {
                        return closed_err(ctx);
                    }
                    return err_tuple(ctx, &e);
                }
            }
        }
        clear_waiter(sidx, ctx.current, false);
        sent += n as u64;
    }
    let t = alloc_nursery(ctx, 3);
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = atom_intern(b"ok");
        *t.add(2) = ((sent << 3) as u64) | TAG_SMALL;
    }
    t as u64
}

pub const T_SEND: u64 = 4;
pub const T_CLOSE: u64 = 5;
pub const T_SHUTDOWN: u64 = 6;
pub const T_SETOPTS: u64 = 7;
pub const T_PEERNAME: u64 = 8;
pub const T_SOCKNAME: u64 = 9;
pub const T_PORT: u64 = 10;
pub const T_CONTROLLING: u64 = 11;
pub const T_GETSTAT: u64 = 12;
pub const T_GETOPTS: u64 = 13;

fn addr_tuple(ctx: &mut ProcCtx, addr: std::net::SocketAddr) -> u64 {
    let small = |v: i64| ((v << 3) as u64) | TAG_SMALL;
    let ip = match addr.ip() {
        std::net::IpAddr::V4(v4) => v4.octets(),
        std::net::IpAddr::V6(_) => [0, 0, 0, 0], // TODO(ipv6)
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let a = alloc_nursery(ctx, 5);
    unsafe {
        *a = (4 << 8) | KIND_TUPLE;
        for (i, o) in ip.iter().enumerate() {
            *a.add(1 + i) = small(*o as i64);
        }
    }
    fr[2] = a as u64;
    let pair = alloc_nursery(ctx, 3);
    unsafe {
        *pair = (2 << 8) | KIND_TUPLE;
        *pair.add(1) = fr[2];
        *pair.add(2) = small(addr.port() as i64);
    }
    ctx.roots_head = saved;
    pair as u64
}

#[no_mangle]
pub extern "C" fn mana_rt_tcp(
    ctx: *mut ProcCtx,
    op: u64,
    a: u64,
    b: u64,
    c: u64,
    d: u64,
) -> u64 {
    use std::io::{Read, Write};
    let ctx = unsafe { &mut *ctx };
    match op {
        T_CONNECT => {
            // a=addr, b=port, c=opts, d=timeout
            let Ok(ip) = ip_of(a) else { return raise_badarg(ctx) };
            if b & TAG_MASK != TAG_SMALL {
                return raise_badarg(ctx);
            }
            let port = (b as i64 >> 3) as u16;
            let Ok(opts) = parse_tcp_opts(c) else { return raise_badarg(ctx) };
            let Ok(deadline) = timeout_deadline(d) else { return raise_badarg(ctx) };
            let addr = std::net::SocketAddr::new(ip, port);
            let stream = match mio::net::TcpStream::connect(addr) {
                Ok(s) => s,
                Err(e) => return err_tuple(ctx, &e),
            };
            let idx = SOCKETS.lock().unwrap().insert(SockEntry {
                source: SockSource::Stream(stream),
                read_waiter: None,
                write_waiter: None,
                registered: false,
                owner: ctx.current,
                active: opts.active,
                binary: opts.binary,
                rbuf: Vec::new(),
                recv_oct: 0,
                send_oct: 0,
            });
            // wait for writability, then check SO_ERROR
            loop {
                {
                    let mut tab = SOCKETS.lock().unwrap();
                    let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut())
                    else {
                        drop(tab);
                        return closed_err(ctx);
                    };
                    let SockSource::Stream(s) = &mut entry.source else {
                        drop(tab);
                        return raise_badarg(ctx);
                    };
                    match s.peer_addr() {
                        Ok(_) => {
                            drop(tab);
                            ensure_registered_active(ctx, idx);
                            let h = sock_handle(ctx, idx);
                            return pair_term(ctx, b"ok", h);
                        }
                        Err(e)
                            if e.kind() == std::io::ErrorKind::NotConnected
                                || e.raw_os_error() == Some(libc_einprogress()) =>
                        {
                            // a refused connect also reports NotConnected
                            // from peer_addr — the verdict lives in SO_ERROR
                            if let Ok(Some(err)) = s.take_error() {
                                tab.slots[idx] = None;
                                tab.free.push(idx);
                                drop(tab);
                                return pair_term(
                                    ctx,
                                    b"error",
                                    if err.raw_os_error() == Some(111) {
                                        atom_intern(b"econnrefused")
                                    } else {
                                        posix_atom(&err)
                                    },
                                );
                            }
                        }
                        Err(_) => {
                            let e = s
                                .take_error()
                                .ok()
                                .flatten()
                                .unwrap_or_else(|| {
                                    std::io::Error::from(std::io::ErrorKind::Other)
                                });
                            tab.slots[idx] = None;
                            tab.free.push(idx);
                            drop(tab);
                            return pair_term(
                                ctx,
                                b"error",
                                if e.raw_os_error() == Some(111) {
                                    atom_intern(b"econnrefused")
                                } else {
                                    posix_atom(&e)
                                },
                            );
                        }
                    }
                }
                if !park_on_socket(ctx, idx, false, deadline) {
                    let mut tab = SOCKETS.lock().unwrap();
                    tab.slots[idx] = None;
                    tab.free.push(idx);
                    drop(tab);
                    return pair_term(ctx, b"error", atom_intern(b"timeout"));
                }
            }
        }
        T_LISTEN => {
            // a=port, b=opts
            if a & TAG_MASK != TAG_SMALL {
                return raise_badarg(ctx);
            }
            let port = (a as i64 >> 3) as u16;
            let Ok(opts) = parse_tcp_opts(b) else { return raise_badarg(ctx) };
            let addr = std::net::SocketAddr::new(
                std::net::IpAddr::V4(std::net::Ipv4Addr::UNSPECIFIED),
                port,
            );
            match mio::net::TcpListener::bind(addr) {
                Ok(l) => {
                    let idx = SOCKETS.lock().unwrap().insert(SockEntry {
                        source: SockSource::Listener(l),
                        read_waiter: None,
                        write_waiter: None,
                        registered: false,
                        owner: ctx.current,
                        active: opts.active,
                        binary: opts.binary,
                        rbuf: Vec::new(),
                        recv_oct: 0,
                        send_oct: 0,
                    });
                    let h = sock_handle(ctx, idx);
                    pair_term(ctx, b"ok", h)
                }
                Err(e) => err_tuple(ctx, &e),
            }
        }
        T_ACCEPT => {
            // a=lsock, b=timeout
            let Some(idx) = sock_resolve(a) else { return raise_badarg(ctx) };
            let Ok(deadline) = timeout_deadline(b) else { return raise_badarg(ctx) };
            loop {
                let accepted = {
                    let mut tab = SOCKETS.lock().unwrap();
                    let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut())
                    else {
                        drop(tab);
                        return closed_err(ctx);
                    };
                    let opts = TcpOpts { binary: entry.binary, active: entry.active };
                    let SockSource::Listener(l) = &mut entry.source else {
                        drop(tab);
                        return raise_badarg(ctx);
                    };
                    match l.accept() {
                        Ok((stream, _)) => {
                            let owner = ctx.current;
                            let i = tab.insert(SockEntry {
                                source: SockSource::Stream(stream),
                                read_waiter: None,
                                write_waiter: None,
                                registered: false,
                                owner,
                                active: opts.active,
                                binary: opts.binary,
                                rbuf: Vec::new(),
                                recv_oct: 0,
                                send_oct: 0,
                            });
                            Some(Ok(i))
                        }
                        Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => None,
                        Err(e) => Some(Err(e)),
                    }
                };
                match accepted {
                    Some(Ok(i)) => {
                        clear_waiter(idx, ctx.current, true);
                        ensure_registered_active(ctx, i);
                        let h = sock_handle(ctx, i);
                        return pair_term(ctx, b"ok", h);
                    }
                    Some(Err(e)) => {
                        clear_waiter(idx, ctx.current, true);
                        return err_tuple(ctx, &e);
                    }
                    None => {
                        if !park_on_socket(ctx, idx, true, deadline) {
                            return pair_term(ctx, b"error", atom_intern(b"timeout"));
                        }
                    }
                }
            }
        }
        T_RECV => {
            // a=sock, b=len, c=timeout
            let Some(idx) = sock_resolve(a) else { return raise_badarg(ctx) };
            if b & TAG_MASK != TAG_SMALL || (b as i64 >> 3) < 0 {
                return raise_badarg(ctx);
            }
            let want = (b as i64 >> 3) as usize;
            let Ok(deadline) = timeout_deadline(c) else { return raise_badarg(ctx) };
            let mut chunk = vec![0u8; 65536];
            loop {
                enum Step {
                    Done(Vec<u8>, bool),
                    Closed(bool),
                    Park,
                    Err(std::io::Error),
                }
                let step = {
                    let mut tab = SOCKETS.lock().unwrap();
                    let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut())
                    else {
                        drop(tab);
                        return closed_err(ctx);
                    };
                    let binary = entry.binary;
                    // enough buffered already?
                    if want > 0 && entry.rbuf.len() >= want {
                        let rest = entry.rbuf.split_off(want);
                        let data = std::mem::replace(&mut entry.rbuf, rest);
                        Step::Done(data, binary)
                    } else if want == 0 && !entry.rbuf.is_empty() {
                        let data = std::mem::take(&mut entry.rbuf);
                        Step::Done(data, binary)
                    } else {
                        let SockSource::Stream(s) = &mut entry.source else {
                            drop(tab);
                            return raise_badarg(ctx);
                        };
                        match s.read(&mut chunk) {
                            Ok(0) => Step::Closed(binary),
                            Ok(k) => {
                                entry.recv_oct += k as u64;
                                entry.rbuf.extend_from_slice(&chunk[..k]);
                                if want == 0 || entry.rbuf.len() >= want {
                                    let take = if want == 0 {
                                        entry.rbuf.len()
                                    } else {
                                        want
                                    };
                                    let rest = entry.rbuf.split_off(take);
                                    let data =
                                        std::mem::replace(&mut entry.rbuf, rest);
                                    Step::Done(data, binary)
                                } else {
                                    Step::Park
                                }
                            }
                            Err(e)
                                if e.kind() == std::io::ErrorKind::WouldBlock
                                    || e.kind()
                                        == std::io::ErrorKind::Interrupted =>
                            {
                                Step::Park
                            }
                            Err(e) => Step::Err(e),
                        }
                    }
                };
                match step {
                    Step::Done(data, binary) => {
                        clear_waiter(idx, ctx.current, true);
                        let term = if binary {
                            bytes_to_new_bin(ctx, &data)
                        } else {
                            bytes_to_byte_list(ctx, &data)
                        };
                        return pair_term(ctx, b"ok", term);
                    }
                    Step::Closed(_) => {
                        clear_waiter(idx, ctx.current, true);
                        return closed_err(ctx);
                    }
                    Step::Err(e) => {
                        clear_waiter(idx, ctx.current, true);
                        return err_tuple(ctx, &e);
                    }
                    Step::Park => {
                        if !park_on_socket(ctx, idx, true, deadline) {
                            return pair_term(ctx, b"error", atom_intern(b"timeout"));
                        }
                    }
                }
            }
        }
        T_SEND => {
            // a=sock, b=iodata
            let Some(idx) = sock_resolve(a) else { return raise_badarg(ctx) };
            let mut data = Vec::new();
            if iolist_flatten(b, &mut data).is_err() {
                return raise_badarg(ctx);
            }
            let mut off = 0usize;
            loop {
                let step: Result<Option<usize>, std::io::Error> = {
                    let mut tab = SOCKETS.lock().unwrap();
                    let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut())
                    else {
                        drop(tab);
                        return closed_err(ctx);
                    };
                    let SockSource::Stream(s) = &mut entry.source else {
                        drop(tab);
                        return raise_badarg(ctx);
                    };
                    match s.write(&data[off..]) {
                        Ok(k) => {
                            entry.send_oct += k as u64;
                            Ok(Some(k))
                        }
                        Err(e)
                            if e.kind() == std::io::ErrorKind::WouldBlock
                                || e.kind() == std::io::ErrorKind::Interrupted =>
                        {
                            Ok(None)
                        }
                        Err(e) => Err(e),
                    }
                };
                match step {
                    Ok(Some(k)) => {
                        off += k;
                        if off == data.len() {
                            clear_waiter(idx, ctx.current, false);
                            return atom_intern(b"ok");
                        }
                    }
                    Ok(None) => {
                        park_on_socket(ctx, idx, false, None);
                    }
                    Err(e) => {
                        clear_waiter(idx, ctx.current, false);
                        if e.kind() == std::io::ErrorKind::BrokenPipe
                            || e.kind() == std::io::ErrorKind::ConnectionReset
                        {
                            return closed_err(ctx);
                        }
                        return err_tuple(ctx, &e);
                    }
                }
            }
        }
        T_CLOSE => {
            let Some(idx) = sock_resolve(a) else { return raise_badarg(ctx) };
            let entry = {
                let mut tab = SOCKETS.lock().unwrap();
                let e = tab.slots.get_mut(idx).and_then(|s| s.take());
                if e.is_some() {
                    tab.free.push(idx);
                }
                e
            };
            if let Some(e) = entry {
                // waiters retry, observe the missing entry → {error, closed}
                if let Some(pid) = e.read_waiter {
                    IO_WAKES.push((pid, idx, true));
                }
                if let Some(pid) = e.write_waiter {
                    IO_WAKES.push((pid, idx, false));
                }
                for s in 0..ctx.global.n_scheds {
                    wake_sched(ctx.global, s);
                }
                // dropping the source closes the fd (epoll auto-deregisters)
            }
            atom_intern(b"ok")
        }
        T_SHUTDOWN => {
            let Some(idx) = sock_resolve(a) else { return raise_badarg(ctx) };
            let how = if b & TAG_MASK == TAG_ATOM {
                match atom_bytes(b) {
                    b"read" => std::net::Shutdown::Read,
                    b"write" => std::net::Shutdown::Write,
                    b"read_write" => std::net::Shutdown::Both,
                    _ => return raise_badarg(ctx),
                }
            } else {
                return raise_badarg(ctx);
            };
            let mut tab = SOCKETS.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                drop(tab);
                return closed_err(ctx);
            };
            let SockSource::Stream(s) = &mut entry.source else {
                drop(tab);
                return raise_badarg(ctx);
            };
            let res = s.shutdown(how);
            drop(tab);
            match res {
                Ok(()) => atom_intern(b"ok"),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        T_SETOPTS => {
            let Some(idx) = sock_resolve(a) else { return raise_badarg(ctx) };
            let Ok(opts) = parse_tcp_opts(b) else { return raise_badarg(ctx) };
            let has_mode_opt = |mut cur: u64, name: &[u8]| -> bool {
                while cur & TAG_MASK == TAG_CONS {
                    let p = (cur & !TAG_MASK) as *const u64;
                    let h = unsafe { *p };
                    if h & TAG_MASK == TAG_ATOM && atom_bytes(h) == name {
                        return true;
                    }
                    if h & TAG_MASK == TAG_BOXED && h != 0 {
                        unsafe {
                            let t = h as *const u64;
                            if *t == (2 << 8) | KIND_TUPLE
                                && *t.add(1) & TAG_MASK == TAG_ATOM
                                && atom_bytes(*t.add(1)) == name
                            {
                                return true;
                            }
                        }
                    }
                    cur = unsafe { *p.add(1) };
                }
                false
            };
            let mut tab = SOCKETS.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                drop(tab);
                return closed_err(ctx);
            };
            let mut activated = false;
            if has_mode_opt(b, b"active") {
                let was = entry.active;
                entry.active = opts.active;
                activated = was == ActiveMode::Passive && opts.active != ActiveMode::Passive;
            }
            if has_mode_opt(b, b"binary") {
                entry.binary = true;
            }
            if has_mode_opt(b, b"list") {
                entry.binary = false;
            }
            drop(tab);
            if activated {
                // deliver anything already buffered (or an edge the kernel
                // already reported) — the pump no-ops if the socket is quiet
                ensure_registered_active(ctx, idx);
                IO_ACTIVE.push(idx);
                for s in 0..ctx.global.n_scheds {
                    wake_sched(ctx.global, s);
                }
            }
            atom_intern(b"ok")
        }
        T_CONTROLLING => {
            let Some(idx) = sock_resolve(a) else { return raise_badarg(ctx) };
            if b & 0xF != PID_TAG4 {
                return raise_badarg(ctx);
            }
            let pid = (b >> 4) as usize;
            let mut tab = SOCKETS.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                drop(tab);
                return closed_err(ctx);
            };
            entry.owner = pid;
            atom_intern(b"ok")
        }
        T_PEERNAME | T_SOCKNAME | T_PORT => {
            let Some(idx) = sock_resolve(a) else { return raise_badarg(ctx) };
            let addr = {
                let mut tab = SOCKETS.lock().unwrap();
                let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut())
                else {
                    drop(tab);
                    return closed_err(ctx);
                };
                match (&entry.source, op) {
                    (SockSource::Stream(s), T_PEERNAME) => s.peer_addr(),
                    (SockSource::Stream(s), _) => s.local_addr(),
                    (SockSource::Listener(_), T_PEERNAME) => {
                        drop(tab);
                        return raise_badarg(ctx);
                    }
                    (SockSource::Listener(l), _) => l.local_addr(),
                }
            };
            match addr {
                Ok(sa) => {
                    if op == T_PORT {
                        let small = ((sa.port() as i64) << 3) as u64 | TAG_SMALL;
                        pair_term(ctx, b"ok", small)
                    } else {
                        let t = addr_tuple(ctx, sa);
                        pair_term(ctx, b"ok", t)
                    }
                }
                Err(e) => err_tuple(ctx, &e),
            }
        }
        T_GETSTAT => {
            let Some(idx) = sock_resolve(a) else { return raise_badarg(ctx) };
            let (recv_oct, send_oct) = {
                let tab = SOCKETS.lock().unwrap();
                let Some(entry) = tab.slots.get(idx).and_then(|s| s.as_ref()) else {
                    drop(tab);
                    return closed_err(ctx);
                };
                (entry.recv_oct, entry.send_oct)
            };
            let stats: [(&[u8], u64); 8] = [
                (b"recv_oct", recv_oct),
                (b"recv_cnt", 0),
                (b"recv_max", 0),
                (b"recv_avg", 0),
                (b"send_oct", send_oct),
                (b"send_cnt", 0),
                (b"send_max", 0),
                (b"send_avg", 0),
            ];
            let saved = ctx.roots_head;
            let mut fr = [0u64, 2, NIL, NIL];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            for (name, v) in stats.iter().rev() {
                let t = alloc_nursery(ctx, 3);
                unsafe {
                    *t = (2 << 8) | KIND_TUPLE;
                    *t.add(1) = atom_intern(name);
                    *t.add(2) = ((*v as i64) << 3) as u64 | TAG_SMALL;
                }
                fr[3] = t as u64;
                let cell = alloc_nursery(ctx, 2);
                unsafe {
                    *cell = fr[3];
                    *cell.add(1) = fr[2];
                }
                fr[2] = cell as u64 | TAG_CONS;
            }
            let list = fr[2];
            ctx.roots_head = saved;
            pair_term(ctx, b"ok", list)
        }
        T_GETOPTS => {
            let Some(idx) = sock_resolve(a) else { return raise_badarg(ctx) };
            let (active, binary) = {
                let tab = SOCKETS.lock().unwrap();
                let Some(entry) = tab.slots.get(idx).and_then(|s| s.as_ref()) else {
                    drop(tab);
                    return closed_err(ctx);
                };
                (entry.active, entry.binary)
            };
            // answer the asked-for option names we model; skip unknowns
            let mut wanted: Vec<&'static [u8]> = Vec::new();
            let mut cur = b;
            while cur & TAG_MASK == TAG_CONS {
                let p = (cur & !TAG_MASK) as *const u64;
                let o = unsafe { *p };
                if o & TAG_MASK == TAG_ATOM {
                    match atom_bytes(o) {
                        b"active" => wanted.push(b"active"),
                        b"mode" => wanted.push(b"mode"),
                        b"packet" => wanted.push(b"packet"),
                        b"nodelay" => wanted.push(b"nodelay"),
                        b"keepalive" => wanted.push(b"keepalive"),
                        b"reuseaddr" => wanted.push(b"reuseaddr"),
                        _ => {}
                    }
                }
                cur = unsafe { *p.add(1) };
            }
            let saved = ctx.roots_head;
            let mut fr = [0u64, 2, NIL, NIL];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            for name in wanted.iter().rev() {
                let val = match *name {
                    b"active" => match active {
                        ActiveMode::Passive => known().false_a,
                        ActiveMode::Once => atom_intern(b"once"),
                        ActiveMode::Always => known().true_a,
                    },
                    b"mode" => {
                        if binary {
                            atom_intern(b"binary")
                        } else {
                            atom_intern(b"list")
                        }
                    }
                    b"packet" => TAG_SMALL, // small 0
                    _ => known().true_a, // nodelay/keepalive/reuseaddr
                };
                let t = alloc_nursery(ctx, 3);
                unsafe {
                    *t = (2 << 8) | KIND_TUPLE;
                    *t.add(1) = atom_intern(name);
                    *t.add(2) = val;
                }
                fr[3] = t as u64;
                let cell = alloc_nursery(ctx, 2);
                unsafe {
                    *cell = fr[3];
                    *cell.add(1) = fr[2];
                }
                fr[2] = cell as u64 | TAG_CONS;
            }
            let list = fr[2];
            ctx.roots_head = saved;
            pair_term(ctx, b"ok", list)
        }
        _ => raise_badarg(ctx),
    }
}

fn libc_einprogress() -> i32 {
    115 // linux EINPROGRESS
}

// ---- active mode ({active, once | true}) ----
//
// The reactor never reads sockets: on a readable event for an active socket
// with no parked reader it enqueues the index here; a scheduler drains at
// its loop top, performs the nonblocking reads, and delivers real
// {tcp, Sock, Data} / {tcp_closed, Sock} messages to the owner (built in
// the shared old space — push_and_wake requires shared-safe terms).
static IO_ACTIVE: SegQueue<usize> = SegQueue::new();

fn shared_bin(ctx: &mut ProcCtx, bytes: &[u8]) -> u64 {
    let words = 1 + bytes.len().div_ceil(8);
    let p = alloc_shared(ctx, words);
    unsafe {
        *p = ((bytes.len() as u64) << 8) | KIND_BIN;
        if words > 1 {
            *p.add(words - 1) = 0; // zero the padding tail word
        }
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), p.add(1) as *mut u8, bytes.len());
    }
    p as u64
}

fn shared_byte_list(ctx: &mut ProcCtx, bytes: &[u8]) -> u64 {
    let mut tail = NIL;
    for &b in bytes.iter().rev() {
        let cell = alloc_shared(ctx, 2);
        unsafe {
            *cell = ((b as u64) << 3) | TAG_SMALL;
            *cell.add(1) = tail;
        }
        tail = cell as u64 | TAG_CONS;
    }
    tail
}

fn shared_sock_handle(ctx: &mut ProcCtx, idx: usize) -> u64 {
    shared_tuple(
        ctx,
        &[atom_intern(b"mana_socket"), ((idx as u64) << 3) | TAG_SMALL],
    )
}

/// Register an active socket with the reactor if it isn't yet (sockets that
/// never park would otherwise never get events).
fn ensure_registered_active(ctx: &mut ProcCtx, idx: usize) {
    let mut need = false;
    {
        let mut tab = SOCKETS.lock().unwrap();
        if let Some(e) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) {
            if e.active != ActiveMode::Passive {
                if !e.registered {
                    e.registered = true;
                    need = true;
                }
            }
        }
    }
    if need {
        REACTOR_CMDS.push(idx);
        ensure_reactor(ctx.global);
        reactor_wake();
    }
}

/// Drain pending active-mode sockets (scheduler loop top, a safepoint).
fn drain_io_active(ctx: &mut ProcCtx) {
    let n = IO_ACTIVE.len();
    for _ in 0..n {
        let Some(idx) = IO_ACTIVE.pop() else { break };
        active_pump(ctx, idx);
    }
}

fn active_pump(ctx: &mut ProcCtx, idx: usize) {
    use std::io::Read;
    let mut chunk = vec![0u8; 65536];
    loop {
        enum Ev {
            Data(Vec<u8>, usize, bool, bool), // bytes, owner, binary, once
            Closed(usize),
            Quiet,
        }
        // read + state transitions under the lock; deliver outside it
        // (push_and_wake takes state locks — never nest under SOCKETS)
        let ev = {
            let mut tab = SOCKETS.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                return;
            };
            if entry.active == ActiveMode::Passive {
                return; // deactivated (or tcp_closed already sent)
            }
            let owner = entry.owner;
            let binary = entry.binary;
            let once = entry.active == ActiveMode::Once;
            if !entry.rbuf.is_empty() {
                let data = std::mem::take(&mut entry.rbuf);
                if once {
                    entry.active = ActiveMode::Passive;
                }
                Ev::Data(data, owner, binary, once)
            } else {
                let SockSource::Stream(s) = &mut entry.source else {
                    return; // listeners have no active data
                };
                match s.read(&mut chunk) {
                    Ok(0) => {
                        entry.active = ActiveMode::Passive; // tcp_closed once
                        Ev::Closed(owner)
                    }
                    Ok(k) => {
                        entry.recv_oct += k as u64;
                        if once {
                            entry.active = ActiveMode::Passive;
                        }
                        Ev::Data(chunk[..k].to_vec(), owner, binary, once)
                    }
                    Err(e)
                        if e.kind() == std::io::ErrorKind::WouldBlock
                            || e.kind() == std::io::ErrorKind::Interrupted =>
                    {
                        Ev::Quiet
                    }
                    Err(_) => {
                        entry.active = ActiveMode::Passive;
                        Ev::Closed(owner)
                    }
                }
            }
        };
        match ev {
            Ev::Data(bytes, owner, binary, once) => {
                let handle = shared_sock_handle(ctx, idx);
                let payload = if binary {
                    shared_bin(ctx, &bytes)
                } else {
                    shared_byte_list(ctx, &bytes)
                };
                let msg = shared_tuple(ctx, &[atom_intern(b"tcp"), handle, payload]);
                push_and_wake(ctx, owner, msg);
                if once {
                    return;
                }
            }
            Ev::Closed(owner) => {
                let handle = shared_sock_handle(ctx, idx);
                let msg = shared_tuple(ctx, &[atom_intern(b"tcp_closed"), handle]);
                push_and_wake(ctx, owner, msg);
                return;
            }
            Ev::Quiet => return,
        }
    }
}

// ---------------------------------------------------------------------------
// erlang:decode_packet/3 — http_bin/httph_bin only (Bandit's HTTP/1 parser).
// Stateless per call, mirroring erts packet_parser shapes; the
// Conf.DecodePacket conformance program pins every shape against BEAM.

/// erts' known-header table: atom text + the index reported in the
/// http_header tuple's second element.
const HTTP_FIELDS: &[&str] = &[
    "Cache-Control",
    "Connection",
    "Date",
    "Pragma",
    "Transfer-Encoding",
    "Upgrade",
    "Via",
    "Accept",
    "Accept-Charset",
    "Accept-Encoding",
    "Accept-Language",
    "Authorization",
    "From",
    "Host",
    "If-Modified-Since",
    "If-Match",
    "If-None-Match",
    "If-Range",
    "If-Unmodified-Since",
    "Max-Forwards",
    "Proxy-Authorization",
    "Range",
    "Referer",
    "User-Agent",
    "Age",
    "Location",
    "Proxy-Authenticate",
    "Public",
    "Retry-After",
    "Server",
    "Vary",
    "Warning",
    "Www-Authenticate",
    "Allow",
    "Content-Base",
    "Content-Encoding",
    "Content-Language",
    "Content-Length",
    "Content-Location",
    "Content-Md5",
    "Content-Range",
    "Content-Type",
    "Etag",
    "Expires",
    "Last-Modified",
    "Accept-Ranges",
    "Set-Cookie",
    "Set-Cookie2",
    "X-Forwarded-For",
    "Cookie",
    "Keep-Alive",
    "Proxy-Connection",
];

const HTTP_METHODS: &[&str] = &["OPTIONS", "GET", "HEAD", "POST", "PUT", "DELETE", "TRACE"];

/// Canonical-case a header name the way erts does: capitalize the first
/// letter of every dash-separated token, lowercase the rest.
fn canonical_field(name: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(name.len());
    let mut start_of_token = true;
    for &b in name {
        if b == b'-' {
            out.push(b'-');
            start_of_token = true;
        } else if start_of_token {
            out.push(b.to_ascii_uppercase());
            start_of_token = false;
        } else {
            out.push(b.to_ascii_lowercase());
        }
    }
    out
}

fn small_of(v: i64) -> u64 {
    ((v << 3) as u64) | TAG_SMALL
}

#[no_mangle]
pub extern "C" fn mana_rt_decode_packet(ctx: *mut ProcCtx, ty: u64, bin: u64, _opts: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if ty & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let Some((bp, blen)) = bin_parts(bin) else {
        return raise_badarg(ctx);
    };
    let bytes: Vec<u8> = unsafe { std::slice::from_raw_parts(bp, blen) }.to_vec();
    // root the input binary across the parse: dp_ok slices the REST out of
    // it (a view for large tails — Bandit re-feeds ever-shrinking buffers,
    // and copying every rest made header parsing O(lines x buffer))
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, bin];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let slot = &fr[2] as *const u64;
    let base = bytes.as_ptr();
    let r = match atom_bytes(ty) {
        b"http_bin" => dp_http(ctx, slot, base, &bytes),
        b"httph_bin" => dp_httph(ctx, slot, base, &bytes),
        _ => {
            ctx.roots_head = saved;
            return raise_badarg(ctx);
        }
    };
    ctx.roots_head = saved;
    r
}

fn dp_more(ctx: &mut ProcCtx) -> u64 {
    pair_term(ctx, b"more", atom_intern(b"undefined"))
}

/// {ok, Packet, Rest} with Packet rooted across the Rest allocation.
/// `bin_slot` points at the GC-rooted original input term; `base` is the
/// scratch copy's start — Rest becomes a slice of the ORIGINAL binary
/// (zero-copy view when large).
fn dp_ok(
    ctx: &mut ProcCtx,
    packet: u64,
    bin_slot: *const u64,
    base: *const u8,
    rest: &[u8],
) -> u64 {
    let off = rest.as_ptr() as usize - base as usize;
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, NIL];
    fr[0] = saved;
    fr[2] = packet;
    ctx.roots_head = fr.as_ptr() as u64;
    let r = mana_rt_bin_slice(ctx as *mut ProcCtx, unsafe { *bin_slot }, off as u64, rest.len() as i64);
    let ctx = unsafe { &mut *(ctx as *mut ProcCtx) };
    fr[3] = r;
    let p = alloc_nursery(ctx, 4);
    unsafe {
        *p = (3 << 8) | KIND_TUPLE;
        *p.add(1) = atom_intern(b"ok");
        *p.add(2) = fr[2];
        *p.add(3) = fr[3];
    }
    ctx.roots_head = saved;
    p as u64
}

fn dp_http_error(
    ctx: &mut ProcCtx,
    bin_slot: *const u64,
    base: *const u8,
    line: &[u8],
    rest: &[u8],
) -> u64 {
    let lb = bytes_to_new_bin(ctx, line);
    let err = pair_term(ctx, b"http_error", lb); // roots lb internally
    dp_ok(ctx, err, bin_slot, base, rest)
}

/// Take one line (up to and including \r\n or \n). Returns (line_without
/// terminator, rest_index) or None if incomplete.
fn dp_line(bytes: &[u8]) -> Option<(&[u8], usize)> {
    let nl = bytes.iter().position(|&b| b == b'\n')?;
    let line = if nl > 0 && bytes[nl - 1] == b'\r' {
        &bytes[..nl - 1]
    } else {
        &bytes[..nl]
    };
    Some((line, nl + 1))
}

fn dp_http(ctx: &mut ProcCtx, bin_slot: *const u64, base: *const u8, bytes: &[u8]) -> u64 {
    let Some((line, rest_at)) = dp_line(bytes) else {
        return dp_more(ctx);
    };
    let rest = &bytes[rest_at..];
    let full_line = &bytes[..rest_at];
    // response line?
    if line.starts_with(b"HTTP/") {
        return dp_response(ctx, bin_slot, base, line, full_line, rest);
    }
    // request line: METHOD SP URI [SP HTTP/x.y]
    let mut parts = line.splitn(3, |&b| b == b' ');
    let method = parts.next().unwrap_or(b"");
    let Some(uri) = parts.next() else {
        return dp_http_error(ctx, bin_slot, base, full_line, rest);
    };
    let version = parts.next();
    if method.is_empty() || uri.is_empty() {
        return dp_http_error(ctx, bin_slot, base, full_line, rest);
    }
    let ver = match version {
        None => (0i64, 9i64),
        Some(v) => match dp_version(v) {
            Some(v) => v,
            None => return dp_http_error(ctx, bin_slot, base, full_line, rest),
        },
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, NIL, NIL, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    // method: known atom or binary
    fr[2] = if let Some(name) = HTTP_METHODS.iter().find(|&&m| m.as_bytes() == method) {
        atom_intern(name.as_bytes())
    } else {
        bytes_to_new_bin(ctx, method)
    };
    fr[3] = dp_uri(ctx, uri);
    let vt = alloc_nursery(ctx, 3);
    unsafe {
        *vt = (2 << 8) | KIND_TUPLE;
        *vt.add(1) = small_of(ver.0);
        *vt.add(2) = small_of(ver.1);
    }
    fr[4] = vt as u64;
    let req = alloc_nursery(ctx, 5);
    unsafe {
        *req = (4 << 8) | KIND_TUPLE;
        *req.add(1) = atom_intern(b"http_request");
        *req.add(2) = fr[2];
        *req.add(3) = fr[3];
        *req.add(4) = fr[4];
    }
    ctx.roots_head = saved;
    dp_ok(ctx, req as u64, bin_slot, base, rest)
}

fn dp_version(v: &[u8]) -> Option<(i64, i64)> {
    let v = v.strip_prefix(b"HTTP/")?;
    let dot = v.iter().position(|&b| b == b'.')?;
    let major = std::str::from_utf8(&v[..dot]).ok()?.parse::<i64>().ok()?;
    let minor = std::str::from_utf8(&v[dot + 1..]).ok()?.parse::<i64>().ok()?;
    Some((major, minor))
}

fn dp_response(
    ctx: &mut ProcCtx,
    bin_slot: *const u64,
    base: *const u8,
    line: &[u8],
    full_line: &[u8],
    rest: &[u8],
) -> u64 {
    let mut parts = line.splitn(3, |&b| b == b' ');
    let ver = parts.next().unwrap_or(b"");
    let Some(vt) = dp_version(ver) else {
        return dp_http_error(ctx, bin_slot, base, full_line, rest);
    };
    let Some(status) = parts.next() else {
        return dp_http_error(ctx, bin_slot, base, full_line, rest);
    };
    let Ok(code) = std::str::from_utf8(status).unwrap_or("x").parse::<i64>() else {
        return dp_http_error(ctx, bin_slot, base, full_line, rest);
    };
    let phrase = parts.next().unwrap_or(b"");
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let vtt = alloc_nursery(ctx, 3);
    unsafe {
        *vtt = (2 << 8) | KIND_TUPLE;
        *vtt.add(1) = small_of(vt.0);
        *vtt.add(2) = small_of(vt.1);
    }
    fr[2] = vtt as u64;
    fr[3] = bytes_to_new_bin(ctx, phrase);
    let resp = alloc_nursery(ctx, 5);
    unsafe {
        *resp = (4 << 8) | KIND_TUPLE;
        *resp.add(1) = atom_intern(b"http_response");
        *resp.add(2) = fr[2];
        *resp.add(3) = small_of(code);
        *resp.add(4) = fr[3];
    }
    ctx.roots_head = saved;
    dp_ok(ctx, resp as u64, bin_slot, base, rest)
}

fn dp_uri(ctx: &mut ProcCtx, uri: &[u8]) -> u64 {
    if uri == b"*" {
        return atom_intern(b"*");
    }
    let lower: Vec<u8> = uri.to_ascii_lowercase();
    for (scheme, name) in [(b"http://".as_slice(), &b"http"[..]), (b"https://", b"https")] {
        if lower.starts_with(scheme) {
            let after = &uri[scheme.len()..];
            let path_at = after
                .iter()
                .position(|&b| b == b'/')
                .unwrap_or(after.len());
            let hostport = &after[..path_at];
            let path: &[u8] = if path_at == after.len() { b"/" } else { &after[path_at..] };
            let (host, port) = match hostport.iter().position(|&b| b == b':') {
                Some(c) => {
                    let p = std::str::from_utf8(&hostport[c + 1..])
                        .ok()
                        .and_then(|s| s.parse::<i64>().ok());
                    (&hostport[..c], p)
                }
                None => (hostport, None),
            };
            let saved = ctx.roots_head;
            let mut fr = [0u64, 2, NIL, NIL];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            fr[2] = bytes_to_new_bin(ctx, host);
            fr[3] = bytes_to_new_bin(ctx, path);
            let t = alloc_nursery(ctx, 6);
            unsafe {
                *t = (5 << 8) | KIND_TUPLE;
                *t.add(1) = atom_intern(b"absoluteURI");
                *t.add(2) = atom_intern(name);
                *t.add(3) = fr[2];
                *t.add(4) = match port {
                    Some(p) => small_of(p),
                    None => atom_intern(b"undefined"),
                };
                *t.add(5) = fr[3];
            }
            ctx.roots_head = saved;
            return t as u64;
        }
    }
    if let Some(pos) = uri.windows(3).position(|w| w == b"://") {
        let saved = ctx.roots_head;
        let mut fr = [0u64, 2, NIL, NIL];
        fr[0] = saved;
        ctx.roots_head = fr.as_ptr() as u64;
        fr[2] = bytes_to_new_bin(ctx, &uri[..pos]);
        fr[3] = bytes_to_new_bin(ctx, &uri[pos + 3..]);
        let t = alloc_nursery(ctx, 4);
        unsafe {
            *t = (3 << 8) | KIND_TUPLE;
            *t.add(1) = atom_intern(b"scheme");
            *t.add(2) = fr[2];
            *t.add(3) = fr[3];
        }
        ctx.roots_head = saved;
        return t as u64;
    }
    if uri.first() == Some(&b'/') {
        let p = bytes_to_new_bin(ctx, uri);
        return pair_term(ctx, b"abs_path", p);
    }
    // anything else (unknown methods' tokens etc.): the bare binary
    bytes_to_new_bin(ctx, uri)
}

fn dp_httph(ctx: &mut ProcCtx, bin_slot: *const u64, base: *const u8, bytes: &[u8]) -> u64 {
    let Some((line, mut rest_at)) = dp_line(bytes) else {
        return dp_more(ctx);
    };
    if line.is_empty() {
        return dp_ok(ctx, atom_intern(b"http_eoh"), bin_slot, base, &bytes[rest_at..]);
    }
    if rest_at == bytes.len() {
        // a complete header line could still be extended by an obs-fold
        // continuation — BEAM waits for at least one more byte
        return dp_more(ctx);
    }
    let full_line = &bytes[..rest_at];
    let Some(colon) = line.iter().position(|&b| b == b':') else {
        return dp_http_error(ctx, bin_slot, base, full_line, &bytes[rest_at..]);
    };
    let name = &line[..colon];
    let mut value: Vec<u8> = line[colon + 1..]
        .iter()
        .copied()
        .skip_while(|&b| b == b' ' || b == b'\t')
        .collect();
    // obs-fold: continuation lines start with SP/HT and extend the value
    // RAW — BEAM preserves the CRLF and the leading whitespace verbatim
    while rest_at < bytes.len() && (bytes[rest_at] == b' ' || bytes[rest_at] == b'\t') {
        let Some((cont, next_at)) = dp_line(&bytes[rest_at..]) else {
            return dp_more(ctx);
        };
        value.extend_from_slice(b"\r\n");
        value.extend_from_slice(cont);
        rest_at += next_at;
    }
    let rest = &bytes[rest_at..];
    let canon = canonical_field(name);
    let (idx, field_term_is_atom) = match HTTP_FIELDS
        .iter()
        .position(|&f| f.as_bytes() == canon.as_slice())
    {
        Some(i) => (i as i64 + 1, true),
        None => (0, false),
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    fr[2] = if field_term_is_atom {
        atom_intern(HTTP_FIELDS[(idx - 1) as usize].as_bytes())
    } else {
        bytes_to_new_bin(ctx, &canon)
    };
    fr[3] = bytes_to_new_bin(ctx, &value);
    // 4th element: the field name as received (original case) — OTP 26+
    let orig = bytes_to_new_bin(ctx, name);
    let mut fr2 = [0u64, 1, orig];
    fr2[0] = ctx.roots_head;
    ctx.roots_head = fr2.as_ptr() as u64;
    let h = alloc_nursery(ctx, 6);
    unsafe {
        *h = (5 << 8) | KIND_TUPLE;
        *h.add(1) = atom_intern(b"http_header");
        *h.add(2) = small_of(idx);
        *h.add(3) = fr[2];
        *h.add(4) = fr2[2];
        *h.add(5) = fr[3];
    }
    ctx.roots_head = saved;
    dp_ok(ctx, h as u64, bin_slot, base, rest)
}

/// send_after/start_timer. `wrap != 0` wraps the message as
/// {timeout, Ref, Msg} (start_timer semantics). Returns the timer ref.
#[no_mangle]
pub extern "C" fn mana_rt_send_after(
    ctx: *mut ProcCtx,
    ms: u64,
    dest: u64,
    msg: u64,
    wrap: u64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if ms & TAG_MASK != TAG_SMALL || (ms as i64 >> 3) < 0 {
        return raise_badarg(ctx);
    }
    let millis = (ms as i64 >> 3) as u64;
    let (dest_pid, dest_name) = if dest & 0xF == PID_TAG4 {
        (Some((dest >> 4) as usize), None)
    } else if dest & TAG_MASK == TAG_ATOM {
        (None, Some(dest))
    } else {
        return raise_badarg(ctx);
    };
    let r = mana_rt_make_ref(ctx as *mut ProcCtx);
    let payload = if wrap != 0 {
        // {timeout, Ref, Msg}
        let m = eternal_deep_copy(msg);
        let p = alloc_space(4);
        unsafe {
            *p = (3 << 8) | KIND_TUPLE;
            *p.add(1) = atom_intern(b"timeout");
            *p.add(2) = r;
            *p.add(3) = m;
        }
        p as u64
    } else {
        eternal_deep_copy(msg)
    };
    let mut guard = TIMERS.lock().unwrap();
    let t = guard.get_or_insert_with(|| Timers {
        entries: Vec::new(),
        global: ctx.global,
        thread_started: false,
    });
    if !t.thread_started {
        t.thread_started = true;
        std::thread::Builder::new()
            .name("mana-timers".into())
            .spawn(timer_thread)
            .expect("timer thread");
    }
    t.entries.push(TimerEntry {
        deadline: std::time::Instant::now() + std::time::Duration::from_millis(millis),
        ref_id: r >> 4,
        dest_pid,
        dest_name,
        msg: payload,
    });
    drop(guard);
    TIMER_CV.notify_one();
    r
}

/// cancel_timer/1,2 → remaining ms | false.
#[no_mangle]
pub extern "C" fn mana_rt_cancel_timer(ctx: *mut ProcCtx, r: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if r & 0xF != REF_TAG4 {
        return raise_badarg(ctx);
    }
    let ref_id = r >> 4;
    let mut guard = TIMERS.lock().unwrap();
    let Some(t) = guard.as_mut() else {
        return known().false_a;
    };
    match t.entries.iter().position(|e| e.ref_id == ref_id) {
        Some(i) => {
            let e = t.entries.swap_remove(i);
            let rem = e
                .deadline
                .saturating_duration_since(std::time::Instant::now())
                .as_millis() as u64;
            ((rem << 3) as u64) | TAG_SMALL
        }
        None => known().false_a,
    }
}

// ---------------------------------------------------------------------------
// process dictionary + name registry

/// put/2 — returns the previous value or undefined. Both key and value are
/// promoted so the entry is safe for cross-thread readers and minors.
#[no_mangle]
pub extern "C" fn mana_rt_pd_put(ctx: *mut ProcCtx, k: u64, v: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, k, v];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let k = promote_term(ctx, fr[2]);
    fr[2] = k;
    let v = promote_term(ctx, fr[3]);
    ctx.roots_head = saved;
    let cell = proc_ref(ctx.global, ctx.current).expect("live current process");
    let p = unsafe { proc_mut(cell) };
    let mut pd = p.pdict.lock();
    match pd.iter_mut().find(|(ek, _)| mana_rt_eq_exact(*ek, k) == 1) {
        Some(e) => std::mem::replace(&mut e.1, v),
        None => {
            pd.push((k, v));
            known().undefined
        }
    }
}

#[no_mangle]
pub extern "C" fn mana_rt_pd_get(ctx: *mut ProcCtx, k: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let cell = proc_ref(ctx.global, ctx.current).expect("live current process");
    let p = unsafe { proc_mut(cell) };
    let pd = p.pdict.lock();
    pd.iter()
        .find(|(ek, _)| mana_rt_eq_exact(*ek, k) == 1)
        .map(|&(_, v)| v)
        .unwrap_or(known().undefined)
}

#[no_mangle]
pub extern "C" fn mana_rt_pd_erase(ctx: *mut ProcCtx, k: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let cell = proc_ref(ctx.global, ctx.current).expect("live current process");
    let p = unsafe { proc_mut(cell) };
    let mut pd = p.pdict.lock();
    match pd.iter().position(|(ek, _)| mana_rt_eq_exact(*ek, k) == 1) {
        Some(i) => pd.remove(i).1,
        None => known().undefined,
    }
}

/// The whole dictionary as [{K, V}] — for get/0 and process_info.
/// erlang:get_keys/0 — list of pdict keys.
#[no_mangle]
pub extern "C" fn mana_rt_pd_keys(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let cell = proc_ref(ctx.global, ctx.current).expect("live current process");
    let p = unsafe { proc_mut(cell) };
    let keys: Vec<u64> = p.pdict.lock().iter().map(|&(k, _)| k).collect();
    // pdict values are promoted at put — keys are shared-safe; the list
    // cells still need the acc rooted across allocs
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &k in keys.iter().rev() {
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = k;
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[2]
}

fn pdict_to_list(ctx: &mut ProcCtx, pid: usize) -> u64 {
    let entries: Vec<(u64, u64)> = match proc_ref(ctx.global, pid) {
        Some(cell) => unsafe { proc_mut(cell) }.pdict.lock().clone(),
        None => Vec::new(),
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, 0];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &(k, v) in entries.iter().rev() {
        // k/v are old-space — no rooting needed for them
        let t = alloc_nursery(ctx, 3);
        unsafe {
            *t = (2 << 8) | KIND_TUPLE;
            *t.add(1) = k;
            *t.add(2) = v;
        }
        fr[3] = t as u64;
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = fr[3];
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[2]
}

#[no_mangle]
pub extern "C" fn mana_rt_pd_get_all(ctx: *mut ProcCtx) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    let cur = ctxr.current;
    pdict_to_list(ctxr, cur)
}

/// Registered names: atom → pid id. Names are dropped at process death.
static NAME_REGISTRY: std::sync::Mutex<Option<std::collections::HashMap<u64, usize>>> =
    std::sync::Mutex::new(None);

#[no_mangle]
pub extern "C" fn mana_rt_register(ctx: *mut ProcCtx, name: u64, pid: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if name & TAG_MASK != TAG_ATOM
        || atom_bytes(name) == b"undefined"
        || pid & 0xF != PID_TAG4
    {
        return raise_badarg(ctx);
    }
    let id = (pid >> 4) as usize;
    if proc_ref(ctx.global, id).is_none() {
        return raise_badarg(ctx);
    }
    let mut guard = NAME_REGISTRY.lock().unwrap();
    let map = guard.get_or_insert_with(Default::default);
    if map.contains_key(&name) || map.values().any(|&p| p == id) {
        return raise_badarg(ctx);
    }
    map.insert(name, id);
    known().true_a
}

#[no_mangle]
pub extern "C" fn mana_rt_whereis(ctx: *mut ProcCtx, name: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if name & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let guard = NAME_REGISTRY.lock().unwrap();
    match guard.as_ref().and_then(|m| m.get(&name)) {
        // a name may outlive its process between death and cleanup — treat
        // dead as unregistered
        Some(&id) if proc_ref(ctx.global, id).is_some() => make_pid(id),
        _ => known().undefined,
    }
}

#[no_mangle]
pub extern "C" fn mana_rt_unregister(ctx: *mut ProcCtx, name: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut guard = NAME_REGISTRY.lock().unwrap();
    match guard.as_mut().and_then(|m| m.remove(&name)) {
        Some(_) => known().true_a,
        None => raise_badarg(ctx),
    }
}

/// process_info/2 — the closed-world subset: registered_name, dictionary,
/// message_queue_len; everything else answers undefined.
#[no_mangle]
pub extern "C" fn mana_rt_process_info2(ctx: *mut ProcCtx, pid: u64, item: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if pid & 0xF != PID_TAG4 || item & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let id = (pid >> 4) as usize;
    if proc_ref(ctx.global, id).is_none() {
        return known().undefined;
    }
    match atom_bytes(item) {
        b"registered_name" => {
            let guard = NAME_REGISTRY.lock().unwrap();
            let name = guard
                .as_ref()
                .and_then(|m| m.iter().find(|&(_, &p)| p == id).map(|(&n, _)| n));
            drop(guard);
            match name {
                Some(n) => {
                    let t = alloc_nursery(ctx, 3);
                    unsafe {
                        *t = (2 << 8) | KIND_TUPLE;
                        *t.add(1) = item;
                        *t.add(2) = n;
                    }
                    t as u64
                }
                None => NIL, // BEAM: [] for an unnamed live process
            }
        }
        b"dictionary" => {
            let saved = ctx.roots_head;
            let mut fr = [0u64, 1, 0];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            fr[2] = pdict_to_list(ctx, id);
            let t = alloc_nursery(ctx, 3);
            unsafe {
                *t = (2 << 8) | KIND_TUPLE;
                *t.add(1) = item;
                *t.add(2) = fr[2];
            }
            ctx.roots_head = saved;
            t as u64
        }
        b"trap_exit" => {
            let cell = proc_ref(ctx.global, id).unwrap();
            let p = unsafe { proc_mut(cell) };
            let v = if p.lstate.lock().trap_exit {
                known().true_a
            } else {
                known().false_a
            };
            let t = alloc_nursery(ctx, 3);
            unsafe {
                *t = (2 << 8) | KIND_TUPLE;
                *t.add(1) = item;
                *t.add(2) = v;
            }
            t as u64
        }
        b"current_stacktrace" => {
            // stacktraces are not built — TODO(stacktraces)
            let t = alloc_nursery(ctx, 3);
            unsafe {
                *t = (2 << 8) | KIND_TUPLE;
                *t.add(1) = item;
                *t.add(2) = NIL;
            }
            t as u64
        }
        b"message_queue_len" => {
            // ingress length is approximate cross-thread; good enough
            let cell = proc_ref(ctx.global, id).unwrap();
            let p = unsafe { proc_mut(cell) };
            let n = (p.private.len() - p.cursor.min(p.private.len())) + p.ingress.len();
            let t = alloc_nursery(ctx, 3);
            unsafe {
                *t = (2 << 8) | KIND_TUPLE;
                *t.add(1) = item;
                *t.add(2) = ((n as u64) << 3) | TAG_SMALL;
            }
            t as u64
        }
        _ => known().undefined,
    }
}

/// erlang:spawn_opt/2 — closure spawn with link/monitor options.
#[no_mangle]
pub extern "C" fn mana_rt_spawn_opt_fun(ctx: *mut ProcCtx, fun: u64, opts: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    let (mut link, mut monitor) = (false, false);
    let mut cur = opts;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctxr);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let opt = unsafe { *p };
        if opt & TAG_MASK == TAG_ATOM {
            match atom_bytes(opt) {
                b"link" => link = true,
                b"monitor" => monitor = true,
                _ => {}
            }
        } else if opt & TAG_MASK == TAG_BOXED && opt != 0 {
            let hp = opt as *const u64;
            let h = unsafe { *hp };
            if h & 0xff == KIND_TUPLE
                && h >> 8 == 2
                && atom_bytes(unsafe { *hp.add(1) }) == b"monitor"
            {
                monitor = true;
            }
        }
        cur = unsafe { *p.add(1) };
    }
    let pid = mana_rt_spawn(ctx, fun);
    if pid == 0 {
        return raise_badarg(unsafe { &mut *ctx });
    }
    if link {
        mana_rt_link(ctx, pid);
    }
    if monitor {
        let r = mana_rt_monitor(ctx, pid);
        return shared_tuple(unsafe { &mut *ctx }, &[pid, r]);
    }
    pid
}

// ---------------------------------------------------------------------------
// process BIF surface

/// Reduction budget exhausted: reschedule the current process.
#[no_mangle]
pub extern "C" fn mana_rt_yield(ctx: *mut ProcCtx) {
    let ctx = unsafe { &mut *ctx };
    suspend_current(ctx); // state stays Running → scheduler re-queues
}

#[no_mangle]
pub extern "C" fn mana_rt_self(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &*ctx };
    make_pid(ctx.current)
}

/// erlang:spawn/1 — returns the pid, or 0 for a non-arity-0-fun argument
/// (codegen raises badarg). Round-robin placement across schedulers.
#[no_mangle]
pub extern "C" fn mana_rt_spawn(ctx: *mut ProcCtx, closure: u64) -> u64 {
    if closure & TAG_MASK != TAG_BOXED || closure == 0 {
        return 0;
    }
    let header = unsafe { *(closure as *const u64) };
    if header & 0xff != KIND_FUN || (header >> 8) & 0xff != 0 {
        return 0;
    }
    let ctx = unsafe { &mut *ctx };
    let global = ctx.global;
    let closure = promote_term(ctx, closure);
    let home = if global.n_scheds == 1 {
        0
    } else {
        global.spawn_rr.fetch_add(1, Ordering::Relaxed) % global.n_scheds
    };
    let pid = register_process(
        global,
        Process {
            home,
            coro: Some(make_coroutine(global, home)),
            yielder: std::ptr::null(),
            saved_roots: 0,
            saved_exc_class: 0,
            saved_exc_reason: 0,
            ingress: SegQueue::new(),
            private: Vec::new(),
            cursor: 0,
            state: Mutex::new(PState::Runnable),
            pending_closure: closure,
            lstate: Mutex::new(LinkState::default()),
            pdict: Mutex::new(Vec::new()),
            dirty: std::sync::atomic::AtomicBool::new(true),
        },
    );
    if home == ctx.sched_id {
        ctx.run_q.push_back(pid);
    } else {
        global.scheds[home].inject.push(pid);
        wake_sched(global, home);
    }
    make_pid(pid)
}

/// erlang:'!'/2 — young payload parts are promoted (copied once), old parts
/// pass zero-copy. Sends to dead/unknown pids succeed silently.
#[no_mangle]
pub extern "C" fn mana_rt_send(ctx: *mut ProcCtx, pid: u64, msg: u64) {
    let mut pid = pid;
    if pid & 0xF == REF_TAG4 {
        // reply alias: silently dropped when inactive
        let target = ALIASES
            .lock()
            .unwrap()
            .as_ref()
            .and_then(|m| m.get(&pid).copied());
        match target {
            Some(t) => pid = make_pid(t),
            None => return,
        }
    } else if pid & TAG_MASK == TAG_ATOM {
        let ctxr = unsafe { &mut *ctx };
        match mana_rt_whereis(ctxr as *mut ProcCtx, pid) {
            p if p & 0xF == PID_TAG4 => pid = p,
            _ => return, // BEAM raises badarg; softened — TODO(send-name)
        }
    }
    let Some(id) = pid_id(pid) else { return };
    let ctx = unsafe { &mut *ctx };
    let global = ctx.global;
    let Some(cell) = proc_ref(global, id) else {
        return;
    };
    let p = unsafe { &*cell.0.get() };
    // same-scheduler sends stay zero-copy even for young terms: the local
    // minor drains + scans local ingress queues. Cross-scheduler payloads
    // promote (so no scheduler ever sees another's nursery).
    let msg = if p.home == ctx.sched_id {
        msg
    } else {
        promote_term(ctx, msg)
    };
    p.dirty.store(true, Ordering::Release);
    p.ingress.push(msg);
    let mut st = p.state.lock();
    if matches!(*st, PState::Waiting(_)) {
        *st = PState::Runnable;
        drop(st);
        if p.home == ctx.sched_id {
            ctx.run_q.push_back(id);
        } else {
            global.scheds[p.home].inject.push(id);
            wake_sched(global, p.home);
        }
    }
}

// ---- receive primops (erlc lowers `receive` to these) ----

#[allow(clippy::mut_from_ref)]
fn cur_proc(ctx: &ProcCtx) -> &mut Process {
    debug_assert!(ctx.current_cell != 0);
    unsafe { proc_mut(&*(ctx.current_cell as *const ProcessCell)) }
}

/// Move everything from the ingress queue into the private list.
fn drain_ingress(p: &mut Process) {
    while let Some(m) = p.ingress.pop() {
        p.private.push(m);
    }
}

#[no_mangle]
pub extern "C" fn mana_rt_recv_ready(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &*ctx };
    let p = cur_proc(ctx);
    if p.private.len() <= p.cursor {
        drain_ingress(p);
    }
    (p.private.len() > p.cursor) as u64
}

#[no_mangle]
pub extern "C" fn mana_rt_recv_peek(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &*ctx };
    let p = cur_proc(ctx);
    if p.private.len() > p.cursor {
        p.private[p.cursor]
    } else {
        NIL
    }
}

#[no_mangle]
pub extern "C" fn mana_rt_recv_next(ctx: *mut ProcCtx) {
    let ctx = unsafe { &*ctx };
    cur_proc(ctx).cursor += 1;
}

#[no_mangle]
pub extern "C" fn mana_rt_recv_remove(ctx: *mut ProcCtx) {
    let ctx = unsafe { &*ctx };
    let p = cur_proc(ctx);
    let c = p.cursor;
    p.private.remove(c);
    p.cursor = 0;
}

/// recv_wait_timeout: 1 if the timeout elapsed, 0 if a message is available
/// past the cursor. Timeout term: small int (ms) or 'infinity'.
#[no_mangle]
pub extern "C" fn mana_rt_recv_wait(ctx: *mut ProcCtx, timeout: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let deadline: Option<Instant> = if timeout & TAG_MASK == TAG_SMALL {
        let ms = (timeout as i64) >> 3;
        if ms <= 0 {
            let p = cur_proc(ctx);
            drain_ingress(p);
            return (p.private.len() <= p.cursor) as u64;
        }
        Some(Instant::now() + Duration::from_millis(ms as u64))
    } else {
        None // 'infinity' (or anything non-integer)
    };
    loop {
        {
            let p = cur_proc(ctx);
            drain_ingress(p);
            if p.private.len() > p.cursor {
                return 0;
            }
            if let Some(dl) = deadline {
                if Instant::now() >= dl {
                    return 1;
                }
            }
            *p.state.lock() = PState::Waiting(deadline);
        }
        suspend_current(ctx);
    }
}

// ---------------------------------------------------------------------------
// allocation & GC

/// Allocation slow path (compiled code bumps the nursery inline).
#[no_mangle]
pub extern "C" fn mana_rt_alloc_slow(ctx: *mut ProcCtx, words: u64) -> *mut u64 {
    let ctx = unsafe { &mut *ctx };
    let words = words as usize;
    park_if_stw(ctx);
    let promoted = minor_collect(ctx);
    let g = ctx.global;
    if g.old_used.load(Ordering::Relaxed) > g.old_limit.load(Ordering::Relaxed) {
        stw_major(ctx);
    }
    // adaptive nursery: grow until minors rarely promote
    let grow_to = if words > ctx.nursery_words {
        usize::max(ctx.nursery_words * 2, words * 2)
    } else if promoted > ctx.nursery_words / 16 {
        ctx.nursery_words * 2
    } else {
        0
    };
    // the stress pin (MANA_NURSERY_WORDS) suppresses adaptive growth but
    // must still honor requests that cannot fit the pinned nursery
    let must_grow = words * 2 > ctx.nursery_words;
    if grow_to > 0 && (nursery_words_override().is_none() || must_grow) {
        unsafe { free_space(ctx.nursery_start, ctx.nursery_words) };
        let nursery = alloc_space(grow_to);
        ctx.nursery_start = nursery;
        ctx.nursery_words = grow_to;
        ctx.heap_top = nursery;
        ctx.heap_end = unsafe { nursery.add(grow_to) };
    }
    unsafe {
        let p = ctx.heap_top;
        ctx.heap_top = ctx.heap_top.add(words);
        p
    }
}

/// Eternal objects are write-once: their fields can reference the
/// ALLOCATING scheduler's current nursery only until that scheduler's next
/// minor forwards them — afterwards they point old/static forever. Minors
/// therefore scan only the fresh ones (this list); the permanent registry
/// is walked at majors (old-space compaction). Scanning the whole registry
/// per minor made keepalive GC quadratic (eternals accrue per request).
static FRESH_ETERNALS: std::sync::Mutex<Vec<(usize, bool, usize)>> =
    std::sync::Mutex::new(Vec::new());

/// Raise-path allocations: never moved; fields scanned by collections.
#[no_mangle]
pub extern "C" fn mana_rt_alloc_eternal(ctx: *mut ProcCtx, words: u64, is_cons: u64) -> *mut u64 {
    let ctx = unsafe { &*ctx };
    let p = alloc_space(words as usize);
    ctx.global.eternal.lock().push((p as usize, is_cons != 0));
    FRESH_ETERNALS
        .lock()
        .unwrap()
        .push((p as usize, is_cons != 0, ctx.sched_id));
    p
}

/// Walk one process's saved GC root slots with `f`.
unsafe fn walk_proc_roots(p: &mut Process, mut f: impl FnMut(*mut u64)) {
    unsafe {
        let mut frame = p.saved_roots as *mut u64;
        while !frame.is_null() {
            let len = *frame.add(1) as usize;
            for i in 0..len {
                f(frame.add(2 + i));
            }
            frame = *frame as *mut u64;
        }
        f(&mut p.saved_exc_class as *mut u64);
        f(&mut p.saved_exc_reason as *mut u64);
        f(&mut p.pending_closure as *mut u64);
    }
    walk_proc_shared_roots(p, f);
}

/// Live shared state that stays valid even while the process is swapped in:
/// the pdict and a pending exit reason. Unlike the saved_* fields these must
/// be forwarded for RUNNING processes too — majors free every old chunk, and
/// pd_put promotes into old space.
fn walk_proc_shared_roots(p: &mut Process, mut f: impl FnMut(*mut u64)) {
    {
        let mut pd = p.pdict.lock();
        for (k, v) in pd.iter_mut() {
            f(k as *mut u64);
            f(v as *mut u64);
        }
    }
    let mut ls = p.lstate.lock();
    if ls.pending_kill != 0 {
        f(&mut ls.pending_kill as *mut u64);
    }
}

/// Scheduler-local minor collection: copy live nursery objects into the
/// shared old space. Nothing outside this scheduler references its nursery
/// (send-time promotion), so the only synchronization is the old-space
/// lock held for the duration.
fn minor_collect(ctx: &mut ProcCtx) -> usize {
    let g = ctx.global;
    let used_before = g.old_used.load(Ordering::Relaxed);
    let mut worklist: Vec<u64> = Vec::new();
    let mut old = g.old.lock();

    unsafe {
        // current process: live chain is in ctx
        let mut frame = ctx.roots_head as *mut u64;
        while !frame.is_null() {
            let len = *frame.add(1) as usize;
            for i in 0..len {
                let s = frame.add(2 + i);
                *s = forward_minor(ctx, &mut old, *s, &mut worklist);
            }
            frame = *frame as *mut u64;
        }
        ctx.exc_class = forward_minor(ctx, &mut old, ctx.exc_class, &mut worklist);
        ctx.exc_reason = forward_minor(ctx, &mut old, ctx.exc_reason, &mut worklist);

        // suspended processes pinned to this scheduler. Messages: drain
        // ingress into private first, then scan private. Anything arriving
        // concurrently from another scheduler is old (send promotes), so it
        // is safe to leave in ingress unscanned.
        {
            let tab = g.procs.read();
            for (id, slot) in tab.iter().enumerate() {
                let Some(cell) = slot else { continue };
                let p = proc_mut(cell);
                if p.home != ctx.sched_id {
                    continue;
                }
                if id != ctx.current {
                    // clean parked processes cannot reference this nursery:
                    // their roots were forwarded by the minor that cleared
                    // the flag, and gaining new refs (running / receiving a
                    // message) re-sets it. This keeps minors O(active
                    // processes), not O(all processes).
                    if !p.dirty.swap(false, Ordering::AcqRel) {
                        continue;
                    }
                    walk_proc_roots(p, |s| {
                        *s = forward_minor(ctx, &mut old, *s, &mut worklist);
                    });
                } else {
                    // pd_put promotes, so this is normally a pass-through;
                    // it keeps the pdict correct even if a nursery term ever
                    // lands there.
                    walk_proc_shared_roots(p, |s| {
                        *s = forward_minor(ctx, &mut old, *s, &mut worklist);
                    });
                }
                drain_ingress(p);
                for m in p.private.iter_mut() {
                    *m = forward_minor(ctx, &mut old, *m, &mut worklist);
                }
            }
        }

        // eternal objects (exception reasons) may reference this nursery —
        // but only the ones allocated on THIS scheduler since its last
        // minor (write-once: after one forwarding pass their fields are
        // old/static forever). The full registry is majors-only.
        {
            let mut fresh = FRESH_ETERNALS.lock().unwrap();
            fresh.retain(|&(pa, is_cons, sid)| {
                if sid != ctx.sched_id {
                    return true;
                }
                scan_fields(pa as *mut u64, is_cons, &mut |s| {
                    *s = forward_minor(ctx, &mut old, *s, &mut worklist);
                });
                false
            });
        }

        while let Some(t) = worklist.pop() {
            let is_cons = t & TAG_MASK == TAG_CONS;
            let p = (t & !TAG_MASK) as *mut u64;
            scan_fields(p, is_cons, &mut |s| {
                *s = forward_minor(ctx, &mut old, *s, &mut worklist);
            });
        }
    }
    drop(old);

    ctx.heap_top = ctx.nursery_start;
    let promoted = g.old_used.load(Ordering::Relaxed) - used_before;
    if g.gc_log {
        eprintln!(
            "mana: minor gc (sched {}), promoted {} words (nursery {}, old {} words)",
            ctx.sched_id,
            promoted,
            ctx.nursery_words,
            g.old_used.load(Ordering::Relaxed)
        );
    }
    promoted
}

/// Apply `f` to each term-field slot of the object at `p`.
/// For cons cells pass `is_cons` (no header); boxed objects self-describe.
unsafe fn scan_fields(p: *mut u64, is_cons: bool, f: &mut impl FnMut(*mut u64)) {
    unsafe {
        if is_cons {
            f(p);
            f(p.add(1));
            return;
        }
        let header = *p;
        match header & 0xff {
            KIND_TUPLE => {
                for i in 0..(header >> 8) as usize {
                    f(p.add(1 + i));
                }
            }
            KIND_FUN => {
                for i in 0..(header >> 16) as usize {
                    f(p.add(2 + i));
                }
            }
            KIND_MAP => {
                for i in 0..2 * (header >> 8) as usize {
                    f(p.add(1 + i));
                }
            }
            // sub-binary views: the parent binary is a term field
            KIND_SUBBIN => f(p.add(1)),
            _ => {}
        }
    }
}

unsafe fn forward_minor(
    ctx: &ProcCtx,
    old: &mut OldSpace,
    t: u64,
    worklist: &mut Vec<u64>,
) -> u64 {
    if t == 0 {
        return 0;
    }
    match t & TAG_MASK {
        TAG_SMALL | TAG_ATOM | TAG_PID => t,
        _ if t == NIL => t,
        TAG_CONS => unsafe {
            let addr = t & !TAG_MASK;
            if !in_my_nursery(ctx, addr) {
                return t;
            }
            let p = addr as *mut u64;
            if *p & TAG_MASK == TAG_FORWARD {
                return (*p & !TAG_MASK) | TAG_CONS;
            }
            let new = old.alloc(2, &ctx.global.old_used);
            *new = *p;
            *new.add(1) = *p.add(1);
            *p = new as u64 | TAG_FORWARD;
            let nt = new as u64 | TAG_CONS;
            worklist.push(nt);
            nt
        },
        TAG_BOXED => unsafe {
            if !in_my_nursery(ctx, t) {
                return t;
            }
            let p = t as *mut u64;
            if *p & TAG_MASK == TAG_FORWARD {
                return *p & !TAG_MASK;
            }
            let words = 1 + payload_words(*p);
            let new = old.alloc(words, &ctx.global.old_used);
            std::ptr::copy_nonoverlapping(p, new, words);
            *p = new as u64 | TAG_FORWARD;
            let nt = new as u64;
            worklist.push(nt);
            nt
        },
        _ => {
            eprintln!("mana: invalid term {:#x} during minor collection", t);
            std::process::exit(70);
        }
    }
}

// ---- stop-the-world major collection ----

/// Park at a safepoint while another scheduler runs a major collection.
fn park_if_stw(ctx: &mut ProcCtx) {
    let g = ctx.global;
    if !g.stw_flag.load(Ordering::Acquire) {
        return;
    }
    let mut stw = g.stw.lock();
    while stw.collecting {
        stw.parked += 1;
        g.stw_cv.notify_all();
        let gen = stw.gen;
        while stw.collecting && stw.gen == gen {
            g.stw_cv.wait(&mut stw);
        }
        stw.parked -= 1;
    }
}

/// Request a stop-the-world major collection; runs once every other
/// scheduler has parked at a safepoint.
fn stw_major(ctx: &mut ProcCtx) {
    let g = ctx.global;
    {
        let mut stw = g.stw.lock();
        if stw.collecting {
            drop(stw);
            park_if_stw(ctx); // someone else is collecting: follow
            return;
        }
        stw.collecting = true;
        g.stw_flag.store(true, Ordering::Release);
        for id in 0..g.n_scheds {
            if id != ctx.sched_id {
                wake_sched(g, id);
            }
        }
        while stw.parked < g.n_scheds - 1 {
            g.stw_cv.wait(&mut stw);
        }
    }

    major_collect_stw(ctx);

    let mut stw = g.stw.lock();
    stw.collecting = false;
    g.stw_flag.store(false, Ordering::Release);
    stw.gen += 1;
    g.stw_cv.notify_all();
}

/// All other schedulers are parked: evacuate every nursery, then compact
/// the old space into one fresh chunk.
fn major_collect_stw(ctx: &mut ProcCtx) {
    let g = ctx.global;
    let used_before = g.old_used.load(Ordering::Relaxed);

    // 1. evacuate every scheduler's nursery (their ctxs are quiescent)
    for id in 0..g.n_scheds {
        let octx = g.scheds[id].ctx_addr.load(Ordering::Acquire) as *mut ProcCtx;
        if octx.is_null() {
            continue;
        }
        minor_collect(unsafe { &mut *octx });
    }

    // 2. full copy of the old space, single-threaded
    let mut old = g.old.lock();
    let live_bound = g.old_used.load(Ordering::Relaxed);
    let to_words = usize::max(live_bound, OLD_CHUNK_WORDS);
    let to_space = alloc_space(to_words);
    let mut top = to_space;
    let mut worklist: Vec<u64> = Vec::new();
    // from-space extents: only terms inside these move; everything else
    // (eternals, compiler statics) passes through untouched
    let from: Vec<(usize, usize)> = old
        .chunks
        .iter()
        .map(|c| (c.start as usize, c.top as usize))
        .collect();
    let from = &from[..];

    // pids currently swapped into a scheduler: their LIVE state is in the
    // ctx (walked below); their saved_* fields are stale from the last
    // yield and must not be scanned.
    let mut running: Vec<usize> = Vec::new();

    unsafe {
        for id in 0..g.n_scheds {
            let octx = g.scheds[id].ctx_addr.load(Ordering::Acquire) as *mut ProcCtx;
            if octx.is_null() {
                continue;
            }
            let octx = &mut *octx;
            if octx.current != usize::MAX {
                running.push(octx.current);
            }
            let mut frame = octx.roots_head as *mut u64;
            while !frame.is_null() {
                let len = *frame.add(1) as usize;
                for i in 0..len {
                    let s = frame.add(2 + i);
                    *s = forward_major(*s, from, &mut top, &mut worklist);
                }
                frame = *frame as *mut u64;
            }
            octx.exc_class = forward_major(octx.exc_class, from, &mut top, &mut worklist);
            octx.exc_reason = forward_major(octx.exc_reason, from, &mut top, &mut worklist);
        }
        {
            let tab = g.procs.read();
            for (id, slot) in tab.iter().enumerate() {
                let Some(cell) = slot else { continue };
                let p = proc_mut(cell);
                if !running.contains(&id) {
                    walk_proc_roots(p, |s| {
                        *s = forward_major(*s, from, &mut top, &mut worklist);
                    });
                } else {
                    // running: saved_* fields are stale, but the pdict and
                    // pending_kill are live and hold old-space terms — the
                    // from-space is about to be freed.
                    walk_proc_shared_roots(p, |s| {
                        *s = forward_major(*s, from, &mut top, &mut worklist);
                    });
                }
                drain_ingress(p); // everyone is parked: no concurrent pushes
                for m in p.private.iter_mut() {
                    *m = forward_major(*m, from, &mut top, &mut worklist);
                }
            }
        }
        {
            let eternal = g.eternal.lock();
            for (pa, is_cons) in eternal.iter() {
                scan_fields(*pa as *mut u64, *is_cons, &mut |s| {
                    *s = forward_major(*s, from, &mut top, &mut worklist);
                });
            }
        }
        while let Some(t) = worklist.pop() {
            let is_cons = t & TAG_MASK == TAG_CONS;
            let p = (t & !TAG_MASK) as *mut u64;
            scan_fields(p, is_cons, &mut |s| {
                *s = forward_major(*s, from, &mut top, &mut worklist);
            });
        }
        for chunk in old.chunks.iter() {
            free_space(chunk.start, chunk.words);
        }
    }

    let live = (top as usize - to_space as usize) / 8;
    old.chunks = vec![Chunk {
        start: to_space,
        top,
        end: unsafe { to_space.add(to_words) },
        words: to_words,
    }];
    g.old_used.store(live, Ordering::Relaxed);
    g.old_limit
        .store(usize::max(4 * live, OLD_LIMIT_INIT), Ordering::Relaxed);
    if g.gc_log {
        eprintln!(
            "mana: major gc, {} -> {} live words (limit {})",
            used_before,
            live,
            g.old_limit.load(Ordering::Relaxed)
        );
    }
}

/// Boxed/cons terms outside the from-space chunks — eternal mallocs and
/// compiler statics (binaries, funs) — are never moved and never get a
/// forwarding header written into them: writes to `.rodata` fault, and the
/// eternal registry scan must keep seeing real headers. Their fields are
/// updated via the eternal registry walk instead.
unsafe fn forward_major(
    t: u64,
    from: &[(usize, usize)],
    top: &mut *mut u64,
    worklist: &mut Vec<u64>,
) -> u64 {
    if t == 0 {
        return 0;
    }
    let in_from = |p: u64| {
        let a = p as usize;
        from.iter().any(|&(s, e)| a >= s && a < e)
    };
    match t & TAG_MASK {
        TAG_SMALL | TAG_ATOM | TAG_PID => t,
        _ if t == NIL => t,
        TAG_CONS => unsafe {
            let p = (t & !TAG_MASK) as *mut u64;
            if !in_from(p as u64) {
                return t;
            }
            if *p & TAG_MASK == TAG_FORWARD {
                return (*p & !TAG_MASK) | TAG_CONS;
            }
            let new = *top;
            *new = *p;
            *new.add(1) = *p.add(1);
            *top = top.add(2);
            *p = new as u64 | TAG_FORWARD;
            let nt = new as u64 | TAG_CONS;
            worklist.push(nt);
            nt
        },
        TAG_BOXED => unsafe {
            let p = t as *mut u64;
            if !in_from(p as u64) {
                return t;
            }
            if *p & TAG_MASK == TAG_FORWARD {
                return *p & !TAG_MASK;
            }
            let words = 1 + payload_words(*p);
            let new = *top;
            std::ptr::copy_nonoverlapping(p, new, words);
            *top = top.add(words);
            *p = new as u64 | TAG_FORWARD;
            let nt = new as u64;
            worklist.push(nt);
            nt
        },
        _ => {
            eprintln!("mana: invalid term {:#x} during major collection", t);
            std::process::exit(70);
        }
    }
}

// ---------------------------------------------------------------------------
// term order, equality, list/tuple helpers

fn atom_bytes(t: u64) -> &'static [u8] {
    unsafe {
        let p = (t & !TAG_MASK) as *const u64;
        let len = *p as usize;
        std::slice::from_raw_parts(p.add(1) as *const u8, len)
    }
}

/// Erlang type rank: number < atom < ref < fun < pid < tuple < map < nil
/// < list < bitstring.
fn type_rank(t: u64) -> u8 {
    match t & TAG_MASK {
        TAG_SMALL => 0,
        TAG_ATOM => 1,
        _ if t == NIL => 7,
        TAG_CONS => 8,
        TAG_PID => {
            if t & 0xF == PID_TAG4 {
                4
            } else {
                2 // ref
            }
        }
        TAG_BOXED => {
            let header = unsafe { *(t as *const u64) };
            match header & 0xff {
                KIND_FLOAT => 0,
                KIND_FUN => 3,
                KIND_MAP => 6,
                KIND_BIN | KIND_SUBBIN => 9,
                KIND_BIGNUM => 0, // numbers
                _ => 5, // tuple
            }
        }
        _ => 10,
    }
}

fn num_val(t: u64) -> f64 {
    if t & TAG_MASK == TAG_SMALL {
        return ((t as i64) >> 3) as f64;
    }
    if let Some((neg, mag)) = bignum_parts(t) {
        let v = bigint::mag_to_f64(mag);
        return if neg { -v } else { v };
    }
    f64::from_bits(unsafe { *(t as *const u64).add(1) })
}

/// Erlang term order with numeric coercion (== semantics for numbers).
/// Lists compared iteratively (payloads can be arbitrarily long).
#[no_mangle]
pub extern "C" fn mana_rt_compare(a: u64, b: u64) -> i64 {
    if a == b {
        return 0;
    }
    let (ra, rb) = (type_rank(a), type_rank(b));
    if ra != rb {
        return if ra < rb { -1 } else { 1 };
    }
    match ra {
        0 => {
            if bignum_parts(a).is_some() || bignum_parts(b).is_some() {
                // int vs int: exact; int vs float: f64 (num_val knows bigs)
                if is_int_term(a) && is_int_term(b) {
                    return int_cmp_exact(a, b);
                }
                let (x, y) = (num_val(a), num_val(b));
                return (x > y) as i64 - (x < y) as i64;
            }
            // numbers, possibly mixed int/float
            if a & TAG_MASK == TAG_SMALL && b & TAG_MASK == TAG_SMALL {
                let (x, y) = ((a as i64) >> 3, (b as i64) >> 3);
                return (x > y) as i64 - (x < y) as i64;
            }
            let (x, y) = (num_val(a), num_val(b));
            (x > y) as i64 - (x < y) as i64
        }
        1 => {
            // atoms: by text
            let (x, y) = (atom_bytes(a), atom_bytes(b));
            match x.cmp(y) {
                std::cmp::Ordering::Less => -1,
                std::cmp::Ordering::Equal => 0,
                std::cmp::Ordering::Greater => 1,
            }
        }
        2 | 4 => {
            let (x, y) = (a >> 4, b >> 4);
            (x > y) as i64 - (x < y) as i64
        }
        3 => {
            // funs: arbitrary but consistent (address order)
            (a > b) as i64 - (a < b) as i64
        }
        6 => unsafe {
            // maps: size, then keys pairwise, then values pairwise
            let (pa, pb) = (a as *const u64, b as *const u64);
            let (na, nb) = ((*pa >> 8) as usize, (*pb >> 8) as usize);
            if na != nb {
                return if na < nb { -1 } else { 1 };
            }
            for i in 0..na {
                let c = mana_rt_compare(*pa.add(1 + i), *pb.add(1 + i));
                if c != 0 {
                    return c;
                }
            }
            for i in 0..na {
                let c = mana_rt_compare(*pa.add(1 + na + i), *pb.add(1 + na + i));
                if c != 0 {
                    return c;
                }
            }
            0
        },
        5 => unsafe {
            // tuples: size first, then elements
            let (pa, pb) = (a as *const u64, b as *const u64);
            let (na, nb) = ((*pa >> 8) as usize, (*pb >> 8) as usize);
            if na != nb {
                return if na < nb { -1 } else { 1 };
            }
            for i in 0..na {
                let c = mana_rt_compare(*pa.add(1 + i), *pb.add(1 + i));
                if c != 0 {
                    return c;
                }
            }
            0
        },
        9 => {
            // binaries: byte-lexicographic, prefix is smaller
            let (xa, xb) = (bin_bytes(a), bin_bytes(b));
            match xa.cmp(xb) {
                std::cmp::Ordering::Less => -1,
                std::cmp::Ordering::Equal => 0,
                std::cmp::Ordering::Greater => 1,
            }
        }
        8 => unsafe {
            // lists: heads recursively, tails iteratively
            let (mut x, mut y) = (a, b);
            loop {
                let (px, py) = ((x & !TAG_MASK) as *const u64, (y & !TAG_MASK) as *const u64);
                let c = mana_rt_compare(*px, *py);
                if c != 0 {
                    return c;
                }
                x = *px.add(1);
                y = *py.add(1);
                if x == y {
                    return 0;
                }
                let (tx, ty) = (x & TAG_MASK == TAG_CONS, y & TAG_MASK == TAG_CONS);
                match (tx, ty) {
                    (true, true) => continue,
                    // improper/ended tails: fall back to general compare
                    _ => return mana_rt_compare(x, y),
                }
            }
        },
        _ => 0,
    }
}

/// Exact equality (`=:=`): like compare == 0, but 1 =:= 1.0 is false.
#[no_mangle]
pub extern "C" fn mana_rt_eq_exact(a: u64, b: u64) -> i64 {
    if a == b {
        return 1;
    }
    let (ta, tb) = (a & TAG_MASK, b & TAG_MASK);
    if ta != tb {
        return 0; // exact: int never equals float (different tags)
    }
    match ta {
        TAG_SMALL | TAG_ATOM | TAG_PID => 0, // immediates: raw inequality is final
        _ if a == NIL || b == NIL => 0,
        TAG_CONS => unsafe {
            let (mut x, mut y) = (a, b);
            loop {
                let (px, py) = ((x & !TAG_MASK) as *const u64, (y & !TAG_MASK) as *const u64);
                if mana_rt_eq_exact(*px, *py) == 0 {
                    return 0;
                }
                x = *px.add(1);
                y = *py.add(1);
                if x == y {
                    return 1;
                }
                if x & TAG_MASK != TAG_CONS || y & TAG_MASK != TAG_CONS {
                    return mana_rt_eq_exact(x, y);
                }
            }
        },
        TAG_BOXED => unsafe {
            let (pa, pb) = (a as *const u64, b as *const u64);
            let (ha, hb) = (*pa, *pb);
            // bin kinds first: a view and a plain binary with equal bytes
            // are =:= even though their headers differ, so the header
            // fast-reject below must not see them
            let bin_kind = |h: u64| matches!(h & 0xff, KIND_BIN | KIND_SUBBIN);
            if bin_kind(ha) || bin_kind(hb) {
                return (bin_kind(ha) && bin_kind(hb) && bin_bytes(a) == bin_bytes(b)) as i64;
            }
            if ha != hb {
                return 0;
            }
            match ha & 0xff {
                KIND_FLOAT => (*pa.add(1) == *pb.add(1)) as i64,
                KIND_TUPLE => {
                    for i in 0..(ha >> 8) as usize {
                        if mana_rt_eq_exact(*pa.add(1 + i), *pb.add(1 + i)) == 0 {
                            return 0;
                        }
                    }
                    1
                }
                KIND_MAP => {
                    for i in 0..2 * (ha >> 8) as usize {
                        if mana_rt_eq_exact(*pa.add(1 + i), *pb.add(1 + i)) == 0 {
                            return 0;
                        }
                    }
                    1
                }
                KIND_BIGNUM => {
                    // headers equal ⇒ same sign and limb count
                    for i in 0..(ha >> 9) as usize {
                        if *pa.add(1 + i) != *pb.add(1 + i) {
                            return 0;
                        }
                    }
                    1
                }
                _ => 0, // funs: identity only (raw-equal handled above)
            }
        },
        _ => 0,
    }
}

/// Raise-site notifier (MANA_DEBUG_RAISE): names the raising function and
/// prints the reason term — the debugging stand-in for stacktraces.
#[no_mangle]
pub extern "C" fn mana_rt_note_raise(msg: *const u8, len: u64, reason: u64) {
    if std::env::var_os("MANA_DEBUG_RAISE").is_some() {
        let m = unsafe { std::slice::from_raw_parts(msg, len as usize) };
        let mut r = String::new();
        write_term(reason, &mut r);
        eprintln!("mana: raise in {}: {}", String::from_utf8_lossy(m), r);
    }
}

/// Inline badarg raise notifier (MANA_DEBUG_BADARG).
#[no_mangle]
pub extern "C" fn mana_rt_note_badarg(msg: *const u8, len: u64) {
    if std::env::var_os("MANA_DEBUG_BADARG").is_some() {
        let m = unsafe { std::slice::from_raw_parts(msg, len as usize) };
        eprintln!("mana: badarg raised in {}", String::from_utf8_lossy(m));
    }
}

/// A stubbed (unsupported-construct) function was actually called.
#[no_mangle]
pub extern "C" fn mana_rt_unsupported(msg: *const u8, len: u64) -> ! {
    let m = unsafe { std::slice::from_raw_parts(msg, len as usize) };
    eprintln!(
        "mana: reached an unsupported construct: {}",
        String::from_utf8_lossy(m)
    );
    std::process::exit(1)
}

/// Set exc and return the sentinel — the raising-BIF convention: codegen
/// treats these helpers exactly like may-raise calls.
fn raise_badarg(ctx: &mut ProcCtx) -> u64 {
    if std::env::var_os("MANA_DEBUG_BADARG").is_some() {
        eprintln!(
            "mana: badarg raised at:\n{}",
            std::backtrace::Backtrace::force_capture()
        );
    }
    ctx.exc_class = atom_error();
    ctx.exc_reason = known().badarg;
    EXC_SENTINEL
}

fn atom_error() -> u64 {
    known().error_a
}

/// Allocate in this scheduler's nursery (falls back to the slow path).
fn alloc_nursery(ctx: &mut ProcCtx, words: usize) -> *mut u64 {
    unsafe {
        if ctx.heap_top.add(words) <= ctx.heap_end {
            let p = ctx.heap_top;
            ctx.heap_top = ctx.heap_top.add(words);
            p
        } else {
            mana_rt_alloc_slow(ctx, words as u64)
        }
    }
}

/// erlang:setelement/3 (1-based index).
#[no_mangle]
pub extern "C" fn mana_rt_setelement(ctx: *mut ProcCtx, i: u64, tup: u64, v: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if i & TAG_MASK != TAG_SMALL || tup & TAG_MASK != TAG_BOXED || tup == 0 {
        return raise_badarg(ctx);
    }
    let idx = (i as i64) >> 3;
    unsafe {
        let p = tup as *const u64;
        let header = *p;
        if header & 0xff != KIND_TUPLE {
            return raise_badarg(ctx);
        }
        let n = (header >> 8) as i64;
        if idx < 1 || idx > n {
            return raise_badarg(ctx);
        }
        // root the inputs across a potential collection
        let frame = [0u64, 2, tup, v];
        let saved = ctx.roots_head;
        let mut fr = frame;
        fr[0] = saved;
        ctx.roots_head = fr.as_ptr() as u64;
        let newp = alloc_nursery(ctx, 1 + n as usize);
        ctx.roots_head = saved;
        let (tup, v) = (fr[2], fr[3]);
        std::ptr::copy_nonoverlapping(tup as *const u64, newp, 1 + n as usize);
        *newp.add(idx as usize) = v;
        newp as u64
    }
}

/// erlang:length/1.
#[no_mangle]
pub extern "C" fn mana_rt_length(ctx: *mut ProcCtx, list: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut n: i64 = 0;
    let mut t = list;
    loop {
        if t == NIL {
            return ((n as u64) << 3) | TAG_SMALL;
        }
        if t & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        n += 1;
        t = unsafe { *((t & !TAG_MASK) as *const u64).add(1) };
    }
}

/// erlang:'++'/2 — copy the left list onto the right.
#[no_mangle]
pub extern "C" fn mana_rt_append(ctx: *mut ProcCtx, left: u64, right: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if left == NIL {
        return right;
    }
    // count (and validate) left
    let mut n = 0usize;
    let mut t = left;
    while t != NIL {
        if t & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        n += 1;
        t = unsafe { *((t & !TAG_MASK) as *const u64).add(1) };
    }
    // root left/right across allocation
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, left, right];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let block = alloc_nursery(ctx, 2 * n);
    ctx.roots_head = saved;
    let (left, right) = (fr[2], fr[3]);
    unsafe {
        let mut src = left;
        let mut out = block;
        for i in 0..n {
            let p = (src & !TAG_MASK) as *const u64;
            *out = *p;
            let next = out.add(2);
            *out.add(1) = if i == n - 1 {
                right
            } else {
                next as u64 | TAG_CONS
            };
            src = *p.add(1);
            out = next;
        }
    }
    block as u64 | TAG_CONS
}

/// erlang:'--'/2 (quadratic, like small-input BEAM).
#[no_mangle]
pub extern "C" fn mana_rt_subtract(ctx: *mut ProcCtx, left: u64, right: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    // collect right into a scratch vec
    let mut rem: Vec<u64> = Vec::new();
    let mut t = right;
    while t != NIL {
        if t & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (t & !TAG_MASK) as *const u64;
        unsafe {
            rem.push(*p);
            t = *p.add(1);
        }
    }
    // collect kept elements of left
    let mut kept: Vec<u64> = Vec::new();
    let mut t = left;
    while t != NIL {
        if t & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (t & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if let Some(pos) = rem.iter().position(|&r| mana_rt_compare(r, h) == 0) {
            rem.remove(pos);
        } else {
            kept.push(h);
        }
        t = unsafe { *p.add(1) };
    }
    if kept.is_empty() {
        return NIL;
    }
    // scratch vecs are not GC roots: allocate first, then build (kept holds
    // terms that could move if alloc collects!) — root them via a frame on
    // the Rust stack sized dynamically: simplest is one allocation for the
    // whole spine, done before any element is re-read... but kept already
    // holds the terms as values. Rooting: temporary frame over the vec.
    let saved = ctx.roots_head;
    let mut fr: Vec<u64> = Vec::with_capacity(2 + kept.len());
    fr.push(saved);
    fr.push(kept.len() as u64);
    fr.extend_from_slice(&kept);
    ctx.roots_head = fr.as_ptr() as u64;
    let block = alloc_nursery(ctx, 2 * kept.len());
    ctx.roots_head = saved;
    unsafe {
        for (i, _) in kept.iter().enumerate() {
            let cell = block.add(2 * i);
            *cell = fr[2 + i];
            *cell.add(1) = if i == kept.len() - 1 {
                NIL
            } else {
                cell.add(2) as u64 | TAG_CONS
            };
        }
    }
    block as u64 | TAG_CONS
}

// ---------------------------------------------------------------------------
// maps (flatmap)

/// Canonical key order: term order, with exactness tiebreak so that keys
/// like 1 and 1.0 remain distinct (int sorts before float).
fn map_key_cmp(a: u64, b: u64) -> std::cmp::Ordering {
    let c = mana_rt_compare(a, b);
    if c != 0 {
        return c.cmp(&0);
    }
    if a == b {
        return std::cmp::Ordering::Equal;
    }
    // compare == 0 with distinct bits: a binary's byte compare was already
    // exact — only numbers (1 vs 1.0), possibly nested in containers, need
    // the exactness tiebreak
    if a & TAG_MASK == TAG_BOXED
        && matches!(unsafe { *(a as *const u64) } & 0xff, KIND_BIN | KIND_SUBBIN)
    {
        return std::cmp::Ordering::Equal;
    }
    if mana_rt_eq_exact(a, b) == 1 {
        return std::cmp::Ordering::Equal;
    }
    // numerically equal but exact-distinct: small int first
    if a & TAG_MASK == TAG_SMALL {
        std::cmp::Ordering::Less
    } else {
        std::cmp::Ordering::Greater
    }
}

fn map_parts(m: u64) -> Option<(*mut u64, usize)> {
    if m & TAG_MASK != TAG_BOXED || m == 0 {
        return None;
    }
    let p = m as *mut u64;
    let header = unsafe { *p };
    if header & 0xff != KIND_MAP {
        return None;
    }
    Some((p, (header >> 8) as usize))
}

/// Find a key (exact match) via binary search; returns the pair index.
fn map_index(p: *const u64, n: usize, key: u64) -> Result<usize, usize> {
    let keys = unsafe { std::slice::from_raw_parts(p.add(1), n) };
    // Equal atoms are pointer-identical (linkonce_odr globals) and equal
    // smalls bit-identical, so for the small maps that dominate (struct
    // fields, changesets) a raw-u64 scan resolves the hit without any
    // generic compares. Misses (and boxed keys) fall to binary search,
    // which also supplies the insertion position for put.
    if n <= 16 {
        if let Some(i) = keys.iter().position(|&k| k == key) {
            return Ok(i);
        }
    }
    keys.binary_search_by(|&k| map_key_cmp(k, key))
}

/// Normalize a freshly built map (unsorted pairs, not yet published):
/// sort by key, deduplicate (last write wins). Shrinks the header size on
/// dedupe; trailing words become unreachable garbage (worklist GC).
#[no_mangle]
pub extern "C" fn mana_rt_map_norm(m: u64) -> u64 {
    let Some((p, n)) = map_parts(m) else { return m };
    unsafe {
        let mut pairs: Vec<(u64, u64)> = (0..n).map(|i| (*p.add(1 + i), *p.add(1 + n + i))).collect();
        // stable sort keeps the LAST duplicate later in the run
        pairs.sort_by(|a, b| map_key_cmp(a.0, b.0));
        let mut out: Vec<(u64, u64)> = Vec::with_capacity(n);
        for pair in pairs {
            if let Some(last) = out.last_mut() {
                if map_key_cmp(last.0, pair.0) == std::cmp::Ordering::Equal {
                    *last = pair; // last wins
                    continue;
                }
            }
            out.push(pair);
        }
        let m2 = out.len();
        *p = ((m2 as u64) << 8) | KIND_MAP;
        for (i, (k, v)) in out.iter().enumerate() {
            *p.add(1 + i) = *k;
            *p.add(1 + m2 + i) = *v;
        }
    }
    m
}

/// Pattern-match lookup: value, or the exception sentinel for miss /
/// non-map. Non-allocating — safe inside match contexts.
#[no_mangle]
pub extern "C" fn mana_rt_map_pat_get(m: u64, key: u64) -> u64 {
    let Some((p, n)) = map_parts(m) else {
        return EXC_SENTINEL;
    };
    match map_index(p, n, key) {
        Ok(i) => unsafe { *p.add(1 + n + i) },
        Err(_) => EXC_SENTINEL,
    }
}

fn raise_map_err(ctx: &mut ProcCtx, tag_is_badmap: bool, culprit: u64) -> u64 {
    // {badmap, M} / {badkey, K} with class error
    let tag = if tag_is_badmap { "badmap" } else { "badkey" };
    // eternal pair (never moved; GC scans fields)
    let p = alloc_space(3);
    ctx.global.eternal.lock().push((p as usize, false));
    unsafe {
        *p = (2 << 8) | KIND_TUPLE;
        *p.add(1) = atom_by_name(tag);
        *p.add(2) = culprit;
    }
    ctx.exc_class = atom_error();
    ctx.exc_reason = p as u64;
    EXC_SENTINEL
}

/// badmap/badkey atoms: registered alongside the rest.
fn atom_by_name(name: &str) -> u64 {
    let k = known();
    match name {
        "badmap" => k.badmap,
        "badkey" => k.badkey,
        "value" => k.value,
        other => panic!("atom_by_name: '{}' is not registered", other),
    }
}

/// maps:put/3 — returns a new map (insert or replace).
#[no_mangle]
pub extern "C" fn mana_rt_map_put(ctx: *mut ProcCtx, key: u64, val: u64, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, n)) = map_parts(m) else {
        return raise_map_err(ctx, true, m);
    };
    // root inputs across allocation
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, key, val, m];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let newp = alloc_nursery(ctx, 1 + 2 * (n + 1));
    ctx.roots_head = saved;
    let (key, val, m) = (fr[2], fr[3], fr[4]);
    let (p, n) = map_parts(m).unwrap();
    unsafe {
        match map_index(p, n, key) {
            Ok(i) => {
                std::ptr::copy_nonoverlapping(p, newp, 1 + 2 * n);
                *newp.add(1 + n + i) = val;
            }
            Err(pos) => {
                *newp = (((n + 1) as u64) << 8) | KIND_MAP;
                // keys with insertion at pos
                for i in 0..pos {
                    *newp.add(1 + i) = *p.add(1 + i);
                    *newp.add(1 + (n + 1) + i) = *p.add(1 + n + i);
                }
                *newp.add(1 + pos) = key;
                *newp.add(1 + (n + 1) + pos) = val;
                for i in pos..n {
                    *newp.add(1 + i + 1) = *p.add(1 + i);
                    *newp.add(1 + (n + 1) + i + 1) = *p.add(1 + n + i);
                }
            }
        }
    }
    newp as u64
}

/// maps:get/2 — badkey/badmap on miss.
#[no_mangle]
pub extern "C" fn mana_rt_map_get(ctx: *mut ProcCtx, key: u64, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((p, n)) = map_parts(m) else {
        return raise_map_err(ctx, true, m);
    };
    match map_index(p, n, key) {
        Ok(i) => unsafe { *p.add(1 + n + i) },
        Err(_) => raise_map_err(ctx, false, key),
    }
}

/// maps:remove/2.
#[no_mangle]
pub extern "C" fn mana_rt_map_remove(ctx: *mut ProcCtx, key: u64, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((p0, n)) = map_parts(m) else {
        return raise_map_err(ctx, true, m);
    };
    let Ok(idx) = map_index(p0, n, key) else {
        return m;
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, m];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let newp = alloc_nursery(ctx, 1 + 2 * (n - 1));
    ctx.roots_head = saved;
    let m = fr[2];
    let (p, n) = map_parts(m).unwrap();
    unsafe {
        *newp = (((n - 1) as u64) << 8) | KIND_MAP;
        let mut j = 0;
        for i in 0..n {
            if i == idx {
                continue;
            }
            *newp.add(1 + j) = *p.add(1 + i);
            *newp.add(1 + (n - 1) + j) = *p.add(1 + n + i);
            j += 1;
        }
    }
    newp as u64
}

/// maps:to_list/1 — [{K, V}] in key order.
#[no_mangle]
pub extern "C" fn mana_rt_map_to_list(ctx: *mut ProcCtx, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, n)) = map_parts(m) else {
        return raise_map_err(ctx, true, m);
    };
    if n == 0 {
        return NIL;
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, m];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    // 2 words per cons + 3 per {K,V} tuple
    let block = alloc_nursery(ctx, n * 5);
    ctx.roots_head = saved;
    let m = fr[2];
    let (p, n) = map_parts(m).unwrap();
    unsafe {
        for i in 0..n {
            let tup = block.add(5 * i);
            *tup = (2 << 8) | KIND_TUPLE;
            *tup.add(1) = *p.add(1 + i);
            *tup.add(2) = *p.add(1 + n + i);
            let cell = tup.add(3);
            *cell = tup as u64;
            *cell.add(1) = if i == n - 1 {
                NIL
            } else {
                block.add(5 * (i + 1) + 3) as u64 | TAG_CONS
            };
        }
    }
    unsafe { block.add(3) as u64 | TAG_CONS }
}

/// maps:from_list/1 — builds then normalizes.
#[no_mangle]
pub extern "C" fn mana_rt_map_from_list(ctx: *mut ProcCtx, list: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    // count and validate [{K,V}]
    let mut n = 0usize;
    let mut t = list;
    while t != NIL {
        if t & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (t & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK != TAG_BOXED || h == 0 {
            return raise_badarg(ctx);
        }
        let hh = unsafe { *(h as *const u64) };
        if hh & 0xff != KIND_TUPLE || (hh >> 8) != 2 {
            return raise_badarg(ctx);
        }
        n += 1;
        t = unsafe { *p.add(1) };
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, list];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let newp = alloc_nursery(ctx, 1 + 2 * n);
    ctx.roots_head = saved;
    let list = fr[2];
    unsafe {
        *newp = ((n as u64) << 8) | KIND_MAP;
        let mut t = list;
        let mut i = 0;
        while t != NIL {
            let p = (t & !TAG_MASK) as *const u64;
            let tup = *p as *const u64;
            *newp.add(1 + i) = *tup.add(1);
            *newp.add(1 + n + i) = *tup.add(2);
            i += 1;
            t = *p.add(1);
        }
    }
    mana_rt_map_norm(newp as u64)
}

/// `~{K := V | M}~` update: key must exist (Elixir `%{m | k: v}`).
#[no_mangle]
pub extern "C" fn mana_rt_map_update_exact(ctx: *mut ProcCtx, key: u64, val: u64, m: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    let Some((p, n)) = map_parts(m) else {
        return raise_map_err(ctxr, true, m);
    };
    if map_index(p, n, key).is_err() {
        return raise_map_err(ctxr, false, key);
    }
    mana_rt_map_put(ctx, key, val, m)
}

/// maps:is_key/2 → true/false atoms (badmap on non-map).
#[no_mangle]
pub extern "C" fn mana_rt_map_is_key(ctx: *mut ProcCtx, key: u64, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((p, n)) = map_parts(m) else {
        return raise_map_err(ctx, true, m);
    };
    if map_index(p, n, key).is_ok() {
        known().true_a
    } else {
        known().false_a
    }
}

/// maps:merge/2 — values from the second map win.
#[no_mangle]
pub extern "C" fn mana_rt_map_merge(ctx: *mut ProcCtx, m1: u64, m2: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, n1)) = map_parts(m1) else {
        return raise_map_err(ctx, true, m1);
    };
    let Some((_, n2)) = map_parts(m2) else {
        return raise_map_err(ctx, true, m2);
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, m1, m2];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let newp = alloc_nursery(ctx, 1 + 2 * (n1 + n2));
    ctx.roots_head = saved;
    let (m1, m2) = (fr[2], fr[3]);
    let (p1, n1) = map_parts(m1).unwrap();
    let (p2, n2) = map_parts(m2).unwrap();
    unsafe {
        // merge two sorted pair sequences; m2 wins ties
        let (mut i, mut j, mut o) = (0usize, 0usize, 0usize);
        let total = n1 + n2;
        let put = |newp: *mut u64, o: usize, k: u64, v: u64| {
            *newp.add(1 + o) = k;
            *newp.add(1 + total + o) = v;
        };
        while i < n1 && j < n2 {
            let (k1, k2) = (*p1.add(1 + i), *p2.add(1 + j));
            match map_key_cmp(k1, k2) {
                std::cmp::Ordering::Less => {
                    put(newp, o, k1, *p1.add(1 + n1 + i));
                    i += 1;
                }
                std::cmp::Ordering::Greater => {
                    put(newp, o, k2, *p2.add(1 + n2 + j));
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    put(newp, o, k2, *p2.add(1 + n2 + j));
                    i += 1;
                    j += 1;
                }
            }
            o += 1;
        }
        while i < n1 {
            put(newp, o, *p1.add(1 + i), *p1.add(1 + n1 + i));
            i += 1;
            o += 1;
        }
        while j < n2 {
            put(newp, o, *p2.add(1 + j), *p2.add(1 + n2 + j));
            j += 1;
            o += 1;
        }
        // compact values if o < total (ties merged): values were written at
        // stride `total`; rewrite them at stride `o`
        if o < total {
            for idx in 0..o {
                let v = *newp.add(1 + total + idx);
                *newp.add(1 + o + idx) = v;
            }
        }
        *newp = ((o as u64) << 8) | KIND_MAP;
    }
    newp as u64
}

// ---------------------------------------------------------------------------
// term output

/// `erlang:display/1` — print a term followed by newline.
#[no_mangle]
pub extern "C" fn mana_rt_display(term: u64) {
    let mut out = String::new();
    write_term(term, &mut out);
    out.push('\n');
    let _ = std::io::stdout().write_all(out.as_bytes());
}

/// An exception unwound past the entry function (uncaught).
#[no_mangle]
pub extern "C" fn mana_rt_uncaught(ctx: *mut ProcCtx) -> ! {
    let ctx = unsafe { &*ctx };
    let mut class = String::new();
    let mut reason = String::new();
    write_term(ctx.exc_class, &mut class);
    write_term(ctx.exc_reason, &mut reason);
    eprintln!("** exception {}: {}", class, reason);
    std::process::exit(1);
}

// ---------------------------------------------------------------------------
// binaries (byte-aligned; sub-byte bitstrings are TODO(bitstring))

fn bin_parts(t: u64) -> Option<(*const u8, usize)> {
    if t & TAG_MASK != TAG_BOXED || t == 0 {
        return None;
    }
    let p = t as *const u64;
    let header = unsafe { *p };
    match header & 0xff {
        KIND_BIN => Some((unsafe { p.add(1) } as *const u8, (header >> 8) as usize)),
        // view: recompute from the parent TERM every call — the parent
        // moves under GC, so the data pointer must never be cached
        KIND_SUBBIN => {
            let parent = unsafe { *p.add(1) };
            let off = unsafe { *p.add(2) } as usize;
            debug_assert!(
                parent & TAG_MASK == TAG_BOXED
                    && unsafe { *(parent as *const u64) } & 0xff == KIND_BIN,
                "sub-binary parent must be a root KIND_BIN"
            );
            let pp = parent as *const u64;
            Some((
                unsafe { (pp.add(1) as *const u8).add(off) },
                (header >> 8) as usize,
            ))
        }
        _ => None,
    }
}

fn bin_bytes(t: u64) -> &'static [u8] {
    match bin_parts(t) {
        Some((p, n)) => unsafe { std::slice::from_raw_parts(p, n) },
        None => &[],
    }
}

/// Allocate an uninitialized binary of `bytes` in the nursery. Padding in
/// the last data word is zeroed so word-granular copies stay deterministic.
/// Caller must have rooted every live term (may GC).
fn alloc_bin(ctx: &mut ProcCtx, bytes: usize) -> *mut u64 {
    let words = 1 + (bytes + 7) / 8;
    let p = alloc_nursery(ctx, words);
    unsafe {
        *p = ((bytes as u64) << 8) | KIND_BIN;
        if bytes % 8 != 0 {
            // zero the final data word's padding (never the header)
            *p.add(words - 1) = 0;
        }
    }
    p
}

/// Codegen entry: allocate a zero-padded binary; construction writers fill
/// it in. All live terms must be rooted by the caller (may GC).
#[no_mangle]
pub extern "C" fn mana_rt_bin_alloc(ctx: *mut ProcCtx, nbytes: u64) -> u64 {
    alloc_bin(unsafe { &mut *ctx }, nbytes as usize) as u64
}

/// Raise-path construction: eternal (malloc) binary, registered so majors
/// keep it alive; never moves, so no rooting needed.
#[no_mangle]
pub extern "C" fn mana_rt_bin_alloc_eternal(ctx: *mut ProcCtx, nbytes: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let bytes = nbytes as usize;
    let words = 1 + (bytes + 7) / 8;
    let p = alloc_space(words);
    ctx.global.eternal.lock().push((p as usize, false));
    unsafe {
        *p = ((bytes as u64) << 8) | KIND_BIN;
        if words > 1 {
            *p.add(words - 1) = 0;
        }
    }
    p as u64
}

/// Pattern preflight: is `t` a binary of exactly `n` bytes (`at_least` = 0)
/// or at least `n` bytes (`at_least` = 1)?
#[no_mangle]
pub extern "C" fn mana_rt_bin_len_check(t: u64, n: u64, at_least: u64) -> u64 {
    match bin_parts(t) {
        Some((_, len)) => {
            (if at_least != 0 { len >= n as usize } else { len == n as usize }) as u64
        }
        None => 0,
    }
}

/// Pattern extraction of an integer segment. flags: bit0 little-endian,
/// bit1 signed. Returns the sentinel for out-of-bounds / non-binary —
/// pattern-match failure, NOT an exception. Non-allocating.
#[no_mangle]
pub extern "C" fn mana_rt_bin_read_int(bin: u64, off: u64, nbytes: u64, flags: u64) -> u64 {
    let Some((p, len)) = bin_parts(bin) else {
        return EXC_SENTINEL;
    };
    let (off, nbytes) = (off as usize, nbytes as usize);
    if off + nbytes > len {
        return EXC_SENTINEL;
    }
    if nbytes > 8 {
        // dynamic sizes beyond 64 bits would need bignums — fail the match
        // (TODO(bignum-segments): BEAM would succeed)
        return EXC_SENTINEL;
    }
    let mut v: u64 = 0;
    unsafe {
        if flags & 1 != 0 {
            for i in (0..nbytes).rev() {
                v = (v << 8) | *p.add(off + i) as u64;
            }
        } else {
            for i in 0..nbytes {
                v = (v << 8) | *p.add(off + i) as u64;
            }
        }
    }
    let sv = if flags & 2 != 0 && nbytes > 0 {
        let shift = 64 - 8 * nbytes.min(8) as u32;
        if shift > 0 { ((v << shift) as i64) >> shift } else { v as i64 }
    } else {
        v as i64
    };
    // small ints hold 61 bits; 64-bit segments with larger values need
    // bignums we don't have
    if nbytes >= 8 && (sv >> 60 != 0 && sv >> 60 != -1) {
        eprintln!("mana: TODO(bignum-segments): 64-bit binary segment value out of small-int range");
        std::process::abort();
    }
    ((sv << 3) as u64) | TAG_SMALL
}

/// Pattern extraction of a utf8 segment: decode one code point at `off`.
/// Returns -1 for fail, else (width_bytes << 32) | code_point.
#[no_mangle]
pub extern "C" fn mana_rt_bin_read_utf8(bin: u64, off: u64) -> i64 {
    let Some((p, len)) = bin_parts(bin) else {
        return -1;
    };
    let off = off as usize;
    if off >= len {
        return -1;
    }
    let bytes = unsafe { std::slice::from_raw_parts(p.add(off), len - off) };
    let width = match bytes[0] {
        0x00..=0x7f => 1,
        0xc0..=0xdf => 2,
        0xe0..=0xef => 3,
        0xf0..=0xf7 => 4,
        _ => return -1,
    };
    if bytes.len() < width {
        return -1;
    }
    match std::str::from_utf8(&bytes[..width]) {
        Ok(s) => {
            let cp = s.chars().next().unwrap() as u32;
            ((width as i64) << 32) | cp as i64
        }
        Err(_) => -1,
    }
}

/// Construction: utf8 width of a code point term (0 = invalid → badarg).
#[no_mangle]
pub extern "C" fn mana_rt_utf8_width(cp: u64) -> u64 {
    if cp & TAG_MASK != TAG_SMALL {
        return 0;
    }
    u32::try_from(cp as i64 >> 3)
        .ok()
        .and_then(char::from_u32)
        .map(|c| c.len_utf8() as u64)
        .unwrap_or(0)
}

/// Construction writer: utf8-encode a code point; returns bytes written
/// (the width was already validated by mana_rt_utf8_width).
#[no_mangle]
pub extern "C" fn mana_rt_bin_write_utf8(bin: u64, off: u64, cp: u64) -> u64 {
    let c = char::from_u32((cp as i64 >> 3) as u32).unwrap();
    let mut buf = [0u8; 4];
    let s = c.encode_utf8(&mut buf);
    let (p, _) = bin_parts(bin).unwrap();
    unsafe {
        std::ptr::copy_nonoverlapping(s.as_ptr(), (p as *mut u8).add(off as usize), s.len());
    }
    s.len() as u64
}

/// Pattern extraction of a binary segment: `len < 0` means the whole rest.
/// Sentinel = match failure. Small slices copy (BEAM's heap-binary
/// heuristic — cheap and they don't pin the parent); larger ones become
/// zero-copy KIND_SUBBIN views over the ROOT binary (slicing a view folds
/// offsets, so views never chain).
#[no_mangle]
pub extern "C" fn mana_rt_bin_slice(ctx: *mut ProcCtx, bin: u64, off: u64, len: i64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, total)) = bin_parts(bin) else {
        return EXC_SENTINEL;
    };
    let off = off as usize;
    if off > total {
        return EXC_SENTINEL;
    }
    let len = if len < 0 { total - off } else { len as usize };
    if off + len > total {
        return EXC_SENTINEL;
    }
    if len <= 64 {
        let saved = ctx.roots_head;
        let mut fr = [0u64, 1, bin];
        fr[0] = saved;
        ctx.roots_head = fr.as_ptr() as u64;
        let newp = alloc_bin(ctx, len);
        ctx.roots_head = saved;
        let (p, _) = bin_parts(fr[2]).unwrap();
        unsafe {
            std::ptr::copy_nonoverlapping(p.add(off), newp.add(1) as *mut u8, len);
        }
        return newp as u64;
    }
    let (parent, abs_off) = {
        let p = bin as *const u64;
        if unsafe { *p } & 0xff == KIND_SUBBIN {
            (unsafe { *p.add(1) }, unsafe { *p.add(2) } as usize + off)
        } else {
            (bin, off)
        }
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, parent];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let vp = alloc_nursery(ctx, 3);
    ctx.roots_head = saved;
    unsafe {
        *vp = ((len as u64) << 8) | KIND_SUBBIN;
        *vp.add(1) = fr[2];
        *vp.add(2) = abs_off as u64;
    }
    vp as u64
}

/// Construction writer: constant segment bytes from a static array.
#[no_mangle]
pub extern "C" fn mana_rt_bin_write_bytes(bin: u64, off: u64, ptr: *const u8, len: u64) {
    let (p, _) = bin_parts(bin).unwrap();
    unsafe {
        std::ptr::copy_nonoverlapping(ptr, (p as *mut u8).add(off as usize), len as usize);
    }
}

/// Pattern check: do the bytes at `off` equal a constant array? 0 for
/// non-binary / out of bounds / mismatch. Non-allocating.
#[no_mangle]
pub extern "C" fn mana_rt_bin_match_bytes(bin: u64, off: u64, ptr: *const u8, len: u64) -> u64 {
    let Some((p, total)) = bin_parts(bin) else {
        return 0;
    };
    let (off, len) = (off as usize, len as usize);
    if off + len > total {
        return 0;
    }
    let a = unsafe { std::slice::from_raw_parts(p.add(off), len) };
    let b = unsafe { std::slice::from_raw_parts(ptr, len) };
    (a == b) as u64
}

/// Construction writer: store an integer segment (truncating, like BEAM).
/// Non-allocating; badarg if the value is not a small int.
#[no_mangle]
pub extern "C" fn mana_rt_bin_write_int(
    ctx: *mut ProcCtx,
    bin: u64,
    off: u64,
    val: u64,
    nbytes: u64,
    little: u64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    // BEAM truncates integer segments to the low bits — bignums included
    let v: u64 = if val & TAG_MASK == TAG_SMALL {
        (val as i64 >> 3) as u64
    } else if let Some((neg, mag)) = bignum_parts(val) {
        // low 64 bits, two's complement for negatives (nbytes <= 8)
        let lo = mag[0];
        if neg { lo.wrapping_neg() } else { lo }
    } else {
        return raise_badarg(ctx);
    };
    let (p, _) = bin_parts(bin).unwrap();
    let (off, nbytes) = (off as usize, nbytes as usize);
    unsafe {
        let p = p as *mut u8;
        for i in 0..nbytes {
            let byte = (v >> (8 * if little != 0 { i } else { nbytes - 1 - i })) as u8;
            *p.add(off + i) = byte;
        }
    }
    0
}

/// Construction writer: splice a binary. `len < 0` copies all of it; a
/// non-negative len copies the first len bytes (badarg if src is shorter,
/// like BEAM's fixed-size binary segments). Non-allocating.
#[no_mangle]
pub extern "C" fn mana_rt_bin_write_bin(
    ctx: *mut ProcCtx,
    bin: u64,
    off: u64,
    src: u64,
    len: i64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((sp, sn)) = bin_parts(src) else {
        return raise_badarg(ctx);
    };
    let n = if len < 0 {
        sn
    } else if (len as usize) <= sn {
        len as usize
    } else {
        return raise_badarg(ctx);
    };
    let (p, _) = bin_parts(bin).unwrap();
    unsafe {
        std::ptr::copy_nonoverlapping(sp, (p as *mut u8).add(off as usize), n);
    }
    0
}

/// erlang:byte_size/1 (raising convention).
#[no_mangle]
pub extern "C" fn mana_rt_byte_size(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    match bin_parts(t) {
        Some((_, n)) => ((n as u64) << 3) | TAG_SMALL,
        None => raise_badarg(ctx),
    }
}

/// erlang:binary_part/3 — negative length reaches backwards (BEAM).
#[no_mangle]
pub extern "C" fn mana_rt_binary_part(ctx: *mut ProcCtx, bin: u64, pos: u64, len: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, total)) = bin_parts(bin) else {
        return raise_badarg(ctx);
    };
    if pos & TAG_MASK != TAG_SMALL || len & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let (pos, len) = (pos as i64 >> 3, len as i64 >> 3);
    let (start, n) = if len < 0 { (pos + len, -len) } else { (pos, len) };
    if start < 0 || n < 0 || (start + n) as usize > total || start as usize > total {
        return raise_badarg(ctx);
    }
    let v = mana_rt_bin_slice(ctx, bin, start as u64, n);
    if v == EXC_SENTINEL {
        return raise_badarg(ctx);
    }
    v
}

/// erlang:list_to_tuple/1.
#[no_mangle]
pub extern "C" fn mana_rt_list_to_tuple(ctx: *mut ProcCtx, l: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    // count first (validates properness)
    let mut n = 0usize;
    let mut cur = l;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        n += 1;
        cur = unsafe { *((cur & !TAG_MASK) as *const u64).add(1) };
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, l];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let t = alloc_nursery(ctx, 1 + n);
    ctx.roots_head = saved;
    unsafe {
        *t = ((n as u64) << 8) | KIND_TUPLE;
        let mut cur = fr[2];
        for i in 0..n {
            let p = (cur & !TAG_MASK) as *const u64;
            *t.add(1 + i) = *p;
            cur = *p.add(1);
        }
    }
    t as u64
}

/// erlang:tuple_to_list/1.
#[no_mangle]
pub extern "C" fn mana_rt_tuple_to_list(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let ok = t & TAG_MASK == TAG_BOXED
        && t != 0
        && unsafe { *(t as *const u64) } & 0xff == KIND_TUPLE;
    if !ok {
        return raise_badarg(ctx);
    }
    let n = (unsafe { *(t as *const u64) } >> 8) as usize;
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, t, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for i in (0..n).rev() {
        let cell = alloc_nursery(ctx, 2);
        let tp = fr[2] as *const u64;
        unsafe {
            *cell = *tp.add(1 + i);
            *cell.add(1) = fr[3];
        }
        fr[3] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[3]
}

/// erlang:split_binary/2 → {Prefix, Suffix}.
#[no_mangle]
pub extern "C" fn mana_rt_split_binary(ctx: *mut ProcCtx, bin: u64, pos: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, total)) = bin_parts(bin) else {
        return raise_badarg(ctx);
    };
    if pos & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let at = pos as i64 >> 3;
    if at < 0 || at as usize > total {
        return raise_badarg(ctx);
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, bin, 0, 0];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    fr[3] = mana_rt_bin_slice(ctx, fr[2], 0, at);
    fr[4] = mana_rt_bin_slice(ctx, fr[2], at as u64, -1);
    let t = alloc_nursery(ctx, 3);
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = fr[3];
        *t.add(2) = fr[4];
    }
    ctx.roots_head = saved;
    t as u64
}

/// erlang:binary_to_list/1.
#[no_mangle]
pub extern "C" fn mana_rt_binary_to_list(ctx: *mut ProcCtx, bin: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, n)) = bin_parts(bin) else {
        return raise_badarg(ctx);
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, bin, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for i in (0..n).rev() {
        let cell = alloc_nursery(ctx, 2);
        let (p, _) = bin_parts(fr[2]).unwrap();
        unsafe {
            *cell = ((*p.add(i) as u64) << 3) | TAG_SMALL;
            *cell.add(1) = fr[3];
        }
        fr[3] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[3]
}

/// Flatten an iolist (nested lists of bytes and binaries, binary tails
/// allowed) into `out`. Err = badarg.
fn iolist_flatten(t: u64, out: &mut Vec<u8>) -> Result<(), ()> {
    if let Some((p, n)) = bin_parts(t) {
        out.extend_from_slice(unsafe { std::slice::from_raw_parts(p, n) });
        return Ok(());
    }
    let mut cur = t;
    loop {
        if cur == NIL {
            return Ok(());
        }
        if cur & TAG_MASK != TAG_CONS {
            // a binary tail terminates an iolist
            if bin_parts(cur).is_some() {
                return iolist_flatten(cur, out);
            }
            return Err(());
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK == TAG_SMALL {
            let v = h as i64 >> 3;
            if !(0..=255).contains(&v) {
                return Err(());
            }
            out.push(v as u8);
        } else {
            iolist_flatten(h, out)?;
        }
        cur = unsafe { *p.add(1) };
    }
}

fn bytes_to_new_bin(ctx: &mut ProcCtx, bytes: &[u8]) -> u64 {
    // bytes are already copied out of the heap — nothing to root
    let p = alloc_bin(ctx, bytes.len());
    unsafe {
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), p.add(1) as *mut u8, bytes.len());
    }
    p as u64
}

/// IEEE CRC-32 (gzip's checksum), table-driven.
fn crc32(bytes: &[u8]) -> u32 {
    static TABLE: std::sync::OnceLock<[u32; 256]> = std::sync::OnceLock::new();
    let table = TABLE.get_or_init(|| {
        let mut t = [0u32; 256];
        for (i, e) in t.iter_mut().enumerate() {
            let mut c = i as u32;
            for _ in 0..8 {
                c = if c & 1 != 0 { 0xedb8_8320 ^ (c >> 1) } else { c >> 1 };
            }
            *e = c;
        }
        t
    });
    let mut c = 0xffff_ffffu32;
    for &b in bytes {
        c = table[((c ^ b as u32) & 0xff) as usize] ^ (c >> 8);
    }
    !c
}

/// zlib:gzip/1 — a real gzip container (RFC 1952) over DEFLATE-compressed
/// data (miniz_oxide). gunzip/1 inverts it and verifies the CRC32 + ISIZE
/// trailer.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_gzip(ctx: *mut ProcCtx, data: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut input = Vec::new();
    if iolist_flatten(data, &mut input).is_err() {
        return raise_badarg(ctx);
    }
    let body = miniz_oxide::deflate::compress_to_vec(&input, 6);
    let mut out = Vec::with_capacity(body.len() + 18);
    // header: magic, CM=8 (deflate), no flags, no mtime, XFL=0, OS=unknown
    out.extend_from_slice(&[0x1f, 0x8b, 0x08, 0x00, 0, 0, 0, 0, 0x00, 0xff]);
    out.extend_from_slice(&body);
    out.extend_from_slice(&crc32(&input).to_le_bytes());
    out.extend_from_slice(&(input.len() as u32).to_le_bytes());
    bytes_to_new_bin(ctx, &out)
}

/// zlib:gunzip/1 — parse a gzip container, inflate, verify CRC32 + ISIZE.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_gunzip(ctx: *mut ProcCtx, data: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut input = Vec::new();
    if iolist_flatten(data, &mut input).is_err() {
        return raise_badarg(ctx);
    }
    match gunzip_bytes(&input) {
        Some(out) => bytes_to_new_bin(ctx, &out),
        None => raise_badarg(ctx),
    }
}

fn gunzip_bytes(input: &[u8]) -> Option<Vec<u8>> {
    if input.len() < 18 || input[0] != 0x1f || input[1] != 0x8b || input[2] != 0x08 {
        return None;
    }
    let flg = input[3];
    let mut off = 10usize;
    if flg & 0x04 != 0 {
        // FEXTRA: 2-byte length then that many bytes
        if off + 2 > input.len() {
            return None;
        }
        let xlen = u16::from_le_bytes([input[off], input[off + 1]]) as usize;
        off += 2 + xlen;
    }
    if flg & 0x08 != 0 {
        // FNAME: null-terminated
        off = skip_cstr(input, off)?;
    }
    if flg & 0x10 != 0 {
        // FCOMMENT: null-terminated
        off = skip_cstr(input, off)?;
    }
    if flg & 0x02 != 0 {
        off += 2; // FHCRC
    }
    if off + 8 > input.len() {
        return None;
    }
    let body = &input[off..input.len() - 8];
    let out = miniz_oxide::inflate::decompress_to_vec(body).ok()?;
    let n = input.len();
    let crc = u32::from_le_bytes([input[n - 8], input[n - 7], input[n - 6], input[n - 5]]);
    let isize = u32::from_le_bytes([input[n - 4], input[n - 3], input[n - 2], input[n - 1]]);
    if crc32(&out) != crc || out.len() as u32 != isize {
        return None;
    }
    Some(out)
}

fn skip_cstr(input: &[u8], mut off: usize) -> Option<usize> {
    while off < input.len() {
        let b = input[off];
        off += 1;
        if b == 0 {
            return Some(off);
        }
    }
    None
}

/// zlib:compress/1 (zlib wrapper) and zlib:zip/1 (raw deflate).
#[no_mangle]
pub extern "C" fn mana_rt_zlib_compress(ctx: *mut ProcCtx, data: u64, raw: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut input = Vec::new();
    if iolist_flatten(data, &mut input).is_err() {
        return raise_badarg(ctx);
    }
    let out = if (raw as i64 >> 3) != 0 {
        miniz_oxide::deflate::compress_to_vec(&input, 6)
    } else {
        miniz_oxide::deflate::compress_to_vec_zlib(&input, 6)
    };
    bytes_to_new_bin(ctx, &out)
}

/// zlib:uncompress/1 (zlib wrapper) and zlib:unzip/1 (raw inflate).
#[no_mangle]
pub extern "C" fn mana_rt_zlib_uncompress(ctx: *mut ProcCtx, data: u64, raw: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut input = Vec::new();
    if iolist_flatten(data, &mut input).is_err() {
        return raise_badarg(ctx);
    }
    let res = if (raw as i64 >> 3) != 0 {
        miniz_oxide::inflate::decompress_to_vec(&input)
    } else {
        miniz_oxide::inflate::decompress_to_vec_zlib(&input)
    };
    match res {
        Ok(out) => bytes_to_new_bin(ctx, &out),
        Err(_) => raise_badarg(ctx),
    }
}

// ---------------------------------------------------------------------------
// zlib streams (miniz_oxide): opaque {mana_zlib, N} handles over a global
// slot table, mirroring the {mana_socket, N} pattern. A stream is created
// Idle by open/0 and switched to inflate or deflate mode by init. Bandit's
// permessage-deflate uses raw (negative-windowBits) streams with sync
// flush; browsers use the one-shot gzip/gunzip above.

enum ZStream {
    Idle,
    Inflate {
        state: Box<miniz_oxide::inflate::stream::InflateState>,
        window_bits: i32,
        pending: Vec<u8>,
    },
    Deflate {
        comp: Box<miniz_oxide::deflate::core::CompressorOxide>,
        flags: u32,
    },
}

static ZLIB_STREAMS: std::sync::Mutex<Vec<Option<std::sync::Arc<std::sync::Mutex<ZStream>>>>> =
    std::sync::Mutex::new(Vec::new());

fn zlib_handle(ctx: &mut ProcCtx, idx: usize) -> u64 {
    let p = alloc_nursery(ctx, 3);
    unsafe {
        *p = (2 << 8) | KIND_TUPLE;
        *p.add(1) = atom_intern(b"mana_zlib");
        *p.add(2) = ((idx as u64) << 3) | TAG_SMALL;
    }
    p as u64
}

fn zlib_resolve(t: u64) -> Option<(usize, std::sync::Arc<std::sync::Mutex<ZStream>>)> {
    if t & TAG_MASK != TAG_BOXED || t == 0 {
        return None;
    }
    let idx = unsafe {
        let p = t as *const u64;
        if *p != (2 << 8) | KIND_TUPLE {
            return None;
        }
        if *p.add(1) & TAG_MASK != TAG_ATOM || atom_bytes(*p.add(1)) != b"mana_zlib" {
            return None;
        }
        let i = *p.add(2);
        if i & TAG_MASK != TAG_SMALL {
            return None;
        }
        (i as i64 >> 3) as usize
    };
    let streams = ZLIB_STREAMS.lock().unwrap();
    streams.get(idx).and_then(|s| s.clone()).map(|a| (idx, a))
}

/// zlib:open/0 — a fresh Idle stream handle.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_open(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let idx = {
        let mut streams = ZLIB_STREAMS.lock().unwrap();
        let cell = Some(std::sync::Arc::new(std::sync::Mutex::new(ZStream::Idle)));
        match streams.iter().position(|s| s.is_none()) {
            Some(i) => {
                streams[i] = cell;
                i
            }
            None => {
                streams.push(cell);
                streams.len() - 1
            }
        }
    };
    zlib_handle(ctx, idx)
}

/// zlib:close/1 — free the slot.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_close(ctx: *mut ProcCtx, z: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    match zlib_resolve(z) {
        Some((idx, _)) => {
            let mut streams = ZLIB_STREAMS.lock().unwrap();
            if idx < streams.len() {
                streams[idx] = None;
            }
            known().ok
        }
        None => raise_badarg(ctx),
    }
}

fn zlib_window_bits(t: u64) -> i32 {
    if t & TAG_MASK == TAG_SMALL {
        (t as i64 >> 3) as i32
    } else {
        15 // default
    }
}

/// zlib:inflateInit/1,2 — switch the stream to inflate mode. Negative
/// windowBits selects the raw (headerless) format used by permessage-
/// deflate; the window magnitude is ignored (miniz always uses 32K, a
/// superset that decodes any smaller-window stream).
#[no_mangle]
pub extern "C" fn mana_rt_zlib_inflate_init(ctx: *mut ProcCtx, z: u64, window_bits: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, arc)) = zlib_resolve(z) else {
        return raise_badarg(ctx);
    };
    let wb = zlib_window_bits(window_bits);
    let mut s = arc.lock().unwrap();
    *s = ZStream::Inflate {
        state: miniz_oxide::inflate::stream::InflateState::new_boxed_with_window_bits(wb),
        window_bits: wb,
        pending: Vec::new(),
    };
    known().ok
}

/// zlib:deflateInit/2,6 — switch the stream to deflate mode. level and
/// strategy are honored, windowBits sign selects raw vs zlib (magnitude
/// ignored — output window is always 15), method and memLevel are ignored.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_deflate_init(
    ctx: *mut ProcCtx,
    z: u64,
    level: u64,
    window_bits: u64,
    strategy: u64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, arc)) = zlib_resolve(z) else {
        return raise_badarg(ctx);
    };
    let lvl = if level & TAG_MASK == TAG_SMALL {
        let v = level as i64 >> 3;
        if (0..=9).contains(&v) {
            v as i32
        } else {
            6 // default / -1
        }
    } else {
        6
    };
    let wb = zlib_window_bits(window_bits);
    let strat = if strategy & TAG_MASK == TAG_ATOM {
        match atom_bytes(strategy) {
            b"filtered" => 1,
            b"huffman_only" => 2,
            b"rle" => 3,
            _ => 0,
        }
    } else {
        0
    };
    let flags =
        miniz_oxide::deflate::core::create_comp_flags_from_zip_params(lvl, wb, strat);
    let mut s = arc.lock().unwrap();
    *s = ZStream::Deflate {
        comp: Box::new(miniz_oxide::deflate::core::CompressorOxide::new(flags)),
        flags,
    };
    known().ok
}

fn zlib_flush(t: u64) -> miniz_oxide::MZFlush {
    use miniz_oxide::MZFlush;
    if t & TAG_MASK == TAG_ATOM {
        match atom_bytes(t) {
            b"sync" => MZFlush::Sync,
            b"full" => MZFlush::Full,
            b"finish" => MZFlush::Finish,
            _ => MZFlush::None,
        }
    } else {
        MZFlush::None
    }
}

/// zlib:deflate/2,3 — compress a chunk with the given flush; returns the
/// output as a single binary (valid iodata — Bandit does iodata_to_binary).
#[no_mangle]
pub extern "C" fn mana_rt_zlib_deflate(ctx: *mut ProcCtx, z: u64, data: u64, flush: u64) -> u64 {
    use miniz_oxide::{MZFlush, MZStatus};
    let ctx = unsafe { &mut *ctx };
    let mut input = Vec::new();
    if iolist_flatten(data, &mut input).is_err() {
        return raise_badarg(ctx);
    }
    let Some((_, arc)) = zlib_resolve(z) else {
        return raise_badarg(ctx);
    };
    let fl = zlib_flush(flush);
    let mut s = arc.lock().unwrap();
    let ZStream::Deflate { comp, .. } = &mut *s else {
        return raise_badarg(ctx);
    };
    let mut out = Vec::with_capacity(input.len() / 2 + 64);
    let mut scratch = vec![0u8; 32 * 1024];
    let mut inbuf = &input[..];
    loop {
        let res = miniz_oxide::deflate::stream::deflate(comp, inbuf, &mut scratch, fl);
        out.extend_from_slice(&scratch[..res.bytes_written]);
        inbuf = &inbuf[res.bytes_consumed..];
        match res.status {
            Ok(MZStatus::StreamEnd) => break,
            Ok(_) => {
                let filled = res.bytes_written == scratch.len();
                if inbuf.is_empty() && !filled {
                    break;
                }
            }
            Err(_) => return raise_badarg(ctx),
        }
        // Finish must loop to StreamEnd; others stop when drained above
        if fl != MZFlush::Finish && inbuf.is_empty() && res.bytes_written == 0 {
            break;
        }
    }
    drop(s);
    bytes_to_new_bin(ctx, &out)
}

/// zlib:safeInflate/2 — one bounded inflate round over the accumulated
/// input; returns `{continue, Bin}` when more output may follow (the
/// output chunk filled) or `{finished, Bin}` when the input is drained.
/// Bandit re-calls with `[]` until it sees `finished`.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_safe_inflate(ctx: *mut ProcCtx, z: u64, data: u64) -> u64 {
    use miniz_oxide::{MZFlush, MZStatus};
    let ctx = unsafe { &mut *ctx };
    let mut newdata = Vec::new();
    if iolist_flatten(data, &mut newdata).is_err() {
        return raise_badarg(ctx);
    }
    let Some((_, arc)) = zlib_resolve(z) else {
        return raise_badarg(ctx);
    };
    const CHUNK: usize = 16 * 1024;
    let mut s = arc.lock().unwrap();
    let ZStream::Inflate { state, pending, .. } = &mut *s else {
        return raise_badarg(ctx);
    };
    pending.extend_from_slice(&newdata);
    let mut scratch = vec![0u8; CHUNK];
    let res = miniz_oxide::inflate::stream::inflate(state, pending, &mut scratch, MZFlush::None);
    let consumed = res.bytes_consumed;
    let written = res.bytes_written;
    pending.drain(..consumed);
    let done = matches!(res.status, Ok(MZStatus::StreamEnd)) || written < CHUNK;
    let out = scratch[..written].to_vec();
    drop(s);
    // build {tag, Bin} — root the binary across the tuple alloc
    let bin = bytes_to_new_bin(ctx, &out);
    let mut fr = [ctx.roots_head, 1, bin];
    ctx.roots_head = fr.as_ptr() as u64;
    let tag = atom_intern(if done { b"finished" } else { b"continue" });
    let p = alloc_nursery(ctx, 3);
    unsafe {
        *p = (2 << 8) | KIND_TUPLE;
        *p.add(1) = tag;
        *p.add(2) = fr[2];
    }
    ctx.roots_head = fr[0];
    let _ = &mut fr;
    p as u64
}

/// zlib:inflateReset/1 and deflateReset/1 — restore the stream to its
/// post-init state, keeping the same mode and parameters.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_reset(ctx: *mut ProcCtx, z: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, arc)) = zlib_resolve(z) else {
        return raise_badarg(ctx);
    };
    let mut s = arc.lock().unwrap();
    match &mut *s {
        ZStream::Inflate {
            state,
            window_bits,
            pending,
        } => {
            state.reset(miniz_oxide::DataFormat::from_window_bits(*window_bits));
            pending.clear();
        }
        ZStream::Deflate { comp, flags } => {
            *comp = Box::new(miniz_oxide::deflate::core::CompressorOxide::new(*flags));
        }
        ZStream::Idle => {}
    }
    known().ok
}

/// zlib:inflateEnd/1 and deflateEnd/1 — return the stream to Idle.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_end(ctx: *mut ProcCtx, z: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, arc)) = zlib_resolve(z) else {
        return raise_badarg(ctx);
    };
    *arc.lock().unwrap() = ZStream::Idle;
    known().ok
}

/// erlang:list_to_binary/1 (accepts iolists, like BEAM).
#[no_mangle]
pub extern "C" fn mana_rt_list_to_binary(ctx: *mut ProcCtx, l: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if l != NIL && l & TAG_MASK != TAG_CONS {
        return raise_badarg(ctx);
    }
    let mut out = Vec::new();
    match iolist_flatten(l, &mut out) {
        Ok(()) => bytes_to_new_bin(ctx, &out),
        Err(()) => raise_badarg(ctx),
    }
}

/// erlang:iolist_to_binary/1 — also accepts a bare binary.
#[no_mangle]
pub extern "C" fn mana_rt_iolist_to_binary(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut out = Vec::new();
    match iolist_flatten(t, &mut out) {
        Ok(()) => bytes_to_new_bin(ctx, &out),
        Err(()) => raise_badarg(ctx),
    }
}

/// Integer digits in a base (2..=36, uppercase — BEAM's format).
/// Digits of ANY integer term in `base` (bignum-aware).
fn int_term_digits(t: u64, base: u32) -> Option<String> {
    if t & TAG_MASK == TAG_SMALL {
        return Some(int_digits(t as i64 >> 3, base));
    }
    let (neg, mag) = bignum_parts(t)?;
    let body = if base == 10 {
        bigint::mag_to_decimal(mag)
    } else {
        // repeated divrem by the base — rare path (Integer.to_string/2)
        let mut cur = mag.to_vec();
        let mut out = Vec::new();
        while !cur.is_empty() {
            let (q, r) = bigint::mag_divrem_limb(&cur, base as u64);
            out.push(
                char::from_digit(r as u32, base)
                    .unwrap()
                    .to_ascii_uppercase() as u8,
            );
            cur = q;
        }
        out.reverse();
        String::from_utf8(out).unwrap()
    };
    Some(if neg { format!("-{}", body) } else { body })
}

fn int_digits(v: i64, base: u32) -> String {
    if v == 0 {
        return "0".into();
    }
    let neg = v < 0;
    let mut x = v.unsigned_abs();
    let mut out = Vec::new();
    while x > 0 {
        let d = (x % base as u64) as u32;
        out.push(char::from_digit(d, base).unwrap().to_ascii_uppercase() as u8);
        x /= base as u64;
    }
    if neg {
        out.push(b'-');
    }
    out.reverse();
    String::from_utf8(out).unwrap()
}

/// erlang:integer_to_binary/1,2 (base as a term; small 10 for /1).
#[no_mangle]
pub extern "C" fn mana_rt_integer_to_binary(ctx: *mut ProcCtx, t: u64, base: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if !is_int_term(t) || base & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let b = base as i64 >> 3;
    if !(2..=36).contains(&b) {
        return raise_badarg(ctx);
    }
    let s = int_term_digits(t, b as u32).unwrap();
    bytes_to_new_bin(ctx, s.as_bytes())
}

/// erlang:integer_to_list/1,2.
#[no_mangle]
pub extern "C" fn mana_rt_integer_to_list(ctx: *mut ProcCtx, t: u64, base: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if !is_int_term(t) || base & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let b = base as i64 >> 3;
    if !(2..=36).contains(&b) {
        return raise_badarg(ctx);
    }
    let s = int_term_digits(t, b as u32).unwrap();
    bytes_to_charlist(ctx, s.as_bytes())
}

/// erlang:pid_to_list/1 — BEAM-style "<0.ID.0>" charlist (no distribution,
/// so node creation and serial are 0). Inspect.PID wraps this as
/// "#PID<0.ID.0>".
#[no_mangle]
pub extern "C" fn mana_rt_pid_to_list(ctx: *mut ProcCtx, pid: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if pid & 0xF != PID_TAG4 {
        return raise_badarg(ctx);
    }
    let id = pid >> 4;
    let s = format!("<0.{}.0>", id);
    bytes_to_charlist(ctx, s.as_bytes())
}

/// Parse decimal/base digits (with optional sign) — badarg on any junk.
fn parse_int_term(ctx: &mut ProcCtx, bytes: &[u8], base: u32) -> Option<u64> {
    let s = std::str::from_utf8(bytes).ok()?;
    if let Ok(v) = i64::from_str_radix(s, base) {
        if v >> 60 == 0 || v >> 60 == -1 {
            return Some(((v << 3) as u64) | TAG_SMALL);
        }
    }
    // outside i64 / outside the small range: parse into limbs
    let (neg, digits) = match s.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    if digits.is_empty() {
        return None;
    }
    let mag = if base == 10 {
        bigint::mag_from_decimal(digits.as_bytes())?
    } else {
        let mut acc: Vec<u64> = Vec::new();
        for c in digits.chars() {
            let d = c.to_digit(base)?;
            acc = bigint::mag_add(&bigint::mag_mul(&acc, &[base as u64]), &[d as u64]);
        }
        bigint::normalize(acc)
    };
    Some(make_int_mag(ctx, neg && !mag.is_empty(), &mag))
}

/// erlang:binary_to_integer/1,2.
#[no_mangle]
pub extern "C" fn mana_rt_binary_to_integer(ctx: *mut ProcCtx, bin: u64, base: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if bin_parts(bin).is_none() || base & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let b = base as i64 >> 3;
    if !(2..=36).contains(&b) {
        return raise_badarg(ctx);
    }
    let bytes = bin_bytes(bin).to_vec();
    match parse_int_term(ctx, &bytes, b as u32) {
        Some(t) => t,
        None => raise_badarg(ctx),
    }
}

/// erlang:list_to_integer/1,2.
#[no_mangle]
pub extern "C" fn mana_rt_list_to_integer(ctx: *mut ProcCtx, l: u64, base: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if base & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let b = base as i64 >> 3;
    if !(2..=36).contains(&b) {
        return raise_badarg(ctx);
    }
    let mut bytes = Vec::new();
    let mut cur = l;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK != TAG_SMALL {
            return raise_badarg(ctx);
        }
        bytes.push((h as i64 >> 3) as u8);
        cur = unsafe { *p.add(1) };
    }
    match parse_int_term(ctx, &bytes, b as u32) {
        Some(t) => t,
        None => raise_badarg(ctx),
    }
}

/// erlang:atom_to_list/1.
#[no_mangle]
pub extern "C" fn mana_rt_atom_to_list(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if t & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let bytes: Vec<u8> = atom_bytes(t).to_vec();
    bytes_to_charlist(ctx, &bytes)
}

/// erlang:atom_to_binary/1,2 (utf8 == latin1 for our ascii atom names).
#[no_mangle]
pub extern "C" fn mana_rt_atom_to_binary(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if t & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let bytes: Vec<u8> = atom_bytes(t).to_vec();
    bytes_to_new_bin(ctx, &bytes)
}

// Closed-world atom table: codegen plants one pointer per atom static in
// the `mana_atoms` ELF section; the linker deduplicates (linkonce_odr) and
// provides __start/__stop bounds. Every program registers well-known atoms,
// so the section is never empty.
extern "C" {
    static __start_mana_atoms: u64;
    static __stop_mana_atoms: u64;
}

type AtomTable = std::sync::RwLock<rustc_hash::FxHashMap<&'static [u8], u64>>;

fn atom_table_lock() -> &'static AtomTable {
    static TABLE: std::sync::OnceLock<AtomTable> = std::sync::OnceLock::new();
    TABLE.get_or_init(|| {
        let mut map = rustc_hash::FxHashMap::default();
        unsafe {
            let start = &raw const __start_mana_atoms;
            let stop = &raw const __stop_mana_atoms;
            let n = (stop as usize - start as usize) / 8;
            for i in 0..n {
                // entries are raw pointers to the atom structs
                let p = *start.add(i);
                if p != 0 {
                    let atom = p | TAG_ATOM;
                    map.insert(atom_bytes(atom), atom);
                }
            }
        }
        std::sync::RwLock::new(map)
    })
}

/// Look up an existing atom by name bytes.
fn atom_lookup(bytes: &[u8]) -> Option<u64> {
    atom_table_lock().read().unwrap().get(bytes).copied()
}

/// Get-or-mint an atom. Minted atoms are eternal {len, bytes} structs in
/// the SAME table, so pointer identity (raw =:=) holds program-wide. BEAM
/// parity for list_to_atom/binary_to_atom; the table can grow at runtime
/// but never shrinks — same as BEAM.
fn atom_intern(bytes: &[u8]) -> u64 {
    if let Some(a) = atom_lookup(bytes) {
        return a;
    }
    let mut map = atom_table_lock().write().unwrap();
    if let Some(&a) = map.get(bytes) {
        return a;
    }
    let words = 1 + (bytes.len() + 7) / 8;
    let p = alloc_space(words);
    unsafe {
        *p = bytes.len() as u64;
        if bytes.len() % 8 != 0 {
            *p.add(words - 1) = 0;
        }
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), p.add(1) as *mut u8, bytes.len());
    }
    let atom = (p as u64) | TAG_ATOM;
    let key: &'static [u8] = Box::leak(bytes.to_vec().into_boxed_slice());
    map.insert(key, atom);
    atom
}

// Behaviours table: (module_atom, behaviour_atom) raw-pointer pairs.
extern "C" {
    static __start_mana_behaviours: u64;
    static __stop_mana_behaviours: u64;
}

fn behaviours_of(m: u64) -> Vec<u64> {
    let mut out = Vec::new();
    unsafe {
        let start = &raw const __start_mana_behaviours;
        let stop = &raw const __stop_mana_behaviours;
        let n = (stop as usize - start as usize) / 16;
        for i in 0..n {
            let e = start.add(2 * i);
            // a self-referential pair is the section anchor, not data
            if *e | TAG_ATOM == m && *e.add(1) != *e {
                out.push(*e.add(1) | TAG_ATOM);
            }
        }
    }
    out
}

// Closed-world export table: codegen plants one 4-word entry per exported
// function in the `mana_exports` ELF section: raw pointers to the module
// and function atom structs, the arity, and the code pointer. Atoms are
// program-wide deduped, so lookup is by tagged-word identity.
extern "C" {
    static __start_mana_exports: u64;
    static __stop_mana_exports: u64;
}

fn export_table() -> &'static rustc_hash::FxHashMap<(u64, u64, u64), usize> {
    static TABLE: std::sync::OnceLock<rustc_hash::FxHashMap<(u64, u64, u64), usize>> =
        std::sync::OnceLock::new();
    TABLE.get_or_init(|| {
        let mut map = rustc_hash::FxHashMap::default();
        unsafe {
            let start = &raw const __start_mana_exports;
            let stop = &raw const __stop_mana_exports;
            let n = (stop as usize - start as usize) / 32;
            for i in 0..n {
                let e = start.add(4 * i);
                let (m, f, a, code) = (*e, *e.add(1), *e.add(2), *e.add(3));
                if m != 0 && f != 0 {
                    map.insert((m | TAG_ATOM, f | TAG_ATOM, a), code as usize);
                }
            }
        }
        map
    })
}

/// Call `code` (a compiled function of `n` params) with unpacked args.
/// Closures take the fun term as a trailing parameter (`fun_term != 0`).
unsafe fn call_dynamic(
    ctx: *mut ProcCtx,
    code: usize,
    argv: &[u64],
    fun_term: u64,
) -> Option<u64> {
    type C = *mut ProcCtx;
    let a = argv;
    let r = match (a.len(), fun_term != 0) {
        (0, false) => std::mem::transmute::<usize, extern "C" fn(C) -> u64>(code)(ctx),
        (1, false) => std::mem::transmute::<usize, extern "C" fn(C, u64) -> u64>(code)(ctx, a[0]),
        (2, false) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64) -> u64>(code)(ctx, a[0], a[1]),
        (3, false) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64) -> u64>(code)(ctx, a[0], a[1], a[2]),
        (4, false) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64) -> u64>(code)(ctx, a[0], a[1], a[2], a[3]),
        (5, false) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64, u64) -> u64>(code)(ctx, a[0], a[1], a[2], a[3], a[4]),
        (6, false) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64, u64, u64) -> u64>(code)(ctx, a[0], a[1], a[2], a[3], a[4], a[5]),
        (7, false) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64, u64, u64, u64) -> u64>(code)(ctx, a[0], a[1], a[2], a[3], a[4], a[5], a[6]),
        (8, false) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(code)(ctx, a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]),
        (0, true) => std::mem::transmute::<usize, extern "C" fn(C, u64) -> u64>(code)(ctx, fun_term),
        (1, true) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64) -> u64>(code)(ctx, a[0], fun_term),
        (2, true) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64) -> u64>(code)(ctx, a[0], a[1], fun_term),
        (3, true) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64) -> u64>(code)(ctx, a[0], a[1], a[2], fun_term),
        (4, true) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64, u64) -> u64>(code)(ctx, a[0], a[1], a[2], a[3], fun_term),
        (5, true) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64, u64, u64) -> u64>(code)(ctx, a[0], a[1], a[2], a[3], a[4], fun_term),
        (6, true) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64, u64, u64, u64) -> u64>(code)(ctx, a[0], a[1], a[2], a[3], a[4], a[5], fun_term),
        (7, true) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(code)(ctx, a[0], a[1], a[2], a[3], a[4], a[5], a[6], fun_term),
        (8, true) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64>(code)(ctx, a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], fun_term),
        _ => return None,
    };
    Some(r)
}

/// Unpack a proper list of at most 8 elements. Err(()) = improper/too long.
fn unpack_args(list: u64) -> Result<([u64; 8], usize), ()> {
    let mut v = [0u64; 8];
    let mut n = 0;
    let mut cur = list;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS || n == 8 {
            return Err(());
        }
        let p = (cur & !TAG_MASK) as *const u64;
        unsafe {
            v[n] = *p;
            cur = *p.add(1);
        }
        n += 1;
    }
    Ok((v, n))
}

fn raise_undef(ctx: &mut ProcCtx) -> u64 {
    ctx.exc_class = atom_error();
    ctx.exc_reason = known().undef;
    EXC_SENTINEL
}

/// erlang:apply/3 — closed world: only exported functions of compiled
/// modules are callable; anything else is undef (like BEAM without the
/// module loaded). Arities above 8 are TODO(apply-arity).
#[no_mangle]
pub extern "C" fn mana_rt_apply3(ctx: *mut ProcCtx, m: u64, f: u64, args: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if m & TAG_MASK != TAG_ATOM || f & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let Ok((argv, n)) = unpack_args(args) else {
        if std::env::var_os("MANA_DEBUG_BADARG").is_some() {
            eprintln!(
                "mana: apply3 bad args list for {}:{} (args {:#x})",
                String::from_utf8_lossy(atom_bytes(m)),
                String::from_utf8_lossy(atom_bytes(f)),
                args
            );
        }
        return raise_badarg(ctx);
    };
    let Some(&code) = export_table().get(&(m, f, n as u64)) else {
        // dynamic calls into the BIF surface (compiled statically
        // everywhere else): the hot handful, extended on demand
        if atom_bytes(m) == b"erlang" {
            match (atom_bytes(f), n) {
                (b"error", 1) | (b"exit", 1) | (b"throw", 1) => {
                    let class = match atom_bytes(f) {
                        b"error" => atom_error(),
                        b"exit" => find_atom("exit").expect("exit atom"),
                        _ => find_atom("throw").expect("throw atom"),
                    };
                    ctx.exc_class = class;
                    ctx.exc_reason = argv[0];
                    return EXC_SENTINEL;
                }
                (b"apply", 3) => return mana_rt_apply3(ctx, argv[0], argv[1], argv[2]),
                (b"apply", 2) => return mana_rt_apply_fun(ctx, argv[0], argv[1]),
                (b"send", 2) | (b"!", 2) => {
                    mana_rt_send(ctx, argv[0], argv[1]);
                    return argv[1];
                }
                (b"self", 0) => return make_pid(ctx.current),
                _ => {}
            }
        }
        // module_info is never compiled; answer the introspection shapes
        // callers actually use (attributes → behaviours, module → the atom)
        if atom_bytes(f) == b"module_info" && module_is_compiled(m) {
            if n == 0 {
                return NIL;
            }
            if n == 1 {
                return module_info_item(ctx, m, argv[0]);
            }
        }
        if std::env::var_os("MANA_DEBUG_UNDEF").is_some() {
            eprintln!(
                "mana: undef {}:{}/{}",
                String::from_utf8_lossy(atom_bytes(m)),
                String::from_utf8_lossy(atom_bytes(f)),
                n
            );
        }
        return raise_undef(ctx);
    };
    unsafe { call_dynamic(ctx, code, &argv[..n], 0).unwrap_or_else(|| raise_undef(ctx)) }
}

/// Introspection items shared by the module_info fallback in apply3 and
/// erlang:get_module_info/2 (which compiled `__info__/1` clauses call).
fn module_info_item(ctx: &mut ProcCtx, m: u64, item: u64) -> u64 {
    match atom_bytes(item) {
        b"module" => m,
        b"attributes" => {
            // [{behaviour, [B]}] per declared behaviour
            let bs = behaviours_of(m);
            let saved = ctx.roots_head;
            let mut fr = [0u64, 2, NIL, 0];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            for &b in bs.iter().rev() {
                let inner = alloc_nursery(ctx, 2);
                unsafe {
                    *inner = b;
                    *inner.add(1) = NIL;
                }
                let t = alloc_nursery(ctx, 3);
                unsafe {
                    *t = (2 << 8) | KIND_TUPLE;
                    *t.add(1) = atom_intern(b"behaviour");
                    *t.add(2) = inner as u64 | TAG_CONS;
                }
                fr[3] = t as u64;
                let cell = alloc_nursery(ctx, 2);
                unsafe {
                    *cell = fr[3];
                    *cell.add(1) = fr[2];
                }
                fr[2] = cell as u64 | TAG_CONS;
            }
            ctx.roots_head = saved;
            fr[2]
        }
        b"functions" | b"exports" => {
            // {name, arity} pairs from the export table, name/arity sorted
            // for determinism (BEAM's order is unspecified)
            let mut fs: Vec<(u64, u64)> = export_table()
                .keys()
                .filter(|(km, _, _)| *km == m)
                .map(|(_, kf, ka)| (*kf, *ka))
                .collect();
            fs.sort_by(|a, b| atom_bytes(a.0).cmp(atom_bytes(b.0)).then(a.1.cmp(&b.1)));
            let saved = ctx.roots_head;
            let mut fr = [0u64, 2, NIL, 0];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            for &(f, a) in fs.iter().rev() {
                let t = alloc_nursery(ctx, 3);
                unsafe {
                    *t = (2 << 8) | KIND_TUPLE;
                    *t.add(1) = f;
                    *t.add(2) = ((a << 3) as u64) | TAG_SMALL;
                }
                fr[3] = t as u64;
                let cell = alloc_nursery(ctx, 2);
                unsafe {
                    *cell = fr[3];
                    *cell.add(1) = fr[2];
                }
                fr[2] = cell as u64 | TAG_CONS;
            }
            ctx.roots_head = saved;
            fr[2]
        }
        _ => NIL,
    }
}

/// erlang:get_module_info/2 — reached by compiled `__info__/1` clauses
/// (attributes/compile arms); the useful arms answer, the rest are [].
#[no_mangle]
pub extern "C" fn mana_rt_get_module_info(ctx: *mut ProcCtx, m: u64, item: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if m & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    module_info_item(ctx, m, item)
}

/// erlang:apply/2 — call a fun value with a runtime argument list.
#[no_mangle]
pub extern "C" fn mana_rt_apply_fun(ctx: *mut ProcCtx, fun: u64, args: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Ok((argv, n)) = unpack_args(args) else {
        return raise_badarg(ctx);
    };
    if fun & TAG_MASK != TAG_BOXED || fun == 0 {
        return raise_badarg(ctx);
    }
    let header = unsafe { *(fun as *const u64) };
    if header & 0xff != KIND_FUN || (header >> 8) & 0xff != n as u64 {
        // wrong kind or arity — bare badarg (badarity tuples carry
        // stacktrace-shaped payloads we don't build; TODO(stacktraces))
        return raise_badarg(ctx);
    }
    let code = unsafe { *(fun as *const u64).add(1) } as usize;
    unsafe { call_dynamic(ctx, code, &argv[..n], fun).unwrap_or_else(|| raise_badarg(ctx)) }
}

// ---------------------------------------------------------------------------
// io (native cut: we never compile OTP's io.erl / group-leader protocol)

/// io:put_chars/1 — write iodata (chardata restricted to bytes; unicode
/// code points beyond latin-1 are TODO(unicode)) to stdout. Returns ok.
#[no_mangle]
pub extern "C" fn mana_rt_io_put_chars(ctx: *mut ProcCtx, data: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut out = Vec::new();
    if iolist_flatten(data, &mut out).is_err() {
        return raise_badarg(ctx);
    }
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut lock = stdout.lock();
    if lock.write_all(&out).and_then(|_| lock.flush()).is_err() {
        return raise_badarg(ctx);
    }
    known().ok
}

/// Flatten chardata: like an iolist, but integers are Unicode code points
/// (utf8-encoded), not bytes. Binaries splice raw (assumed utf8).
fn chardata_flatten(t: u64, out: &mut Vec<u8>) -> Result<(), ()> {
    if let Some((p, n)) = bin_parts(t) {
        out.extend_from_slice(unsafe { std::slice::from_raw_parts(p, n) });
        return Ok(());
    }
    let mut cur = t;
    loop {
        if cur == NIL {
            return Ok(());
        }
        if cur & TAG_MASK != TAG_CONS {
            if bin_parts(cur).is_some() {
                return chardata_flatten(cur, out);
            }
            return Err(());
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK == TAG_SMALL {
            let cp = h as i64 >> 3;
            let c = u32::try_from(cp).ok().and_then(char::from_u32).ok_or(())?;
            let mut buf = [0u8; 4];
            out.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
        } else {
            chardata_flatten(h, out)?;
        }
        cur = unsafe { *p.add(1) };
    }
}

/// unicode:characters_to_nfc_list/1 — NFC-normalized code point list
/// (String.Tokenizer validates identifiers through this).
#[no_mangle]
pub extern "C" fn mana_rt_unicode_to_nfc_list(ctx: *mut ProcCtx, t: u64) -> u64 {
    use unicode_normalization::UnicodeNormalization;
    let ctx = unsafe { &mut *ctx };
    let mut bytes = Vec::new();
    if chardata_flatten(t, &mut bytes).is_err() {
        return raise_badarg(ctx);
    }
    let Ok(s) = std::str::from_utf8(&bytes) else {
        return raise_badarg(ctx);
    };
    let nfc: String = s.nfc().collect();
    utf8_to_codepoint_list(ctx, nfc.as_bytes())
}

/// unicode:characters_to_binary/1 (utf8 in, utf8 out).
#[no_mangle]
pub extern "C" fn mana_rt_unicode_to_binary(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut out = Vec::new();
    match chardata_flatten(t, &mut out) {
        Ok(()) => bytes_to_new_bin(ctx, &out),
        Err(()) => raise_badarg(ctx),
    }
}

/// unicode:characters_to_list/1 — code point list from utf8 chardata.
#[no_mangle]
pub extern "C" fn mana_rt_unicode_to_list(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut bytes = Vec::new();
    if chardata_flatten(t, &mut bytes).is_err() {
        return raise_badarg(ctx);
    }
    let Ok(s) = std::str::from_utf8(&bytes) else {
        return raise_badarg(ctx);
    };
    let cps: Vec<u64> = s.chars().map(|c| ((c as u64) << 3) | TAG_SMALL).collect();
    // build the list back-to-front; the code points are immediates so only
    // the partial list needs rooting
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &cp in cps.iter().rev() {
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = cp;
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[2]
}

/// The io_lib format engine: ~[F][.P][t]C for C in s f e p w n ~, with
/// `*` widths/precisions taken from the argument list and negative widths
/// meaning left-alignment (the benchee console subset). Unknown directives
/// print their raw text.
fn format_engine(fmt: u64, args: u64) -> Result<Vec<u8>, ()> {
    let mut fbytes = Vec::new();
    chardata_flatten(fmt, &mut fbytes)?;
    let mut argv = Vec::new();
    let mut cur = args;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return Err(());
        }
        let p = (cur & !TAG_MASK) as *const u64;
        unsafe {
            argv.push(*p);
            cur = *p.add(1);
        }
    }
    let mut out = Vec::new();
    let mut ai = 0;
    let mut i = 0;
    let mut next_arg = |ai: &mut usize| -> u64 {
        let v = argv.get(*ai).copied().unwrap_or(NIL);
        *ai += 1;
        v
    };
    while i < fbytes.len() {
        let b = fbytes[i];
        if b != b'~' || i + 1 >= fbytes.len() {
            out.push(b);
            i += 1;
            continue;
        }
        let mut j = i + 1;
        // field width: [-]digits or *
        let mut width: Option<i64> = None;
        let mut neg = false;
        if fbytes.get(j) == Some(&b'-') {
            neg = true;
            j += 1;
        }
        if fbytes.get(j) == Some(&b'*') {
            let w = next_arg(&mut ai);
            if w & TAG_MASK == TAG_SMALL {
                width = Some(w as i64 >> 3);
            }
            j += 1;
        } else {
            let mut digits = 0i64;
            let mut any = false;
            while let Some(&d) = fbytes.get(j) {
                if d.is_ascii_digit() {
                    digits = digits * 10 + (d - b'0') as i64;
                    any = true;
                    j += 1;
                } else {
                    break;
                }
            }
            if any {
                width = Some(if neg { -digits } else { digits });
            }
        }
        // precision: .digits or .*
        let mut prec: Option<usize> = None;
        if fbytes.get(j) == Some(&b'.') {
            j += 1;
            if fbytes.get(j) == Some(&b'*') {
                let p = next_arg(&mut ai);
                if p & TAG_MASK == TAG_SMALL {
                    prec = Some((p as i64 >> 3).max(0) as usize);
                }
                j += 1;
            } else {
                let mut digits = 0usize;
                while let Some(&d) = fbytes.get(j) {
                    if d.is_ascii_digit() {
                        digits = digits * 10 + (d - b'0') as usize;
                        j += 1;
                    } else {
                        break;
                    }
                }
                prec = Some(digits);
            }
        }
        // modifiers
        while matches!(fbytes.get(j), Some(b't') | Some(b'l')) {
            j += 1;
        }
        let pad = |out: &mut Vec<u8>, piece: Vec<u8>, width: Option<i64>| {
            match width {
                Some(w) => {
                    let w_abs = w.unsigned_abs() as usize;
                    let fill = w_abs.saturating_sub(piece.len());
                    if w < 0 {
                        out.extend_from_slice(&piece);
                        out.extend(std::iter::repeat(b' ').take(fill));
                    } else {
                        out.extend(std::iter::repeat(b' ').take(fill));
                        out.extend_from_slice(&piece);
                    }
                }
                None => out.extend_from_slice(&piece),
            }
        };
        match fbytes.get(j) {
            Some(b'n') => out.push(b'\n'),
            Some(b'~') => out.push(b'~'),
            Some(b's') => {
                let a = next_arg(&mut ai);
                let mut piece = Vec::new();
                if a & TAG_MASK == TAG_ATOM {
                    piece.extend_from_slice(atom_bytes(a));
                } else {
                    chardata_flatten(a, &mut piece)?;
                }
                pad(&mut out, piece, width);
            }
            Some(b'f') => {
                let a = next_arg(&mut ai);
                let Some((x, _)) = num_of(a) else {
                    return Err(());
                };
                let piece = format!("{:.*}", prec.unwrap_or(6), x).into_bytes();
                pad(&mut out, piece, width);
            }
            Some(b'e') => {
                let a = next_arg(&mut ai);
                let Some((x, _)) = num_of(a) else {
                    return Err(());
                };
                let piece = display_float(x).into_bytes();
                pad(&mut out, piece, width);
            }
            Some(b'p') | Some(b'w') => {
                let a = next_arg(&mut ai);
                let mut s = String::new();
                write_term(a, &mut s);
                pad(&mut out, s.into_bytes(), width);
            }
            Some(&other) => {
                out.push(b'~');
                out.push(other);
            }
            None => out.push(b'~'),
        }
        i = j + 1;
    }
    Ok(out)
}

/// io:format/2.
#[no_mangle]
pub extern "C" fn mana_rt_io_format(ctx: *mut ProcCtx, fmt: u64, args: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Ok(out) = format_engine(fmt, args) else {
        return raise_badarg(ctx);
    };
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut lock = stdout.lock();
    if lock.write_all(&out).and_then(|_| lock.flush()).is_err() {
        return raise_badarg(ctx);
    }
    known().ok
}

/// Byte vec → charlist (nursery); bytes already copied off-heap.
fn bytes_to_charlist(ctx: &mut ProcCtx, bytes: &[u8]) -> u64 {
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &b in bytes.iter().rev() {
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = ((b as u64) << 3) | TAG_SMALL;
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[2]
}

/// utf8 bytes → CODEPOINT charlist (io_lib semantics; binary_to_list's
/// byte semantics live in bytes_to_charlist).
fn utf8_to_codepoint_list(ctx: &mut ProcCtx, bytes: &[u8]) -> u64 {
    let s = String::from_utf8_lossy(bytes);
    let cps: Vec<u64> = s.chars().map(|c| ((c as u64) << 3) | TAG_SMALL).collect();
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &cp in cps.iter().rev() {
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = cp;
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[2]
}

/// io_lib:format/2 — the formatted codepoint charlist.
#[no_mangle]
pub extern "C" fn mana_rt_io_lib_format(ctx: *mut ProcCtx, fmt: u64, args: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Ok(out) = format_engine(fmt, args) else {
        return raise_badarg(ctx);
    };
    utf8_to_codepoint_list(ctx, &out)
}

/// io_lib:write/1 (and write/2 with depth ignored) — display text of a term.
#[no_mangle]
pub extern "C" fn mana_rt_io_lib_write(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut s = String::new();
    write_term(t, &mut s);
    utf8_to_codepoint_list(ctx, s.as_bytes())
}

// ---------------------------------------------------------------------------
// persistent_term (native cut)

/// Deep copy a term into self-contained eternal storage: every pointer in
/// the copy targets another eternal block, so the GC never needs to see it.
/// persistent_term values are immortal by design (puts are rare).
fn eternal_deep_copy(t: u64) -> u64 {
    match t & TAG_MASK {
        TAG_CONS => {
            let p = (t & !TAG_MASK) as *const u64;
            let (h, tl) = unsafe { (*p, *p.add(1)) };
            let np = alloc_space(2);
            unsafe {
                *np = eternal_deep_copy(h);
                *np.add(1) = eternal_deep_copy(tl);
            }
            np as u64 | TAG_CONS
        }
        TAG_BOXED if t != 0 => {
            let p = t as *const u64;
            let header = unsafe { *p };
            // flatten views up front: an eternal reason must not pin a heap
            // parent (and eternal storage never gets GC-forwarded)
            if header & 0xff == KIND_SUBBIN {
                let bytes = bin_bytes(t);
                let bwords = 1 + (bytes.len() + 7) / 8;
                let bp = alloc_space(bwords);
                unsafe {
                    *bp = ((bytes.len() as u64) << 8) | KIND_BIN;
                    if bytes.len() % 8 != 0 {
                        *bp.add(bwords - 1) = 0;
                    }
                    std::ptr::copy_nonoverlapping(
                        bytes.as_ptr(),
                        bp.add(1) as *mut u8,
                        bytes.len(),
                    );
                }
                return bp as u64;
            }
            let words = 1 + payload_words(header);
            let np = alloc_space(words);
            unsafe {
                *np = header;
                match header & 0xff {
                    KIND_FLOAT | KIND_BIN | KIND_BIGNUM => {
                        std::ptr::copy_nonoverlapping(p.add(1), np.add(1), words - 1);
                    }
                    KIND_FUN => {
                        *np.add(1) = *p.add(1); // code ptr
                        for i in 2..words {
                            *np.add(i) = eternal_deep_copy(*p.add(i));
                        }
                    }
                    _ => {
                        for i in 1..words {
                            *np.add(i) = eternal_deep_copy(*p.add(i));
                        }
                    }
                }
            }
            np as u64
        }
        _ => t, // immediates and atoms (static) pass through
    }
}

static PERSISTENT_TERMS: std::sync::Mutex<Option<std::collections::HashMap<u64, u64>>> =
    std::sync::Mutex::new(None);

/// persistent_term:put/2 — keys compared exactly (we require immediate or
/// atom keys, which covers real usage; compound keys are TODO).
#[no_mangle]
pub extern "C" fn mana_rt_pt_put(_ctx: *mut ProcCtx, key: u64, val: u64) -> u64 {
    let key = eternal_deep_copy(key);
    let val = eternal_deep_copy(val);
    let mut guard = PERSISTENT_TERMS.lock().unwrap();
    let map = guard.get_or_insert_with(Default::default);
    // exact-compare lookup for compound keys
    let existing = map.keys().copied().find(|&k| mana_rt_eq_exact(k, key) == 1);
    match existing {
        Some(k) => {
            map.insert(k, val);
        }
        None => {
            map.insert(key, val);
        }
    }
    known().ok
}

/// persistent_term:get/1,2 — sentinel-free: get/1 raises badarg on miss
/// (BEAM's behavior), get/2 returns the default.
#[no_mangle]
pub extern "C" fn mana_rt_pt_get(ctx: *mut ProcCtx, key: u64, default: u64, has_default: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let guard = PERSISTENT_TERMS.lock().unwrap();
    let found = guard
        .as_ref()
        .and_then(|m| m.keys().copied().find(|&k| mana_rt_eq_exact(k, key) == 1).map(|k| m[&k]));
    match found {
        Some(v) => v,
        None if has_default != 0 => default,
        None => raise_badarg(ctx),
    }
}

// ---------------------------------------------------------------------------
// binary module C BIFs (all of binary.erl is nif stubs)

/// Any atom compiled into the program, by name. The closed-world table is
/// complete, so a miss means the runtime tried to mint a new atom.
fn find_atom(name: &str) -> Option<u64> {
    atom_lookup(name.as_bytes())
}

/// normal / shutdown / {shutdown, _}: BEAM treats these exit reasons as
/// orderly termination and logs nothing.
fn exit_reason_is_quiet(r: u64) -> bool {
    if r == known().normal {
        return true;
    }
    if r & TAG_MASK == TAG_ATOM {
        return atom_bytes(r) == b"shutdown";
    }
    if r & TAG_MASK == TAG_BOXED && r != 0 {
        let header = unsafe { *(r as *const u64) };
        if header & 0xff == KIND_TUPLE && (header >> 8) == 2 {
            let first = unsafe { *(r as *const u64).add(1) };
            return first & TAG_MASK == TAG_ATOM && atom_bytes(first) == b"shutdown";
        }
    }
    false
}

fn interned_atom_count() -> u64 {
    atom_table_lock().read().map(|m| m.len() as u64).unwrap_or(0)
}

/// Patterns: a binary or a non-empty list of binaries (compile_pattern is
/// the identity in our world). Byte vectors returned for searching.
fn pattern_bins(pat: u64) -> Result<Vec<&'static [u8]>, ()> {
    if bin_parts(pat).is_some() {
        return Ok(vec![bin_bytes(pat)]);
    }
    let mut out = Vec::new();
    let mut cur = pat;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return Err(());
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if bin_parts(h).is_none() {
            return Err(());
        }
        out.push(bin_bytes(h));
        cur = unsafe { *p.add(1) };
    }
    if out.is_empty() || out.iter().any(|b| b.is_empty()) {
        return Err(());
    }
    Ok(out)
}

/// Leftmost match at or after `from`; longest pattern wins ties.
fn bin_search(hay: &[u8], pats: &[&[u8]], from: usize) -> Option<(usize, usize)> {
    for i in from..hay.len() {
        let mut best = 0usize;
        for p in pats {
            if p.len() > best && hay[i..].starts_with(p) {
                best = p.len();
            }
        }
        if best > 0 {
            return Some((i, best));
        }
    }
    None
}

/// binary:split/2,3. opts term: nil or list of global/trim/trim_all.
#[no_mangle]
pub extern "C" fn mana_rt_binary_split(ctx: *mut ProcCtx, bin: u64, pat: u64, opts: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if bin_parts(bin).is_none() {
        return raise_badarg(ctx);
    }
    let Ok(pats) = pattern_bins(pat) else {
        return raise_badarg(ctx);
    };
    let (mut global, mut trim, mut trim_all) = (false, false, false);
    let mut cur = opts;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let opt = unsafe { *p };
        match atom_bytes(opt) {
            b"global" => global = true,
            b"trim" => trim = true,
            b"trim_all" => trim_all = true,
            _ => return raise_badarg(ctx),
        }
        cur = unsafe { *p.add(1) };
    }
    // copy out — allocation below can move the source binary
    let hay: Vec<u8> = bin_bytes(bin).to_vec();
    let pats: Vec<Vec<u8>> = pats.iter().map(|p| p.to_vec()).collect();
    let pref: Vec<&[u8]> = pats.iter().map(|p| p.as_slice()).collect();
    let mut parts: Vec<Vec<u8>> = Vec::new();
    let mut start = 0usize;
    loop {
        match bin_search(&hay, &pref, start) {
            Some((at, len)) => {
                parts.push(hay[start..at].to_vec());
                start = at + len;
                if !global {
                    break;
                }
            }
            None => break,
        }
    }
    parts.push(hay[start..].to_vec());
    if trim_all {
        parts.retain(|p| !p.is_empty());
    } else if trim {
        while parts.last().is_some_and(|p| p.is_empty()) {
            parts.pop();
        }
    }
    // build the result list back-to-front, rooting the partial list and
    // the fresh binary across each cell allocation
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, 0];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for bytes in parts.iter().rev() {
        fr[3] = bytes_to_new_bin(ctx, bytes);
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = fr[3];
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
        fr[3] = 0;
    }
    ctx.roots_head = saved;
    fr[2]
}

/// binary:match/2,3 (mode 0: {S,L}|nomatch) and matches (mode 1: list).
#[no_mangle]
pub extern "C" fn mana_rt_binary_match(ctx: *mut ProcCtx, bin: u64, pat: u64, mode: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if bin_parts(bin).is_none() {
        return raise_badarg(ctx);
    }
    let Ok(pats) = pattern_bins(pat) else {
        return raise_badarg(ctx);
    };
    let hay: Vec<u8> = bin_bytes(bin).to_vec();
    let pats: Vec<Vec<u8>> = pats.iter().map(|p| p.to_vec()).collect();
    let pref: Vec<&[u8]> = pats.iter().map(|p| p.as_slice()).collect();
    fn mk_pair(ctx: &mut ProcCtx, at: usize, len: usize) -> u64 {
        let t = alloc_nursery(ctx, 3);
        unsafe {
            *t = (2 << 8) | KIND_TUPLE;
            *t.add(1) = ((at as u64) << 3) | TAG_SMALL;
            *t.add(2) = ((len as u64) << 3) | TAG_SMALL;
        }
        t as u64
    }
    if mode == 0 {
        return match bin_search(&hay, &pref, 0) {
            Some((at, len)) => mk_pair(ctx, at, len),
            None => find_atom("nomatch").expect("nomatch atom compiled in"),
        };
    }
    let mut hits = Vec::new();
    let mut start = 0usize;
    while let Some((at, len)) = bin_search(&hay, &pref, start) {
        hits.push((at, len));
        start = at + len;
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, 0];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &(at, len) in hits.iter().rev() {
        fr[3] = mk_pair(ctx, at, len);
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = fr[3];
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
        fr[3] = 0;
    }
    ctx.roots_head = saved;
    fr[2]
}

/// binary:copy/2 (copy/1 passes n = 1).
#[no_mangle]
pub extern "C" fn mana_rt_binary_copy(ctx: *mut ProcCtx, bin: u64, n: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if bin_parts(bin).is_none() || n & TAG_MASK != TAG_SMALL || (n as i64 >> 3) < 0 {
        return raise_badarg(ctx);
    }
    let count = (n as i64 >> 3) as usize;
    let bytes: Vec<u8> = bin_bytes(bin).repeat(count);
    bytes_to_new_bin(ctx, &bytes)
}

/// binary:at/2 (pos is a term); `last` != 0 → last byte (binary:last/1),
/// ignoring pos.
#[no_mangle]
pub extern "C" fn mana_rt_binary_at(ctx: *mut ProcCtx, bin: u64, pos: u64, last: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((p, len)) = bin_parts(bin) else {
        return raise_badarg(ctx);
    };
    if len == 0 {
        return raise_badarg(ctx);
    }
    let i = if last != 0 {
        len - 1
    } else {
        if pos & TAG_MASK != TAG_SMALL || (pos as i64 >> 3) < 0 {
            return raise_badarg(ctx);
        }
        (pos as i64 >> 3) as usize
    };
    if i >= len {
        return raise_badarg(ctx);
    }
    let b = unsafe { *p.add(i) };
    ((b as u64) << 3) | TAG_SMALL
}

/// binary:encode_unsigned/1,2 (little != 0 → little-endian).
#[no_mangle]
pub extern "C" fn mana_rt_binary_encode_unsigned(ctx: *mut ProcCtx, n: u64, little: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if n & TAG_MASK != TAG_SMALL || (n as i64) < 0 {
        return raise_badarg(ctx);
    }
    let v = (n as i64 >> 3) as u64;
    let mut bytes: Vec<u8> = Vec::new();
    let mut x = v;
    loop {
        bytes.push((x & 0xff) as u8);
        x >>= 8;
        if x == 0 {
            break;
        }
    }
    if little == 0 {
        bytes.reverse();
    }
    bytes_to_new_bin(ctx, &bytes)
}

/// binary:decode_unsigned/1,2.
#[no_mangle]
pub extern "C" fn mana_rt_binary_decode_unsigned(ctx: *mut ProcCtx, bin: u64, little: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if bin_parts(bin).is_none() {
        return raise_badarg(ctx);
    }
    // `little` is 0 (the /1 default) or the endianness atom from /2
    let is_little =
        little & TAG_MASK == TAG_ATOM && atom_bytes(little) == b"little";
    let bytes = bin_bytes(bin).to_vec();
    let le: Vec<u8> = if is_little {
        bytes
    } else {
        bytes.iter().rev().copied().collect()
    };
    let mag = bigint::mag_from_bytes_le(&le);
    make_int_mag(ctx, false, &mag)
}

/// binary:longest_common_prefix/1 (suffix != 0 → suffix variant).
#[no_mangle]
pub extern "C" fn mana_rt_binary_lcp(ctx: *mut ProcCtx, list: u64, suffix: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if list & TAG_MASK != TAG_CONS {
        return raise_badarg(ctx);
    }
    let Ok(bins) = pattern_bins(list) else {
        return raise_badarg(ctx);
    };
    let mut common = usize::MAX;
    let first = bins[0];
    for b in &bins {
        let mut n = 0;
        let max = first.len().min(b.len());
        while n < max {
            let (x, y) = if suffix != 0 {
                (first[first.len() - 1 - n], b[b.len() - 1 - n])
            } else {
                (first[n], b[n])
            };
            if x != y {
                break;
            }
            n += 1;
        }
        common = common.min(n);
    }
    ((common as u64) << 3) | TAG_SMALL
}

// ---------------------------------------------------------------------------
// lists C BIFs (nif_error stubs in lists.erl; native here, definitions
// overridden at codegen so local and remote callers agree)

/// lists:reverse/2.
#[no_mangle]
pub extern "C" fn mana_rt_lists_reverse(ctx: *mut ProcCtx, l: u64, acc0: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, l, acc0];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    while fr[2] != NIL {
        if fr[2] & TAG_MASK != TAG_CONS {
            ctx.roots_head = saved;
            return raise_badarg(ctx);
        }
        let cell = alloc_nursery(ctx, 2);
        let p = (fr[2] & !TAG_MASK) as *const u64;
        unsafe {
            *cell = *p;
            *cell.add(1) = fr[3];
            fr[2] = *p.add(1);
        }
        fr[3] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[3]
}

/// lists:member/2 (=:= comparison). Non-allocating.
#[no_mangle]
pub extern "C" fn mana_rt_lists_member(ctx: *mut ProcCtx, x: u64, l: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut cur = l;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        unsafe {
            if mana_rt_eq_exact(*p, x) == 1 {
                return known().true_a;
            }
            cur = *p.add(1);
        }
    }
    known().false_a
}

/// lists:keyfind/3 (== comparison, like BEAM's CMP). `mode`: 0 = keyfind
/// (tuple | false), 1 = keymember (bool), 2 = keysearch ({value, T} | false).
#[no_mangle]
pub extern "C" fn mana_rt_lists_keyfind(
    ctx: *mut ProcCtx,
    key: u64,
    n: u64,
    l: u64,
    mode: u64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if n & TAG_MASK != TAG_SMALL || (n as i64 >> 3) < 1 {
        return raise_badarg(ctx);
    }
    let idx = (n as i64 >> 3) as u64;
    let mut cur = l;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK == TAG_BOXED && h != 0 {
            let hp = h as *const u64;
            let header = unsafe { *hp };
            if header & 0xff == KIND_TUPLE && header >> 8 >= idx {
                let el = unsafe { *hp.add(idx as usize) };
                if mana_rt_compare(el, key) == 0 {
                    return match mode {
                        1 => known().true_a,
                        2 => {
                            // {value, Tuple}: h may be young — root it
                            let saved = ctx.roots_head;
                            let mut fr = [0u64, 1, h];
                            fr[0] = saved;
                            ctx.roots_head = fr.as_ptr() as u64;
                            let t = alloc_nursery(ctx, 3);
                            ctx.roots_head = saved;
                            unsafe {
                                *t = (2 << 8) | KIND_TUPLE;
                                *t.add(1) = atom_by_name("value");
                                *t.add(2) = fr[2];
                            }
                            t as u64
                        }
                        _ => h,
                    };
                }
            }
        }
        cur = unsafe { *p.add(1) };
    }
    known().false_a
}

/// maps:iterator/1 → {mana_miter, 0, Map}; maps:next/1 walks it in
/// canonical (sorted) key order, returning {K, V, NextIter} | none.
#[no_mangle]
pub extern "C" fn mana_rt_map_iterator(ctx: *mut ProcCtx, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if map_parts(m).is_none() {
        return raise_map_err(ctx, true, m);
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, m];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let t = alloc_nursery(ctx, 4);
    ctx.roots_head = saved;
    unsafe {
        *t = (3 << 8) | KIND_TUPLE;
        *t.add(1) = atom_intern(b"mana_miter");
        *t.add(2) = TAG_SMALL; // small 0
        *t.add(3) = fr[2];
    }
    t as u64
}

#[no_mangle]
pub extern "C" fn mana_rt_map_next(ctx: *mut ProcCtx, iter: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let ok = iter & TAG_MASK == TAG_BOXED
        && iter != 0
        && unsafe { *(iter as *const u64) } == (3 << 8) | KIND_TUPLE
        && unsafe { atom_bytes(*(iter as *const u64).add(1)) } == b"mana_miter";
    if !ok {
        return raise_badarg(ctx);
    }
    let (i, m) = unsafe {
        let p = iter as *const u64;
        ((*p.add(2) as i64 >> 3) as usize, *p.add(3))
    };
    let Some((_, n)) = map_parts(m) else {
        return raise_badarg(ctx);
    };
    if i >= n {
        return find_atom("none").expect("none atom");
    }
    // build the next iterator, then the result tuple, rooting the map
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, m, 0];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let ni = alloc_nursery(ctx, 4);
    unsafe {
        *ni = (3 << 8) | KIND_TUPLE;
        *ni.add(1) = atom_intern(b"mana_miter");
        *ni.add(2) = (((i + 1) as u64) << 3) | TAG_SMALL;
        *ni.add(3) = fr[2];
    }
    fr[3] = ni as u64;
    let t = alloc_nursery(ctx, 4);
    ctx.roots_head = saved;
    unsafe {
        let (p, n) = map_parts(fr[2]).unwrap();
        *t = (3 << 8) | KIND_TUPLE;
        *t.add(1) = *p.add(1 + i);
        *t.add(2) = *p.add(1 + n + i);
        *t.add(3) = fr[3];
    }
    t as u64
}

/// maps:keys/1 and maps:values/1 (`vals != 0`). Key order = canonical.
#[no_mangle]
pub extern "C" fn mana_rt_map_keys(ctx: *mut ProcCtx, m: u64, vals: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, n)) = map_parts(m) else {
        return raise_map_err(ctx, true, m);
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, m, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for i in (0..n).rev() {
        let cell = alloc_nursery(ctx, 2);
        let (p, _) = map_parts(fr[2]).unwrap();
        let item = unsafe {
            if vals != 0 {
                *p.add(1 + n + i)
            } else {
                *p.add(1 + i)
            }
        };
        unsafe {
            *cell = item;
            *cell.add(1) = fr[3];
        }
        fr[3] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[3]
}

/// maps:take/2 → {Value, MapWithoutKey} | error.
#[no_mangle]
pub extern "C" fn mana_rt_map_take(ctx: *mut ProcCtx, key: u64, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if map_parts(m).is_none() {
        return raise_map_err(ctx, true, m);
    }
    let v = mana_rt_map_pat_get(m, key);
    if v == EXC_SENTINEL {
        return atom_error();
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, key, m, v];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let removed = mana_rt_map_remove(ctx as *mut ProcCtx, fr[2], fr[3]);
    if removed == EXC_SENTINEL {
        ctx.roots_head = saved;
        return EXC_SENTINEL;
    }
    fr[3] = removed;
    let t = alloc_nursery(ctx, 3);
    ctx.roots_head = saved;
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = fr[4];
        *t.add(2) = fr[3];
    }
    t as u64
}

/// maps:update_with/3 — apply Fun to the existing value (badkey on miss).
#[no_mangle]
pub extern "C" fn mana_rt_maps_update_with(ctx: *mut ProcCtx, key: u64, fun: u64, m: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    let Some((p, n)) = map_parts(m) else {
        return raise_map_err(ctxr, true, m);
    };
    if map_index(p, n, key).is_err() {
        return raise_map_err(ctxr, false, key);
    }
    let old = mana_rt_map_pat_get(m, key);
    let saved = ctxr.roots_head;
    let mut fr = [0u64, 2, key, m];
    fr[0] = saved;
    ctxr.roots_head = fr.as_ptr() as u64;
    let c1 = alloc_nursery(ctxr, 2);
    unsafe {
        *c1 = old;
        *c1.add(1) = NIL;
    }
    let newv = mana_rt_apply_fun(ctx, fun, c1 as u64 | TAG_CONS);
    if newv == EXC_SENTINEL {
        ctxr.roots_head = saved;
        return EXC_SENTINEL;
    }
    let key2 = fr[2];
    let m2 = fr[3];
    ctxr.roots_head = saved;
    mana_rt_map_put(ctx, key2, newv, m2)
}

/// maps:update_with/4 — like /3 but inserts Init when the key is absent.
#[no_mangle]
pub extern "C" fn mana_rt_maps_update_with4(
    ctx: *mut ProcCtx,
    key: u64,
    fun: u64,
    init: u64,
    m: u64,
) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    let Some((p, n)) = map_parts(m) else {
        return raise_map_err(ctxr, true, m);
    };
    if map_index(p, n, key).is_err() {
        return mana_rt_map_put(ctx, key, init, m);
    }
    mana_rt_maps_update_with(ctx, key, fun, m)
}

/// maps:with/2 / maps:without/2 — key-list subset / complement.
#[no_mangle]
pub extern "C" fn mana_rt_maps_with(ctx: *mut ProcCtx, keys: u64, m: u64, keep: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    let Some((_, _)) = map_parts(m) else {
        return raise_map_err(ctxr, true, m);
    };
    // collect wanted keys (immediates or heap terms; compared by eq_exact)
    let mut want: Vec<u64> = Vec::new();
    let mut cur = keys;
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        want.push(unsafe { *p });
        cur = unsafe { *p.add(1) };
    }
    let saved = ctxr.roots_head;
    let mut fr = [0u64, 2, m, NIL];
    fr[0] = saved;
    ctxr.roots_head = fr.as_ptr() as u64;
    // build result by folding put over matching pairs (m stays rooted)
    let mut acc = {
        let e = alloc_nursery(ctxr, 1);
        unsafe { *e = KIND_MAP }; // empty map header
        e as u64
    };
    fr[3] = acc;
    let n = map_parts(fr[2]).unwrap().1;
    for i in 0..n {
        let (p, _) = map_parts(fr[2]).unwrap();
        let (k, v) = unsafe { (*p.add(1 + i), *p.add(1 + n + i)) };
        let matched = want.iter().any(|&w| mana_rt_eq_exact(w, k) == 1);
        let include = if keep != 0 { matched } else { !matched };
        if include {
            let r = mana_rt_map_put(ctx, k, v, fr[3]);
            if r == EXC_SENTINEL {
                ctxr.roots_head = saved;
                return EXC_SENTINEL;
            }
            fr[3] = r;
        }
    }
    acc = fr[3];
    ctxr.roots_head = saved;
    acc
}

/// maps:foreach/2 — Fun(K, V) per pair, returns ok.
#[no_mangle]
pub extern "C" fn mana_rt_maps_foreach(ctx: *mut ProcCtx, fun: u64, m: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    if map_parts(m).is_none() {
        return raise_map_err(ctxr, true, m);
    }
    let saved = ctxr.roots_head;
    let mut fr = [0u64, 2, fun, m];
    fr[0] = saved;
    ctxr.roots_head = fr.as_ptr() as u64;
    let n = map_parts(fr[3]).unwrap().1;
    for i in 0..n {
        let (p, _) = map_parts(fr[3]).unwrap();
        let (k, v) = unsafe { (*p.add(1 + i), *p.add(1 + n + i)) };
        let mut fr2 = [0u64, 2, k, v];
        fr2[0] = ctxr.roots_head;
        ctxr.roots_head = fr2.as_ptr() as u64;
        let c2 = alloc_nursery(ctxr, 2);
        unsafe {
            *c2 = fr2[3];
            *c2.add(1) = NIL;
        }
        let c1 = alloc_nursery(ctxr, 2);
        unsafe {
            *c1 = fr2[2];
            *c1.add(1) = c2 as u64 | TAG_CONS;
        }
        ctxr.roots_head = fr2[0];
        let r = mana_rt_apply_fun(ctx, fr[2], c1 as u64 | TAG_CONS);
        if r == EXC_SENTINEL {
            ctxr.roots_head = saved;
            return EXC_SENTINEL;
        }
    }
    ctxr.roots_head = saved;
    atom_intern(b"ok")
}

/// maps:merge_with/3 — merge with a conflict fun (calls back into compiled
/// code; everything rooted around the callbacks).
#[no_mangle]
pub extern "C" fn mana_rt_maps_merge_with(ctx: *mut ProcCtx, fun: u64, m1: u64, m2: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if map_parts(m1).is_none() {
        return raise_map_err(ctx, true, m1);
    }
    if map_parts(m2).is_none() {
        return raise_map_err(ctx, true, m2);
    }
    // acc starts as m1; for each pair in m2: put or resolve via fun
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, fun, m1, m2];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let n2 = map_parts(fr[4]).unwrap().1;
    for i in 0..n2 {
        let (p2, _) = map_parts(fr[4]).unwrap();
        let (k, v2) = unsafe { (*p2.add(1 + i), *p2.add(1 + n2 + i)) };
        let existing = mana_rt_map_pat_get(fr[3], k);
        let newv = if existing == EXC_SENTINEL {
            v2
        } else {
            // fun(K, V1, V2) — build the args list rooted
            let mut fr2 = [0u64, 3, k, existing, v2];
            fr2[0] = ctx.roots_head;
            ctx.roots_head = fr2.as_ptr() as u64;
            let c3 = alloc_nursery(ctx, 2);
            unsafe {
                *c3 = fr2[4];
                *c3.add(1) = NIL;
            }
            let c2 = alloc_nursery(ctx, 2);
            unsafe {
                *c2 = fr2[3];
                *c2.add(1) = c3 as u64 | TAG_CONS;
            }
            let c1 = alloc_nursery(ctx, 2);
            unsafe {
                *c1 = fr2[2];
                *c1.add(1) = c2 as u64 | TAG_CONS;
            }
            ctx.roots_head = fr2[0];
            let r = mana_rt_apply_fun(ctx as *mut ProcCtx, fr[2], c1 as u64 | TAG_CONS);
            if r == EXC_SENTINEL {
                ctx.roots_head = saved;
                return EXC_SENTINEL;
            }
            r
        };
        // re-read the key (allocs may have moved m2)
        let (p2, _) = map_parts(fr[4]).unwrap();
        let k2 = unsafe { *p2.add(1 + i) };
        let merged = mana_rt_map_put(ctx as *mut ProcCtx, k2, newv, fr[3]);
        if merged == EXC_SENTINEL {
            ctx.roots_head = saved;
            return EXC_SENTINEL;
        }
        fr[3] = merged;
    }
    ctx.roots_head = saved;
    fr[3]
}

/// maps:fold/3 — calls back into compiled code (the fun), so the map, fun,
/// and accumulator are rooted and reloaded around every callback.
#[no_mangle]
pub extern "C" fn mana_rt_maps_fold(ctx: *mut ProcCtx, fun: u64, acc0: u64, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, n)) = map_parts(m) else {
        return raise_map_err(ctx, true, m);
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, fun, acc0, m];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for i in 0..n {
        let (p, _) = map_parts(fr[4]).unwrap();
        let (k, v) = unsafe { (*p.add(1 + i), *p.add(1 + n + i)) };
        // args list for apply_fun: build 3 cells rooted via fr (k/v read
        // fresh from the rooted map, acc in fr[3])
        let c3 = alloc_nursery(ctx, 2);
        unsafe {
            *c3 = fr[3];
            *c3.add(1) = NIL;
        }
        // re-read k/v: the alloc above may have moved the map
        let (p, _) = map_parts(fr[4]).unwrap();
        let v2 = unsafe { *p.add(1 + n + i) };
        let c2 = alloc_nursery(ctx, 2);
        unsafe {
            *c2 = v2;
            *c2.add(1) = c3 as u64 | TAG_CONS;
        }
        let (p, _) = map_parts(fr[4]).unwrap();
        let k2 = unsafe { *p.add(1 + i) };
        let c1 = alloc_nursery(ctx, 2);
        unsafe {
            *c1 = k2;
            *c1.add(1) = c2 as u64 | TAG_CONS;
        }
        let _ = (k, v);
        let args = c1 as u64 | TAG_CONS;
        let r = mana_rt_apply_fun(ctx, fr[2], args);
        if r == EXC_SENTINEL {
            ctx.roots_head = saved;
            return EXC_SENTINEL;
        }
        fr[3] = r;
    }
    ctx.roots_head = saved;
    fr[3]
}

// ---------------------------------------------------------------------------
// ets + application env (native cuts): one global store of eternal deep
// copies. Enough for elixir_config-style tables — TODO(ets): match specs,
// ordered tables, delete_all, GC of replaced values.

type KvStore = std::sync::Mutex<Option<Vec<(u64, u64, u64)>>>; // (tab, key, tuple)
static ETS_STORE: KvStore = std::sync::Mutex::new(None);

fn kv_find(rows: &[(u64, u64, u64)], tab: u64, key: u64) -> Option<usize> {
    rows.iter()
        .position(|&(t, k, _)| t == tab && mana_rt_eq_exact(k, key) == 1)
}

/// ets:insert/2 with a tuple or list of tuples (keypos 1); insert_new when
/// `new != 0`.
#[no_mangle]
pub extern "C" fn mana_rt_ets_insert(ctx: *mut ProcCtx, tab: u64, obj: u64, new: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let known = known();
    let mut objs = Vec::new();
    if obj & TAG_MASK == TAG_CONS || obj == NIL {
        let mut cur = obj;
        while cur != NIL {
            if cur & TAG_MASK != TAG_CONS {
                return raise_badarg(ctx);
            }
            let p = (cur & !TAG_MASK) as *const u64;
            unsafe {
                objs.push(*p);
                cur = *p.add(1);
            }
        }
    } else {
        objs.push(obj);
    }
    let kind = ets_kind(tab);
    let mut guard = ETS_STORE.lock().unwrap();
    let rows = guard.get_or_insert_with(Vec::new);
    for o in objs {
        let ok = o & TAG_MASK == TAG_BOXED
            && o != 0
            && unsafe { *(o as *const u64) } & 0xff == KIND_TUPLE
            && unsafe { *(o as *const u64) } >> 8 >= 1;
        if !ok {
            return raise_badarg(ctx);
        }
        let key = unsafe { *(o as *const u64).add(1) };
        match kind {
            ETS_SET => match kv_find(rows, tab, key) {
                Some(i) => {
                    if new != 0 {
                        return known.false_a;
                    }
                    rows[i].2 = eternal_deep_copy(o);
                }
                None => {
                    let copy = eternal_deep_copy(o);
                    let ckey = unsafe { *(copy as *const u64).add(1) };
                    rows.push((tab, ckey, copy));
                }
            },
            _ => {
                // bag dedups exact-equal objects; duplicate_bag always
                // appends. Rows keep insertion order.
                let dup = kind == ETS_BAG
                    && rows.iter().any(|&(t, k, v)| {
                        t == tab
                            && mana_rt_eq_exact(k, key) == 1
                            && mana_rt_eq_exact(v, o) == 1
                    });
                if !dup {
                    let copy = eternal_deep_copy(o);
                    let ckey = unsafe { *(copy as *const u64).add(1) };
                    rows.push((tab, ckey, copy));
                }
            }
        }
    }
    known.true_a
}

/// ets:lookup/2 → list of all stored tuples for the key, in insertion
/// order (bags may hold several — eternal, safe to share).
#[no_mangle]
pub extern "C" fn mana_rt_ets_lookup(ctx: *mut ProcCtx, tab: u64, key: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let found: Vec<u64> = {
        let guard = ETS_STORE.lock().unwrap();
        guard
            .as_ref()
            .map(|rows| {
                rows.iter()
                    .filter(|&&(t, k, _)| t == tab && mana_rt_eq_exact(k, key) == 1)
                    .map(|&(_, _, v)| v)
                    .collect()
            })
            .unwrap_or_default()
    };
    // rows are eternal — build the list newest-cons-last (reverse iter)
    let mut out = NIL;
    for &tuple in found.iter().rev() {
        let mut fr = [ctx.roots_head, 1, out];
        ctx.roots_head = fr.as_ptr() as u64;
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = tuple;
            *cell.add(1) = fr[2];
        }
        ctx.roots_head = fr[0];
        out = cell as u64 | TAG_CONS;
        let _ = &mut fr;
    }
    out
}

/// ets:delete/2 (by key) — removes every row for the key (bag semantics).
#[no_mangle]
pub extern "C" fn mana_rt_ets_delete(_ctx: *mut ProcCtx, tab: u64, key: u64) -> u64 {
    let mut guard = ETS_STORE.lock().unwrap();
    if let Some(rows) = guard.as_mut() {
        rows.retain(|&(t, k, _)| !(t == tab && mana_rt_eq_exact(k, key) == 1));
    }
    known().true_a
}

/// Restricted ets match pattern: literals (eq_exact), '_' wildcard,
/// '$N' captures. Captures append to `caps` tagged with N.
fn ets_match_term(pat: u64, val: u64, caps: &mut Vec<(i64, u64)>) -> bool {
    if pat & TAG_MASK == TAG_ATOM {
        let b = atom_bytes(pat);
        if b == b"_" {
            return true;
        }
        if b.len() >= 2 && b[0] == b'$' && b[1..].iter().all(|c| c.is_ascii_digit()) {
            let n: i64 = std::str::from_utf8(&b[1..]).unwrap().parse().unwrap_or(0);
            caps.push((n, val));
            return true;
        }
        return pat == val;
    }
    if pat & TAG_MASK == TAG_BOXED && pat != 0 && val & TAG_MASK == TAG_BOXED && val != 0 {
        unsafe {
            let (pp, vp) = (pat as *const u64, val as *const u64);
            if *pp & 0xff == KIND_TUPLE && *vp & 0xff == KIND_TUPLE {
                let n = (*pp >> 8) as usize;
                if (*vp >> 8) as usize != n {
                    return false;
                }
                for i in 1..=n {
                    if !ets_match_term(*pp.add(i), *vp.add(i), caps) {
                        return false;
                    }
                }
                return true;
            }
        }
    }
    if pat & TAG_MASK == TAG_CONS && val & TAG_MASK == TAG_CONS {
        unsafe {
            let (pp, vp) = ((pat & !TAG_MASK) as *const u64, (val & !TAG_MASK) as *const u64);
            return ets_match_term(*pp, *vp, caps)
                && ets_match_term(*pp.add(1), *vp.add(1), caps);
        }
    }
    mana_rt_eq_exact(pat, val) == 1
}

/// ets:match/2 — list of capture lists ('$N' order), insertion order.
#[no_mangle]
pub extern "C" fn mana_rt_ets_match(ctx: *mut ProcCtx, tab: u64, pattern: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let rows: Vec<u64> = {
        let guard = ETS_STORE.lock().unwrap();
        guard
            .as_ref()
            .map(|rows| {
                rows.iter()
                    .filter(|(t, _, _)| mana_rt_eq_exact(*t, tab) == 1)
                    .map(|&(_, _, v)| v)
                    .collect()
            })
            .unwrap_or_default()
    };
    // rows are eternal (deep-copied at insert) — safe across allocs
    let mut matches: Vec<Vec<u64>> = Vec::new();
    for row in rows {
        let mut caps: Vec<(i64, u64)> = Vec::new();
        if ets_match_term(pattern, row, &mut caps) {
            caps.sort_by_key(|&(n, _)| n);
            matches.push(caps.into_iter().map(|(_, v)| v).collect());
        }
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for caps in matches.iter().rev() {
        let mut inner = NIL;
        for &v in caps.iter().rev() {
            let cell = alloc_nursery(ctx, 2);
            unsafe {
                *cell = v;
                *cell.add(1) = inner;
            }
            inner = cell as u64 | TAG_CONS;
        }
        fr[3] = inner;
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = fr[3];
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
    }
    let out = fr[2];
    ctx.roots_head = saved;
    out
}

/// Known-table registry: (eternal name term, kind). Kind drives insert
/// dedup and the shape of lookup_element. Unregistered tables (the app-env
/// tag) default to Set.
static ETS_TABLES: std::sync::Mutex<Vec<(u64, u8)>> = std::sync::Mutex::new(Vec::new());

const ETS_SET: u8 = 0;
const ETS_BAG: u8 = 1;
const ETS_DUP_BAG: u8 = 2;

/// Kind of a table by name term; Set for anything not registered.
fn ets_kind(tab: u64) -> u8 {
    let tabs = ETS_TABLES.lock().unwrap();
    tabs.iter()
        .find(|&&(t, _)| mana_rt_eq_exact(t, tab) == 1)
        .map(|&(_, k)| k)
        .unwrap_or(ETS_SET)
}

/// ets:new/2 — registers the (named) table and records its kind from the
/// options (`bag` / `duplicate_bag` / `ordered_set` → Set + TODO(ets); all
/// other options ignored).
#[no_mangle]
pub extern "C" fn mana_rt_ets_new(_ctx: *mut ProcCtx, name: u64, opts: u64) -> u64 {
    let mut kind = ETS_SET;
    let mut cur = opts;
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        let opt = unsafe { *p };
        cur = unsafe { *p.add(1) };
        if opt & TAG_MASK == TAG_ATOM {
            match atom_bytes(opt) {
                b"bag" => kind = ETS_BAG,
                b"duplicate_bag" => kind = ETS_DUP_BAG,
                _ => {}
            }
        }
    }
    let mut tabs = ETS_TABLES.lock().unwrap();
    match tabs.iter().position(|&(t, _)| mana_rt_eq_exact(t, name) == 1) {
        Some(i) => tabs[i].1 = kind,
        None => tabs.push((eternal_deep_copy(name), kind)),
    }
    name
}

/// Seed the `elixir_config` ets table with the URI scheme → default-port
/// entries that `elixir:start/2` inserts on BEAM (`{{uri, <<"http">>}, 80}`
/// …). The closed world never runs the :elixir application boot, so
/// URI.default_port/1 (→ elixir_config:get({uri, Scheme})) would return nil
/// and any HTTP request whose Host header omits a port would then crash in
/// the response path. Called once from the generated main.
#[no_mangle]
pub extern "C" fn mana_rt_seed_uri_defaults(ctx: *mut ProcCtx) {
    let ctx = unsafe { &mut *ctx };
    let tab = atom_intern(b"elixir_config");
    let uri = atom_intern(b"uri");
    let defaults: &[(&[u8], i64)] = &[
        (b"ftp", 21),
        (b"sftp", 22),
        (b"tftp", 69),
        (b"http", 80),
        (b"https", 443),
        (b"ldap", 389),
        (b"ws", 80),
        (b"wss", 443),
    ];
    for &(scheme, port) in defaults {
        let sbin = bytes_to_new_bin(ctx, scheme);
        // root sbin across the two tuple allocs
        let mut fr = [ctx.roots_head, 1, sbin];
        ctx.roots_head = fr.as_ptr() as u64;
        let key = alloc_nursery(ctx, 3);
        unsafe {
            *key = (2 << 8) | KIND_TUPLE;
            *key.add(1) = uri;
            *key.add(2) = fr[2];
        }
        fr[2] = key as u64;
        let row = alloc_nursery(ctx, 3);
        unsafe {
            *row = (2 << 8) | KIND_TUPLE;
            *row.add(1) = fr[2];
            *row.add(2) = ((port << 3) as u64) | TAG_SMALL;
        }
        ctx.roots_head = fr[0];
        let _ = &mut fr;
        mana_rt_ets_insert(ctx, tab, row as u64, 0);
    }
}

// ---------------------------------------------------------------------------
// Public native-author ABI. These are the ONLY symbols a hex package's
// native/ crate (via the mana-native wrapper) calls to build/inspect terms.
// Everything else in this file is private runtime internals. Terms are
// tagged u64; the first arg is the ProcCtx (the codegen contract). Term
// construction that allocates may trigger GC — the caller (mana-native's
// Env) roots live terms across allocations.

/// Bump-allocate `words` on the process nursery; may GC. Returns a raw
/// heap pointer the caller fills with a header + term words. The caller
/// must read any live child terms from its root frame AFTER this call
/// (GC may have moved them).
#[no_mangle]
pub extern "C" fn mana_rt_native_alloc(ctx: *mut ProcCtx, words: u64) -> *mut u64 {
    let ctx = unsafe { &mut *ctx };
    alloc_nursery(ctx, words as usize)
}

/// Build a binary term from raw bytes (copied — the source is not a term,
/// so no rooting needed).
#[no_mangle]
pub extern "C" fn mana_rt_native_make_binary(
    ctx: *mut ProcCtx,
    ptr: *const u8,
    len: usize,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    bytes_to_new_bin(ctx, bytes)
}

/// Build an integer term (small or bignum, normalized).
#[no_mangle]
pub extern "C" fn mana_rt_native_make_int(ctx: *mut ProcCtx, v: i64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    make_int_mag(ctx, v < 0, &[v.unsigned_abs()])
}

/// Build an unsigned integer term (small or bignum) — for JSON numbers
/// that exceed i64 range.
#[no_mangle]
pub extern "C" fn mana_rt_native_make_uint(ctx: *mut ProcCtx, v: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    make_int_mag(ctx, false, &[v])
}

/// Build a boxed float term.
#[no_mangle]
pub extern "C" fn mana_rt_native_make_float(ctx: *mut ProcCtx, v: f64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    box_float(ctx, v)
}

/// Intern an atom from raw bytes (atoms are eternal — no ctx / no GC).
#[no_mangle]
pub extern "C" fn mana_rt_native_make_atom(ptr: *const u8, len: usize) -> u64 {
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    atom_intern(bytes)
}

/// Raise `badarg` from native code (sets the exception cells, returns the
/// sentinel the caller returns to unwind).
#[no_mangle]
pub extern "C" fn mana_rt_native_raise_badarg(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &mut *ctx };
    raise_badarg(ctx)
}

/// Inspection: if `t` is a binary or sub-binary view, write its current
/// data pointer + length and return 1; else return 0. (Handles the view's
/// GC-recomputed data pointer so mana-native need not duplicate that.)
#[no_mangle]
pub extern "C" fn mana_rt_native_bin_parts(
    t: u64,
    out_ptr: *mut *const u8,
    out_len: *mut usize,
) -> u8 {
    match bin_parts(t) {
        Some((p, len)) => {
            unsafe {
                *out_ptr = p;
                *out_len = len;
            }
            1
        }
        None => 0,
    }
}

/// Inspection: write the decimal digits of any integer term (small or
/// bignum) into a caller-provided buffer, snprintf-style — returns the
/// full digit count (which may exceed `cap`; the caller retries with a
/// bigger buffer), or `usize::MAX` if `t` is not an integer. Allocates
/// NOTHING on the process heap, so it is safe to call while walking an
/// unrooted term during JSON encode.
#[no_mangle]
pub extern "C" fn mana_rt_native_int_decimal(t: u64, out: *mut u8, cap: usize) -> usize {
    match int_term_digits(t, 10) {
        Some(s) => {
            let b = s.as_bytes();
            let n = b.len().min(cap);
            unsafe {
                std::ptr::copy_nonoverlapping(b.as_ptr(), out, n);
            }
            b.len()
        }
        None => usize::MAX,
    }
}

#[no_mangle]
pub extern "C" fn mana_rt_ets_info(_ctx: *mut ProcCtx, tab: u64) -> u64 {
    let tabs = ETS_TABLES.lock().unwrap();
    if tabs.iter().any(|&(t, _)| mana_rt_eq_exact(t, tab) == 1) {
        NIL
    } else {
        known().undefined
    }
}

/// ets:match_delete/2 — drop matching rows.
#[no_mangle]
pub extern "C" fn mana_rt_ets_match_delete(_ctx: *mut ProcCtx, tab: u64, pattern: u64) -> u64 {
    let mut guard = ETS_STORE.lock().unwrap();
    if let Some(rows) = guard.as_mut() {
        rows.retain(|&(t, _, v)| {
            if mana_rt_eq_exact(t, tab) != 1 {
                return true;
            }
            let mut caps = Vec::new();
            !ets_match_term(pattern, v, &mut caps)
        });
    }
    known().true_a
}

/// ets:member/2 — true if any object has the key.
#[no_mangle]
pub extern "C" fn mana_rt_ets_member(_ctx: *mut ProcCtx, tab: u64, key: u64) -> u64 {
    let k = known();
    let guard = ETS_STORE.lock().unwrap();
    let hit = guard
        .as_ref()
        .map(|rows| {
            rows.iter()
                .any(|&(t, rk, _)| t == tab && mana_rt_eq_exact(rk, key) == 1)
        })
        .unwrap_or(false);
    if hit {
        k.true_a
    } else {
        k.false_a
    }
}

/// ets:delete_object/2 — remove every row whose stored object equals the
/// given one (Registry's per-key unsubscribe cleanup).
#[no_mangle]
pub extern "C" fn mana_rt_ets_delete_object(ctx: *mut ProcCtx, tab: u64, obj: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let ok = obj & TAG_MASK == TAG_BOXED
        && obj != 0
        && unsafe { *(obj as *const u64) } & 0xff == KIND_TUPLE
        && unsafe { *(obj as *const u64) } >> 8 >= 1;
    if !ok {
        return raise_badarg(ctx);
    }
    let key = unsafe { *(obj as *const u64).add(1) };
    let mut guard = ETS_STORE.lock().unwrap();
    if let Some(rows) = guard.as_mut() {
        rows.retain(|&(t, k, v)| {
            !(t == tab && mana_rt_eq_exact(k, key) == 1 && mana_rt_eq_exact(v, obj) == 1)
        });
    }
    known().true_a
}

/// ets:take/2 — return all objects for the key (as ets:lookup would) and
/// remove them.
#[no_mangle]
pub extern "C" fn mana_rt_ets_take(ctx: *mut ProcCtx, tab: u64, key: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let found: Vec<u64> = {
        let mut guard = ETS_STORE.lock().unwrap();
        match guard.as_mut() {
            Some(rows) => {
                let hits = rows
                    .iter()
                    .filter(|&&(t, k, _)| t == tab && mana_rt_eq_exact(k, key) == 1)
                    .map(|&(_, _, v)| v)
                    .collect();
                rows.retain(|&(t, k, _)| !(t == tab && mana_rt_eq_exact(k, key) == 1));
                hits
            }
            None => Vec::new(),
        }
    };
    let mut out = NIL;
    for &tuple in found.iter().rev() {
        let mut fr = [ctx.roots_head, 1, out];
        ctx.roots_head = fr.as_ptr() as u64;
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = tuple;
            *cell.add(1) = fr[2];
        }
        ctx.roots_head = fr[0];
        out = cell as u64 | TAG_CONS;
        let _ = &mut fr;
    }
    out
}

/// Count rows of `tab` matching a restricted select head (guards must be
/// empty). Shared by select_count and select_delete.
fn ets_select_matches(spec: u64, tab: u64, out_heads: &mut Vec<u64>) -> Result<usize, ()> {
    // parse [{Head, [], _Body}] — heads only, guards must be []
    let mut heads: Vec<u64> = Vec::new();
    let mut cur = spec;
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        let clause = unsafe { *p };
        cur = unsafe { *p.add(1) };
        if clause & TAG_MASK != TAG_BOXED || clause == 0 {
            return Err(());
        }
        unsafe {
            let cp = clause as *const u64;
            if *cp != (3 << 8) | KIND_TUPLE {
                return Err(());
            }
            if *cp.add(2) != NIL {
                return Err(()); // TODO(ets): guards
            }
            heads.push(*cp.add(1));
        }
    }
    let guard = ETS_STORE.lock().unwrap();
    let mut count = 0usize;
    if let Some(rows) = guard.as_ref() {
        for &(t, _, v) in rows {
            if t != tab {
                continue;
            }
            for &h in &heads {
                let mut caps = Vec::new();
                if ets_match_term(h, v, &mut caps) {
                    count += 1;
                    out_heads.push(v);
                    break;
                }
            }
        }
    }
    Ok(count)
}

/// ets:select_count/2 — number of objects matching the spec (empty guards).
#[no_mangle]
pub extern "C" fn mana_rt_ets_select_count(ctx: *mut ProcCtx, tab: u64, spec: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut hits = Vec::new();
    match ets_select_matches(spec, tab, &mut hits) {
        Ok(n) => ((n as u64) << 3) | TAG_SMALL,
        Err(()) => raise_badarg(ctx),
    }
}

/// ets:select_delete/2 — delete objects matching the spec, return the count.
#[no_mangle]
pub extern "C" fn mana_rt_ets_select_delete(ctx: *mut ProcCtx, tab: u64, spec: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut hits: Vec<u64> = Vec::new();
    let n = match ets_select_matches(spec, tab, &mut hits) {
        Ok(n) => n,
        Err(()) => return raise_badarg(ctx),
    };
    let mut guard = ETS_STORE.lock().unwrap();
    if let Some(rows) = guard.as_mut() {
        rows.retain(|&(t, _, v)| {
            !(t == tab && hits.iter().any(|&h| mana_rt_eq_exact(h, v) == 1))
        });
    }
    ((n as u64) << 3) | TAG_SMALL
}

/// Match-spec BODY term substitution: '$N' → capture, '$_' → object,
/// '$$' → all captures, {X} (arity-1 tuple) → tuple-escape of X.
fn ets_subst_body(ctx: &mut ProcCtx, body: u64, caps: &[(i64, u64)], obj: u64) -> u64 {
    if body & TAG_MASK == TAG_ATOM {
        let b = atom_bytes(body);
        if b == b"$_" {
            return obj;
        }
        if b == b"$$" {
            let mut list = NIL;
            let mut sorted: Vec<&(i64, u64)> = caps.iter().collect();
            sorted.sort_by_key(|&&(n, _)| n);
            for &&(_, v) in sorted.iter().rev() {
                let cell = alloc_nursery(ctx, 2);
                unsafe {
                    *cell = v;
                    *cell.add(1) = list;
                }
                list = cell as u64 | TAG_CONS;
            }
            return list;
        }
        if b.len() >= 2 && b[0] == b'$' && b[1..].iter().all(|c| c.is_ascii_digit()) {
            let n: i64 = std::str::from_utf8(&b[1..]).unwrap().parse().unwrap_or(0);
            if let Some(&(_, v)) = caps.iter().find(|&&(cn, _)| cn == n) {
                return v;
            }
        }
        return body;
    }
    if body & TAG_MASK == TAG_BOXED && body != 0 {
        unsafe {
            let p = body as *const u64;
            if *p & 0xff == KIND_TUPLE && (*p >> 8) == 1 {
                // {X}: tuple escape — X built literally (with substitution)
                let inner = *p.add(1);
                if inner & TAG_MASK == TAG_BOXED
                    && inner != 0
                    && *(inner as *const u64) & 0xff == KIND_TUPLE
                {
                    let ip = inner as *const u64;
                    let n = (*ip >> 8) as usize;
                    // substitute fields first (rooted), then build
                    let saved = ctx.roots_head;
                    let mut fields: Vec<u64> = Vec::with_capacity(n);
                    let mut fr = vec![0u64; 2 + n];
                    fr[0] = saved;
                    fr[1] = n as u64;
                    ctx.roots_head = fr.as_ptr() as u64;
                    for i in 0..n {
                        let ip = inner as *const u64; // re-derive (may move? inner unrooted!)
                        let fv = ets_subst_body(ctx, *ip.add(1 + i), caps, obj);
                        fr[2 + i] = fv;
                        fields.push(0);
                    }
                    let t = alloc_nursery(ctx, 1 + n);
                    unsafe {
                        *t = ((n as u64) << 8) | KIND_TUPLE;
                        for i in 0..n {
                            *t.add(1 + i) = fr[2 + i];
                        }
                    }
                    let _ = fields;
                    ctx.roots_head = saved;
                    return t as u64;
                }
            }
        }
    }
    body
}

/// ets:select/2 — restricted match specs [{Head, [], [Body]}] (no guards).
#[no_mangle]
pub extern "C" fn mana_rt_ets_select(ctx: *mut ProcCtx, tab: u64, spec: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    // parse the spec list: [{Head, Guards, [Body]}]
    let mut clauses: Vec<(u64, u64)> = Vec::new(); // (head, body)
    let mut cur = spec;
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        let clause = unsafe { *p };
        cur = unsafe { *p.add(1) };
        if clause & TAG_MASK != TAG_BOXED || clause == 0 {
            return raise_badarg(ctx);
        }
        unsafe {
            let cp = clause as *const u64;
            if *cp != (3 << 8) | KIND_TUPLE {
                return raise_badarg(ctx);
            }
            let guards = *cp.add(2);
            if guards != NIL {
                return raise_badarg(ctx); // TODO(ets): guards
            }
            let body_list = *cp.add(3);
            if body_list & TAG_MASK != TAG_CONS {
                return raise_badarg(ctx);
            }
            let bp = (body_list & !TAG_MASK) as *const u64;
            clauses.push((*cp.add(1), *bp));
        }
    }
    let rows: Vec<u64> = {
        let guard = ETS_STORE.lock().unwrap();
        guard
            .as_ref()
            .map(|rows| {
                rows.iter()
                    .filter(|(t, _, _)| mana_rt_eq_exact(*t, tab) == 1)
                    .map(|&(_, _, v)| v)
                    .collect()
            })
            .unwrap_or_default()
    };
    // results built under a root frame; rows/spec terms are eternal or
    // caller-live respectively (spec is not used after parsing... heads
    // and bodies are caller terms — no alloc happens between uses except
    // inside subst which re-reads from the parsed immediates)
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let mut results: Vec<u64> = Vec::new();
    for row in rows {
        for &(head, body) in &clauses {
            let mut caps = Vec::new();
            if ets_match_term(head, row, &mut caps) {
                caps.sort_by_key(|&(n, _)| n);
                results.push(ets_subst_body(ctx, body, &caps, row));
                break;
            }
        }
        // keep already-built results rooted as a growing list
        while let Some(r) = results.pop() {
            fr[3] = r;
            let cell = alloc_nursery(ctx, 2);
            unsafe {
                *cell = fr[3];
                *cell.add(1) = fr[2];
            }
            fr[2] = cell as u64 | TAG_CONS;
        }
    }
    // reverse into final order
    let mut out = NIL;
    fr[3] = NIL;
    let mut cur = fr[2];
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        let v = unsafe { *p };
        cur = unsafe { *p.add(1) };
        fr[2] = cur; // remaining source stays rooted
        let mut fr3 = [0u64, 2, v, out];
        fr3[0] = ctx.roots_head;
        ctx.roots_head = fr3.as_ptr() as u64;
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = fr3[2];
            *cell.add(1) = fr3[3];
        }
        ctx.roots_head = fr3[0];
        out = cell as u64 | TAG_CONS;
        fr[3] = out;
    }
    ctx.roots_head = saved;
    out
}

/// ets:lookup_element/3 — badarg on missing table/key (Bandit.Clock's
/// date_header rescues the resulting ArgumentError to compute a fallback).
/// For bag / duplicate_bag tables the result is the LIST of the Pos-th
/// elements across every object with the key, in insertion order (this is
/// what Phoenix.Registry.dispatch consumes).
#[no_mangle]
pub extern "C" fn mana_rt_ets_lookup_element(
    ctx: *mut ProcCtx,
    tab: u64,
    key: u64,
    pos: u64,
) -> u64 {
    match ets_lookup_element_impl(ctx, tab, key, pos) {
        Ok(v) => v,
        Err(true) => raise_badarg(unsafe { &mut *ctx }),
        // empty on a /3 call is badarg
        Err(false) => raise_badarg(unsafe { &mut *ctx }),
    }
}

/// ets:lookup_element/4 — like /3 but returns Default when the key is
/// absent instead of raising (pg:get_members/2 relies on this).
#[no_mangle]
pub extern "C" fn mana_rt_ets_lookup_element4(
    ctx: *mut ProcCtx,
    tab: u64,
    key: u64,
    pos: u64,
    default: u64,
) -> u64 {
    match ets_lookup_element_impl(ctx, tab, key, pos) {
        Ok(v) => v,
        Err(true) => raise_badarg(unsafe { &mut *ctx }),
        Err(false) => default, // key absent → default
    }
}

/// Shared body: Ok(term) on success, Err(true) on a genuine badarg (bad
/// pos or malformed tuple), Err(false) when the key has no rows.
fn ets_lookup_element_impl(ctx: *mut ProcCtx, tab: u64, key: u64, pos: u64) -> Result<u64, bool> {
    let ctx = unsafe { &mut *ctx };
    if pos & TAG_MASK != TAG_SMALL || (pos as i64 >> 3) < 1 {
        return Err(true);
    }
    let n = (pos as i64 >> 3) as usize;
    let found: Vec<u64> = {
        let guard = ETS_STORE.lock().unwrap();
        guard
            .as_ref()
            .map(|rows| {
                rows.iter()
                    .filter(|&&(t, k, _)| t == tab && mana_rt_eq_exact(k, key) == 1)
                    .map(|&(_, _, v)| v)
                    .collect()
            })
            .unwrap_or_default()
    };
    if found.is_empty() {
        return Err(false);
    }
    // element at position n of each stored tuple (all eternal)
    let mut elems: Vec<u64> = Vec::with_capacity(found.len());
    for tuple in found {
        unsafe {
            let p = tuple as *const u64;
            if tuple & TAG_MASK != TAG_BOXED || *p & 0xff != KIND_TUPLE || n > (*p >> 8) as usize {
                return Err(true);
            }
            elems.push(*p.add(n));
        }
    }
    if ets_kind(tab) == ETS_SET {
        return Ok(elems[0]);
    }
    // bag: return the list of elements, insertion order
    let mut out = NIL;
    for &e in elems.iter().rev() {
        let mut fr = [ctx.roots_head, 1, out];
        ctx.roots_head = fr.as_ptr() as u64;
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = e;
            *cell.add(1) = fr[2];
        }
        ctx.roots_head = fr[0];
        out = cell as u64 | TAG_CONS;
        let _ = &mut fr;
    }
    Ok(out)
}

/// application env — same store under a reserved table tag (0b111 is never
/// a valid term word for a table name).
const APP_ENV_TAB: u64 = 0b111;

#[no_mangle]
pub extern "C" fn mana_rt_app_set_env(ctx: *mut ProcCtx, app: u64, key: u64, val: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, app, key, val];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let kp = alloc_nursery(ctx, 3);
    unsafe {
        *kp = (2 << 8) | KIND_TUPLE;
        *kp.add(1) = fr[2];
        *kp.add(2) = fr[3];
    }
    fr[2] = kp as u64; // reuse slot: composite {App, Key} key
    let op = alloc_nursery(ctx, 3);
    unsafe {
        *op = (2 << 8) | KIND_TUPLE;
        *op.add(1) = fr[2];
        *op.add(2) = fr[4];
    }
    ctx.roots_head = saved;
    mana_rt_ets_insert(ctx, APP_ENV_TAB, op as u64, 0)
}

/// get_env: `miss` is returned on absence (codegen passes 'undefined' or
/// the default); `wrap_ok != 0` wraps hits as {ok, V}.
#[no_mangle]
pub extern "C" fn mana_rt_app_get_env(
    ctx: *mut ProcCtx,
    app: u64,
    key: u64,
    miss: u64,
    wrap_ok: u64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let guard = ETS_STORE.lock().unwrap();
    let found = guard.as_ref().and_then(|rows| {
        rows.iter()
            .find(|&&(t, k, _)| {
                t == APP_ENV_TAB && {
                    let p = k as *const u64;
                    unsafe {
                        mana_rt_eq_exact(*p.add(1), app) == 1
                            && mana_rt_eq_exact(*p.add(2), key) == 1
                    }
                }
            })
            .map(|&(_, _, tuple)| unsafe { *(tuple as *const u64).add(2) })
    });
    drop(guard);
    match found {
        Some(v) if wrap_ok != 0 => {
            // v is eternal — no rooting needed around this alloc
            let p = alloc_nursery(ctx, 3);
            unsafe {
                *p = (2 << 8) | KIND_TUPLE;
                *p.add(1) = known().ok;
                *p.add(2) = v;
            }
            p as u64
        }
        Some(v) => v,
        None => miss,
    }
}

// ---------------------------------------------------------------------------
// code (native cut: static binary — "loaded" means compiled in)

fn module_is_compiled(m: u64) -> bool {
    if m & TAG_MASK == TAG_ATOM && is_cut_module(atom_bytes(m)) {
        return true;
    }
    export_table().keys().any(|&(em, _, _)| em == m)
}

/// Modules the compiler implements natively (BIF cuts) or compiles as
/// runtime raises — they have no export-table entries but "exist" for
/// code:ensure_loaded / is_loaded (Phoenix.PubSub probes :persistent_term
/// this way). MUST stay in sync with codegen's is_bif_module + the
/// unimplemented-raise list.
fn is_cut_module(name: &[u8]) -> bool {
    matches!(
        name,
        b"erlang"
            | b"maps"
            | b"io"
            | b"unicode"
            | b"persistent_term"
            | b"code"
            | b"io_lib"
            | b"logger"
            | b"ets"
            | b"application"
            | b"prim_file"
            | b"file"
            | b"math"
            | b"re"
            | b"timer"
            | b"gen_tcp"
            | b"inet"
            | b"crypto"
            | b"erts_internal"
            | b"elixir_erl"
            | b"erl_eval"
            | b"beam_lib"
            | b"global"
            | b"global_group"
            | b"net_kernel"
            | b"zlib"
    )
}

/// erlang:module_loaded/1 — closed world: compiled or cut = loaded.
#[no_mangle]
pub extern "C" fn mana_rt_module_loaded(ctx: *mut ProcCtx, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if m & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    if module_is_compiled(m) {
        known().true_a
    } else {
        known().false_a
    }
}

/// code:is_loaded/1 → {file, "native"} | false (Ecto.Queryable.Atom probes
/// schema modules through this).
#[no_mangle]
pub extern "C" fn mana_rt_code_is_loaded(ctx: *mut ProcCtx, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if m & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    if !module_is_compiled(m) {
        return known().false_a;
    }
    // {file, "native"} — charlist, matching code:is_loaded's shape for
    // preloaded/static code
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &b in b"native".iter().rev() {
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = ((b as u64) << 3) | TAG_SMALL;
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
    }
    let t = alloc_nursery(ctx, 3);
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = atom_intern(b"file");
        *t.add(2) = fr[2];
    }
    ctx.roots_head = saved;
    t as u64
}

/// code:lib_dir/1 and code:priv_dir/1 — the --app boot generator bakes
/// each application's build-time dir under env {:mana_app_dirs, App}
/// (a binary). Unknown apps get {error, bad_name}, like BEAM.
#[no_mangle]
pub extern "C" fn mana_rt_code_app_dir(ctx: *mut ProcCtx, app: u64, is_priv: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    if app & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctxr);
    }
    let tab = atom_intern(b"mana_app_dirs");
    let miss = known().undefined;
    let hit = mana_rt_app_get_env(ctx, tab, app, miss, 1);
    let ctxr = unsafe { &mut *ctx };
    if hit == known().undefined {
        let t = alloc_nursery(ctxr, 3);
        unsafe {
            *t = (2 << 8) | KIND_TUPLE;
            *t.add(1) = atom_error();
            *t.add(2) = atom_intern(b"bad_name");
        }
        return t as u64;
    }
    // {ok, DirBin} → charlist (++ "/priv" for priv_dir)
    let dir = unsafe { *((hit & !TAG_MASK) as *const u64).add(2) };
    let mut bytes = bin_bytes(dir).to_vec();
    if is_priv != 0 {
        bytes.extend_from_slice(b"/priv");
    }
    bytes_to_charlist(ctxr, &bytes)
}

/// code:ensure_loaded/1 → {module, M} | {error, nofile}. Eternal tuples —
/// tiny, bounded by call sites.
#[no_mangle]
pub extern "C" fn mana_rt_code_ensure_loaded(ctx: *mut ProcCtx, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if m & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let (tag, val) = if module_is_compiled(m) {
        (known().module, m)
    } else {
        (atom_error(), known().nofile)
    };
    let p = alloc_space(3);
    ctx.global.eternal.lock().push((p as usize, false));
    unsafe {
        *p = (2 << 8) | KIND_TUPLE;
        *p.add(1) = tag;
        *p.add(2) = val;
    }
    p as u64
}

/// erlang:function_exported/3 (module_loaded/1 shares the table).
#[no_mangle]
pub extern "C" fn mana_rt_function_exported(_ctx: *mut ProcCtx, m: u64, f: u64, a: u64) -> u64 {
    if a & TAG_MASK != TAG_SMALL {
        return known().false_a;
    }
    let arity = (a as i64 >> 3) as u64;
    if export_table().contains_key(&(m, f, arity)) {
        known().true_a
    } else {
        known().false_a
    }
}

/// erlang:list_to_atom/1 (interning) and list_to_existing_atom/1 (strict).
#[no_mangle]
pub extern "C" fn mana_rt_list_to_atom(ctx: *mut ProcCtx, l: u64, existing: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut bytes = Vec::new();
    let mut cur = l;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK != TAG_SMALL {
            return raise_badarg(ctx);
        }
        let cp = h as i64 >> 3;
        let Some(c) = u32::try_from(cp).ok().and_then(char::from_u32) else {
            return raise_badarg(ctx);
        };
        let mut buf = [0u8; 4];
        bytes.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
        cur = unsafe { *p.add(1) };
    }
    if existing != 0 {
        match atom_lookup(&bytes) {
            Some(a) => a,
            None => raise_badarg(ctx),
        }
    } else {
        atom_intern(&bytes)
    }
}

/// Deferred-undef target for make_fun/3 misses: raises when called. Extra
/// (argument/fun) registers are ignored — SysV lets callers pass more.
extern "C" fn make_fun_undef(ctx: *mut ProcCtx) -> u64 {
    raise_undef(unsafe { &mut *ctx })
}

/// erlang:make_fun/3 — a fun value for an exported function. The closure
/// convention appends the fun term as a trailing argument; raw compiled
/// functions ignore it (SysV: extra args are harmless), so the closure's
/// code pointer can be the export itself.
#[no_mangle]
pub extern "C" fn mana_rt_make_fun(ctx: *mut ProcCtx, m: u64, f: u64, arity: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if m & TAG_MASK != TAG_ATOM || f & TAG_MASK != TAG_ATOM || arity & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let a = (arity as i64 >> 3) as u64;
    let code = export_table().get(&(m, f, a)).copied().unwrap_or_else(|| {
        if std::env::var_os("MANA_DEBUG_UNDEF").is_some() {
            eprintln!(
                "mana: make_fun miss {}:{}/{}",
                String::from_utf8_lossy(atom_bytes(m)),
                String::from_utf8_lossy(atom_bytes(f)),
                a
            );
        }
        make_fun_undef as usize
    });
    let p = alloc_nursery(ctx, 2);
    unsafe {
        *p = (a << 8) | KIND_FUN; // zero captures
        *p.add(1) = code as u64;
    }
    p as u64
}

/// erlang:binary_to_atom/1,2 — interns (existing == 0) or requires an
/// existing atom (binary_to_existing_atom).
#[no_mangle]
pub extern "C" fn mana_rt_binary_to_atom(ctx: *mut ProcCtx, bin: u64, existing: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((p, n)) = bin_parts(bin) else {
        return raise_badarg(ctx);
    };
    let bytes = unsafe { std::slice::from_raw_parts(p, n) };
    if existing != 0 {
        match atom_lookup(bytes) {
            Some(a) => a,
            None => raise_badarg(ctx),
        }
    } else {
        atom_intern(bytes)
    }
}

fn write_term(t: u64, out: &mut String) {
    match t & TAG_MASK {
        TAG_SMALL => {
            out.push_str(&((t as i64) >> 3).to_string());
        }
        TAG_ATOM => unsafe {
            let p = (t & !TAG_MASK) as *const u64;
            let len = *p as usize;
            let bytes = std::slice::from_raw_parts(p.add(1) as *const u8, len);
            write_atom(&String::from_utf8_lossy(bytes), out);
        },
        _ if t == NIL => out.push_str("[]"),
        TAG_PID => {
            if t & 0xF == PID_TAG4 {
                out.push_str(&format!("<0.{}.0>", t >> 4));
            } else {
                out.push_str(&format!("#Ref<0.{}>", t >> 4));
            }
        }
        TAG_CONS => {
            // BEAM displays proper lists of printable chars as strings
            if let Some(s) = printable_list(t) {
                out.push('"');
                out.push_str(&s);
                out.push('"');
                return;
            }
            out.push('[');
            let mut cur = t;
            loop {
                unsafe {
                    let p = (cur & !TAG_MASK) as *const u64;
                    write_term(*p, out);
                    let tail = *p.add(1);
                    if tail == NIL {
                        break;
                    } else if tail & TAG_MASK == TAG_CONS {
                        out.push(',');
                        cur = tail;
                    } else {
                        out.push('|');
                        write_term(tail, out);
                        break;
                    }
                }
            }
            out.push(']');
        }
        TAG_BOXED => unsafe {
            let p = t as *const u64;
            let header = *p;
            match header & 0xff {
                KIND_TUPLE => {
                    let arity = (header >> 8) as usize;
                    out.push('{');
                    for i in 0..arity {
                        if i > 0 {
                            out.push(',');
                        }
                        write_term(*p.add(1 + i), out);
                    }
                    out.push('}');
                }
                KIND_FLOAT => {
                    let f = f64::from_bits(*p.add(1));
                    out.push_str(&display_float(f));
                }
                KIND_FUN => out.push_str("#Fun<mana>"),
                KIND_MAP => {
                    let n = (header >> 8) as usize;
                    out.push_str("#{");
                    for i in 0..n {
                        if i > 0 {
                            out.push(',');
                        }
                        write_term(*p.add(1 + i), out);
                        out.push_str("=>");
                        write_term(*p.add(1 + n + i), out);
                    }
                    out.push('}');
                }
                KIND_BIGNUM => {
                    let (neg, mag) = bignum_parts(t).unwrap();
                    if neg {
                        out.push('-');
                    }
                    out.push_str(&bigint::mag_to_decimal(mag));
                }
                KIND_BIN | KIND_SUBBIN => {
                    let bytes = bin_bytes(t);
                    out.push_str("<<");
                    // all-printable-ascii binaries render as a string; unlike
                    // char lists, control chars do NOT qualify
                    if !bytes.is_empty() && bytes.iter().all(|&b| (0x20..=0x7e).contains(&b)) {
                        out.push('"');
                        for &b in bytes {
                            // only the quote is escaped (backslash prints raw)
                            if b == b'"' {
                                out.push('\\');
                            }
                            out.push(b as char);
                        }
                        out.push('"');
                    } else {
                        for (i, b) in bytes.iter().enumerate() {
                            if i > 0 {
                                out.push(',');
                            }
                            out.push_str(&b.to_string());
                        }
                    }
                    out.push_str(">>");
                }
                _ => out.push_str("#<unknown-boxed>"),
            }
        },
        _ => out.push_str("#<unknown>"),
    }
}

/// BEAM quotes atoms that are not plain identifiers ([a-z][a-zA-Z0-9_@]*)
/// or that collide with Erlang reserved words. `'` and `\` are escaped;
/// other chars print raw (matching display, not ~p).
fn write_atom(name: &str, out: &mut String) {
    const RESERVED: &[&str] = &[
        "after", "and", "andalso", "band", "begin", "bnot", "bor", "bsl", "bsr",
        "bxor", "case", "catch", "cond", "div", "end", "fun", "if", "let",
        "maybe", "not", "of", "or", "orelse", "receive", "rem", "try", "when",
        "xor",
    ];
    let plain = !name.is_empty()
        && name.as_bytes()[0].is_ascii_lowercase()
        && name
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'@')
        && !RESERVED.contains(&name);
    if plain {
        out.push_str(name);
        return;
    }
    out.push('\'');
    for c in name.chars() {
        if c == '\'' || c == '\\' {
            out.push('\\');
        }
        out.push(c);
    }
    out.push('\'');
}

/// BEAM's display heuristic: a proper list of printable latin-1 chars (or
/// their escapes) renders as a quoted string. Returns the escaped body.
fn printable_list(t: u64) -> Option<String> {
    let mut s = String::new();
    let mut cur = t;
    loop {
        if cur == NIL {
            return if s.is_empty() { None } else { Some(s) };
        }
        if cur & TAG_MASK != TAG_CONS {
            return None;
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK != TAG_SMALL {
            return None;
        }
        let c = (h as i64) >> 3;
        match c {
            32..=126 => {
                let ch = c as u8 as char;
                if ch == '"' || ch == '\\' {
                    s.push('\\');
                }
                s.push(ch);
            }
            // BEAM writes these raw inside the quotes
            8..=13 | 27 => s.push(c as u8 as char),
            _ => return None,
        }
        cur = unsafe { *p.add(1) };
    }
}
