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
//! TODO(bignum): small-int arithmetic wraps into the tag space.
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
/// An inert big-integer literal (decimal digits): ordered/compared/printed
/// correctly, badarith under arithmetic — TODO(bignum) for real math.
pub const KIND_BIGLIT: u64 = 6;

const NURSERY_WORDS: usize = 16 * 1024; // 128 KiB
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
        KIND_BIN | KIND_BIGLIT => ((header >> 8) as usize + 7) / 8,
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
    let nursery = alloc_space(NURSERY_WORDS);
    let ctx = Box::into_raw(Box::new(ProcCtx {
        heap_top: nursery,
        heap_end: unsafe { nursery.add(NURSERY_WORDS) },
        roots_head: 0,
        exc_class: 0,
        exc_reason: 0,
        reductions: REDUCTIONS_PER_SLICE,
        nursery_start: nursery,
        nursery_words: NURSERY_WORDS,
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
                    // an uncaught exit with reason normal/shutdown is an
                    // orderly termination (gen_server stop path) — silent,
                    // like BEAM
                    let quiet = ctx.exc_class == find_atom("exit").unwrap_or(0)
                        && (ctx.exc_reason == known().normal
                            || atom_bytes(ctx.exc_reason) == b"shutdown");
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
    // root the inputs while allocating the pending tuple
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, m, f, args];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let tup = shared_tuple(ctx, &[fr[2], fr[3], fr[4]]);
    ctx.roots_head = saved;
    let pending = promote_term(ctx, tup);
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
// big-integer literal tokens

fn biglit_digits(t: u64) -> Option<&'static [u8]> {
    if t & TAG_MASK != TAG_BOXED || t == 0 {
        return None;
    }
    let p = t as *const u64;
    let h = unsafe { *p };
    if h & 0xff != KIND_BIGLIT {
        return None;
    }
    Some(unsafe { std::slice::from_raw_parts(p.add(1) as *const u8, (h >> 8) as usize) })
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
    let n = bytes.len();
    let words = 1 + (n + 7) / 8;
    let p = alloc_space(words);
    unsafe {
        *p = ((n as u64) << 8) | KIND_BIGLIT;
        if n % 8 != 0 {
            *p.add(words - 1) = 0;
        }
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), p.add(1) as *mut u8, n);
    }
    let t = p as u64;
    let key: &'static [u8] = Box::leak(bytes.to_vec().into_boxed_slice());
    map.insert(key, t);
    t
}

/// Numeric comparison against/between big literals: sign + digit count +
/// lexicographic (exact for integers); floats compare via f64 parse.
fn big_num_cmp(a: u64, b: u64) -> i64 {
    fn parts(t: u64) -> Option<(bool, &'static [u8])> {
        biglit_digits(t).map(|d| match d.strip_prefix(b"-") {
            Some(rest) => (true, rest),
            None => (false, d),
        })
    }
    match (parts(a), parts(b)) {
        (Some((na, da)), Some((nb, db))) => {
            if na != nb {
                return if na { -1 } else { 1 };
            }
            let ord = da
                .len()
                .cmp(&db.len())
                .then_with(|| da.cmp(db));
            let r = match ord {
                std::cmp::Ordering::Less => -1,
                std::cmp::Ordering::Equal => 0,
                std::cmp::Ordering::Greater => 1,
            };
            if na { -r } else { r }
        }
        (Some((neg, d)), None) => {
            // big vs small/float: approximate via f64 (exact for ordering
            // against 61-bit smalls; adequate for floats)
            let x: f64 = std::str::from_utf8(d)
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(f64::INFINITY);
            let x = if neg { -x } else { x };
            let y = num_val(b);
            (x > y) as i64 - (x < y) as i64
        }
        (None, Some(_)) => -big_num_cmp(b, a),
        (None, None) => 0,
    }
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
fn num_of(t: u64) -> Option<(f64, bool)> {
    if t & TAG_MASK == TAG_SMALL {
        return Some(((t as i64 >> 3) as f64, true));
    }
    if t & TAG_MASK == TAG_BOXED && t != 0 {
        let p = t as *const u64;
        if unsafe { *p } & 0xff == KIND_FLOAT {
            return Some((f64::from_bits(unsafe { *p.add(1) }), false));
        }
    }
    None
}

// arithmetic opcodes for mana_rt_arith
pub const AR_ADD: u64 = 0;
pub const AR_SUB: u64 = 1;
pub const AR_MUL: u64 = 2;
pub const AR_FDIV: u64 = 3;
pub const AR_IDIV: u64 = 4;
pub const AR_REM: u64 = 5;
pub const AR_NEG: u64 = 6;
pub const AR_ABS: u64 = 7;

/// Arithmetic slow path: anything that isn't the inline both-small-int
/// case. Mixed/float ops produce boxed floats (box_float — never GCs);
/// non-numbers and integer ops on floats raise badarith like BEAM.
#[no_mangle]
pub extern "C" fn mana_rt_arith(ctx: *mut ProcCtx, op: u64, a: u64, b: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((x, xi)) = num_of(a) else {
        return raise_badarith(ctx);
    };
    match op {
        AR_NEG => {
            if xi {
                return (((-(a as i64 >> 3)) << 3) as u64) | TAG_SMALL;
            }
            return box_float(ctx, -x);
        }
        AR_ABS => {
            if xi {
                let v = a as i64 >> 3;
                return (((v.abs()) << 3) as u64) | TAG_SMALL;
            }
            return box_float(ctx, x.abs());
        }
        _ => {}
    }
    let Some((y, yi)) = num_of(b) else {
        return raise_badarith(ctx);
    };
    match op {
        AR_ADD | AR_SUB | AR_MUL => {
            if xi && yi {
                // both small (inline fast path normally catches this)
                let (p, q) = (a as i64 >> 3, b as i64 >> 3);
                let r = match op {
                    AR_ADD => p.wrapping_add(q),
                    AR_SUB => p.wrapping_sub(q),
                    _ => p.wrapping_mul(q),
                };
                return ((r << 3) as u64) | TAG_SMALL;
            }
            let r = match op {
                AR_ADD => x + y,
                AR_SUB => x - y,
                _ => x * y,
            };
            box_float(ctx, r)
        }
        AR_FDIV => {
            if y == 0.0 {
                return raise_badarith(ctx);
            }
            box_float(ctx, x / y)
        }
        // div/rem are integer-only; the inline fast path handles both-small,
        // so reaching here means at least one float → badarith (BEAM)
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
    let v = r as i64;
    if v >> 60 != 0 && v >> 60 != -1 {
        eprintln!("mana: TODO(bignum): float conversion out of small-int range");
        std::process::exit(1);
    }
    ((v << 3) as u64) | TAG_SMALL
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
    let v = v as i64;
    if v >> 60 != 0 && v >> 60 != -1 {
        eprintln!("mana: TODO(bignum): time value out of small-int range");
        std::process::exit(1);
    }
    ((v << 3) as u64) | TAG_SMALL
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

/// erlang:system_time/1. Unix nanoseconds exceed 61-bit smalls (BEAM uses
/// bignums) — we offset from 2020-01-01 instead; wall-clock DELTAS and
/// second/millisecond absolute values are unaffected in practice —
/// TODO(bignum).
#[no_mangle]
pub extern "C" fn mana_rt_system_time(ctx: *mut ProcCtx, unit: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    const EPOCH_2020_SECS: u64 = 1_577_836_800;
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH + std::time::Duration::from_secs(EPOCH_2020_SECS))
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
    if t & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let v = (t as i64 >> 3) as i128;
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
    if grow_to > 0 {
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

/// Raise-path allocations: never moved; fields scanned by collections.
#[no_mangle]
pub extern "C" fn mana_rt_alloc_eternal(ctx: *mut ProcCtx, words: u64, is_cons: u64) -> *mut u64 {
    let ctx = unsafe { &*ctx };
    let p = alloc_space(words as usize);
    ctx.global.eternal.lock().push((p as usize, is_cons != 0));
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
                    walk_proc_roots(p, |s| {
                        *s = forward_minor(ctx, &mut old, *s, &mut worklist);
                    });
                }
                drain_ingress(p);
                for m in p.private.iter_mut() {
                    *m = forward_minor(ctx, &mut old, *m, &mut worklist);
                }
            }
        }

        // eternal objects (exception reasons) may reference this nursery
        {
            let eternal = g.eternal.lock();
            for (pa, is_cons) in eternal.iter() {
                scan_fields(*pa as *mut u64, *is_cons, &mut |s| {
                    *s = forward_minor(ctx, &mut old, *s, &mut worklist);
                });
            }
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
                    *s = forward_major(*s, &mut top, &mut worklist);
                }
                frame = *frame as *mut u64;
            }
            octx.exc_class = forward_major(octx.exc_class, &mut top, &mut worklist);
            octx.exc_reason = forward_major(octx.exc_reason, &mut top, &mut worklist);
        }
        {
            let tab = g.procs.read();
            for (id, slot) in tab.iter().enumerate() {
                let Some(cell) = slot else { continue };
                let p = proc_mut(cell);
                if !running.contains(&id) {
                    walk_proc_roots(p, |s| {
                        *s = forward_major(*s, &mut top, &mut worklist);
                    });
                }
                drain_ingress(p); // everyone is parked: no concurrent pushes
                for m in p.private.iter_mut() {
                    *m = forward_major(*m, &mut top, &mut worklist);
                }
            }
        }
        {
            let eternal = g.eternal.lock();
            for (pa, is_cons) in eternal.iter() {
                scan_fields(*pa as *mut u64, *is_cons, &mut |s| {
                    *s = forward_major(*s, &mut top, &mut worklist);
                });
            }
        }
        while let Some(t) = worklist.pop() {
            let is_cons = t & TAG_MASK == TAG_CONS;
            let p = (t & !TAG_MASK) as *mut u64;
            scan_fields(p, is_cons, &mut |s| {
                *s = forward_major(*s, &mut top, &mut worklist);
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

unsafe fn forward_major(t: u64, top: &mut *mut u64, worklist: &mut Vec<u64>) -> u64 {
    if t == 0 {
        return 0;
    }
    match t & TAG_MASK {
        TAG_SMALL | TAG_ATOM | TAG_PID => t,
        _ if t == NIL => t,
        TAG_CONS => unsafe {
            let p = (t & !TAG_MASK) as *mut u64;
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
                KIND_BIN => 9,
                KIND_BIGLIT => 0, // numbers
                _ => 5, // tuple
            }
        }
        _ => 10,
    }
}

fn num_val(t: u64) -> f64 {
    if t & TAG_MASK == TAG_SMALL {
        ((t as i64) >> 3) as f64
    } else {
        f64::from_bits(unsafe { *(t as *const u64).add(1) })
    }
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
            if biglit_digits(a).is_some() || biglit_digits(b).is_some() {
                return big_num_cmp(a, b);
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
                KIND_BIN => (bin_bytes(a) == bin_bytes(b)) as i64,
                KIND_BIGLIT => (biglit_digits(a) == biglit_digits(b)) as i64,
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
    if header & 0xff != KIND_BIN {
        return None;
    }
    Some((unsafe { p.add(1) } as *const u8, (header >> 8) as usize))
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
        // (TODO(bignum): BEAM would succeed)
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
        eprintln!("mana: TODO(bignum): 64-bit binary segment value out of small-int range");
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
/// Sentinel = match failure. Allocates the sub-binary (roots `bin`).
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
    newp as u64
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
    if val & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let v = (val as i64 >> 3) as u64;
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
    if t & TAG_MASK != TAG_SMALL || base & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let b = base as i64 >> 3;
    if !(2..=36).contains(&b) {
        return raise_badarg(ctx);
    }
    let s = int_digits(t as i64 >> 3, b as u32);
    bytes_to_new_bin(ctx, s.as_bytes())
}

/// erlang:integer_to_list/1,2.
#[no_mangle]
pub extern "C" fn mana_rt_integer_to_list(ctx: *mut ProcCtx, t: u64, base: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if t & TAG_MASK != TAG_SMALL || base & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let b = base as i64 >> 3;
    if !(2..=36).contains(&b) {
        return raise_badarg(ctx);
    }
    let s = int_digits(t as i64 >> 3, b as u32);
    bytes_to_charlist(ctx, s.as_bytes())
}

/// Parse decimal/base digits (with optional sign) — badarg on any junk.
fn parse_int_bytes(bytes: &[u8], base: u32) -> Option<i64> {
    let s = std::str::from_utf8(bytes).ok()?;
    let v = i64::from_str_radix(s, base).ok()?;
    // small ints are 61 bits
    if v >> 60 != 0 && v >> 60 != -1 {
        return None; // TODO(bignum)
    }
    Some(v)
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
    match parse_int_bytes(bin_bytes(bin), b as u32) {
        Some(v) => ((v << 3) as u64) | TAG_SMALL,
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
    match parse_int_bytes(&bytes, b as u32) {
        Some(v) => ((v << 3) as u64) | TAG_SMALL,
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

type AtomTable = std::sync::RwLock<std::collections::HashMap<&'static [u8], u64>>;

fn atom_table_lock() -> &'static AtomTable {
    static TABLE: std::sync::OnceLock<AtomTable> = std::sync::OnceLock::new();
    TABLE.get_or_init(|| {
        let mut map = std::collections::HashMap::new();
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

fn export_table() -> &'static std::collections::HashMap<(u64, u64, u64), usize> {
    static TABLE: std::sync::OnceLock<std::collections::HashMap<(u64, u64, u64), usize>> =
        std::sync::OnceLock::new();
    TABLE.get_or_init(|| {
        let mut map = std::collections::HashMap::new();
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
        // callers actually use (attributes → [], module → the atom)
        if atom_bytes(f) == b"module_info" && module_is_compiled(m) {
            if n == 0 {
                return NIL;
            }
            if n == 1 {
                return match atom_bytes(argv[0]) {
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
                    _ => NIL,
                };
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
            let words = 1 + payload_words(header);
            let np = alloc_space(words);
            unsafe {
                *np = header;
                match header & 0xff {
                    KIND_FLOAT | KIND_BIN => {
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
    let bytes = bin_bytes(bin);
    if bytes.len() > 7 {
        eprintln!("mana: TODO(bignum): decode_unsigned over 56 bits");
        std::process::exit(1);
    }
    let mut v: u64 = 0;
    if little != 0 {
        for &b in bytes.iter().rev() {
            v = (v << 8) | b as u64;
        }
    } else {
        for &b in bytes {
            v = (v << 8) | b as u64;
        }
    }
    (v << 3) | TAG_SMALL
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
        match kv_find(rows, tab, key) {
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
        }
    }
    known.true_a
}

/// ets:lookup/2 → list of stored tuples (eternal — safe to share).
#[no_mangle]
pub extern "C" fn mana_rt_ets_lookup(ctx: *mut ProcCtx, tab: u64, key: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let guard = ETS_STORE.lock().unwrap();
    let found = guard
        .as_ref()
        .and_then(|rows| kv_find(rows, tab, key).map(|i| rows[i].2));
    drop(guard);
    match found {
        Some(tuple) => {
            let cell = alloc_nursery(ctx, 2);
            unsafe {
                *cell = tuple;
                *cell.add(1) = NIL;
            }
            cell as u64 | TAG_CONS
        }
        None => NIL,
    }
}

/// ets:delete/2 (by key).
#[no_mangle]
pub extern "C" fn mana_rt_ets_delete(_ctx: *mut ProcCtx, tab: u64, key: u64) -> u64 {
    let mut guard = ETS_STORE.lock().unwrap();
    if let Some(rows) = guard.as_mut() {
        if let Some(i) = kv_find(rows, tab, key) {
            rows.remove(i);
        }
    }
    known().true_a
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
    export_table().keys().any(|&(em, _, _)| em == m)
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
                KIND_BIGLIT => {
                    let bytes =
                        std::slice::from_raw_parts(p.add(1) as *const u8, (header >> 8) as usize);
                    out.push_str(&String::from_utf8_lossy(bytes));
                }
                KIND_BIN => {
                    let bytes = std::slice::from_raw_parts(p.add(1) as *const u8, (header >> 8) as usize);
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
