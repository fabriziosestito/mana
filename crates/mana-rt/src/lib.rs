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

const NURSERY_WORDS: usize = 16 * 1024; // 128 KiB
const OLD_CHUNK_WORDS: usize = 64 * 1024;
const OLD_LIMIT_INIT: usize = 4 * OLD_CHUNK_WORDS;
/// Reservation only — anonymous pages commit lazily on first touch.
const STACK_BYTES: usize = 8 * 1024 * 1024;
const ROOT_STACK_BYTES: usize = 32 * 1024 * 1024;
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
        unsafe {
            let code = *((cl & !TAG_MASK) as *const u64).add(1);
            let f: extern "C" fn(*mut ProcCtx, u64) -> u64 = std::mem::transmute(code);
            f(ctx, cl)
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
                    if pid != 0 {
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

fn write_term(t: u64, out: &mut String) {
    match t & TAG_MASK {
        TAG_SMALL => {
            out.push_str(&((t as i64) >> 3).to_string());
        }
        TAG_ATOM => unsafe {
            let p = (t & !TAG_MASK) as *const u64;
            let len = *p as usize;
            let bytes = std::slice::from_raw_parts(p.add(1) as *const u8, len);
            out.push_str(&String::from_utf8_lossy(bytes));
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
                    out.push_str(&format!("{:?}", f));
                }
                KIND_FUN => out.push_str("#Fun<mana>"),
                _ => out.push_str("#<unknown-boxed>"),
            }
        },
        _ => out.push_str("#<unknown>"),
    }
}
