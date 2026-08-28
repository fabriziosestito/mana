//! mana runtime — per-process heap with a Cheney copying collector.
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
//! | 0b111 | GC forwarding marker (never visible to compiled code)          |
//!
//! Boxed header word: low 8 bits = kind (0 tuple, 1 float, 2 fun); tuples
//! keep arity in bits 8+, funs keep arity in bits 8-15 and capture count in
//! bits 16+ (payload: code pointer, then captures).
//!
//! Atoms are `linkonce_odr` statics deduplicated by the linker — never heap
//! allocated, never collected.
//!
//! # Process context (ABI contract with mana-codegen)
//!
//! Every compiled function takes `ctx: *mut ProcCtx` as its first argument.
//! Codegen reads/writes these fields by fixed word offset:
//!
//! * word 0: `heap_top` (nursery allocation pointer — compiled code bumps
//!   this inline on the fast path)
//! * word 1: `heap_end` (nursery limit)
//! * word 2: `roots_head` — a chain of GC root frames on the native stack,
//!   each laid out `[prev_frame, len, slot0, ..., slot(len-1)]`. Frames are
//!   zero-initialized; a slot containing 0 is empty and skipped by the
//!   collector (0 is not a valid term).
//!
//! # Heap organization
//!
//! Generational: a fixed-size nursery (words 0/1) plus a chunked old space.
//! Terms are immutable and every stored field references an older object,
//! so **old objects can never point into the nursery** — minor collections
//! trace from the roots, copy live nursery objects into the old space, stop
//! at any old pointer, and never scan the old space. No write barriers, no
//! remembered sets. A major collection (full copy of the old space) runs
//! when old usage passes a limit, immediately after a minor while the
//! nursery is empty. Old chunks never move between majors.
//!
//! Collection may move heap objects; compiled code must not hold heap terms
//! in registers across a potential GC point unless rooted in a frame slot
//! (mana-codegen's spill discipline enforces this).
//!
//! TODO(bignum): small-int arithmetic currently wraps into the tag space.

use std::collections::VecDeque;
use std::io::Write;
use std::time::{Duration, Instant};

use corosensei::stack::DefaultStack;
use corosensei::{Coroutine, CoroutineResult, Yielder};

pub const TAG_MASK: u64 = 0b111;
pub const TAG_BOXED: u64 = 0b000;
pub const TAG_SMALL: u64 = 0b001;
pub const TAG_ATOM: u64 = 0b010;
pub const NIL: u64 = 0b011;
pub const TAG_CONS: u64 = 0b100;
pub const TAG_PID: u64 = 0b110;
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

/// Spawned-process stack reserve. TODO(stacks): growable stacks need
/// precise stack maps; deep body recursion meanwhile needs headroom.
const STACK_BYTES: usize = 1024 * 1024;
/// The root process gets main-thread-like headroom.
const ROOT_STACK_BYTES: usize = 32 * 1024 * 1024;
const REDUCTIONS_PER_SLICE: i64 = 4000;

type ProcCoro = Coroutine<(), (), u64, DefaultStack>;

#[derive(PartialEq)]
enum ProcState {
    Runnable,
    Running,
    /// waiting for a message, with an optional wake deadline
    Waiting(Option<Instant>),
    Dead,
}

struct Process {
    coro: Option<ProcCoro>,
    yielder: *const Yielder<(), ()>,
    saved_roots: u64,
    saved_exc_class: u64,
    saved_exc_reason: u64,
    mailbox: Vec<u64>,
    cursor: usize,
    state: ProcState,
    /// spawn closure until first resume (kept as a GC root; 0 once started)
    pending_closure: u64,
}

struct Scheduler {
    procs: Vec<Option<Process>>,
    run_q: VecDeque<usize>,
    current: usize,
}

struct Chunk {
    start: *mut u64,
    top: *mut u64,
    end: *mut u64,
    words: usize,
}

#[repr(C)]
pub struct ProcCtx {
    pub heap_top: *mut u64, // word offset 0 — codegen contract (nursery)
    pub heap_end: *mut u64, // word offset 1 — codegen contract (nursery)
    pub roots_head: u64,    // word offset 2 — codegen contract
    pub exc_class: u64,     // word offset 3 — codegen contract (atom term)
    pub exc_reason: u64,    // word offset 4 — codegen contract
    pub reductions: i64,    // word offset 5 — codegen contract
    nursery_start: *mut u64,
    nursery_words: usize,
    old: Vec<Chunk>,
    old_used: usize,
    old_limit: usize,
    /// Raise-path allocations: never freed or moved, but their fields may
    /// reference heap terms, so collections scan them like roots.
    /// (ptr, is_cons) — cons cells have no header to derive layout from.
    eternal: Vec<(*mut u64, bool)>,
    sched: Scheduler,
}

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

/// Create the root process context. Leaked: lives for the program.
#[no_mangle]
pub extern "C" fn mana_rt_init() -> *mut ProcCtx {
    let nursery = alloc_space(NURSERY_WORDS);
    Box::into_raw(Box::new(ProcCtx {
        heap_top: nursery,
        heap_end: unsafe { nursery.add(NURSERY_WORDS) },
        roots_head: 0,
        exc_class: 0,
        exc_reason: 0,
        reductions: REDUCTIONS_PER_SLICE,
        nursery_start: nursery,
        nursery_words: NURSERY_WORDS,
        old: Vec::new(),
        old_used: 0,
        old_limit: OLD_LIMIT_INIT,
        eternal: Vec::new(),
        sched: Scheduler {
            procs: Vec::new(),
            run_q: VecDeque::new(),
            current: 0,
        },
    }))
}

/// Allocation slow path (compiled code bumps the nursery inline): run a
/// minor collection — and a major if the old space passed its limit — then
/// satisfy the request from the (empty) nursery, growing it for oversized
/// requests.
#[no_mangle]
pub extern "C" fn mana_rt_alloc_slow(ctx: *mut ProcCtx, words: u64) -> *mut u64 {
    let ctx = unsafe { &mut *ctx };
    let words = words as usize;
    let promoted = minor_collect(ctx);
    if ctx.old_used > ctx.old_limit {
        major_collect(ctx);
    }
    // Adaptive nursery: promotion means survivors are medium-lived and the
    // nursery is too small for the allocation pattern — grow until copying
    // out of the nursery is rare (<1/16 per minor), so most data dies young.
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

/// Allocation for raise-path terms (exception reasons): plain malloc,
/// never moved — keeps abort paths from turning every multi-clause
/// function into a GC-framed one. Registered so collections can scan the
/// fields (a caught reason may reference heap terms). `is_cons` != 0 marks
/// a headerless cons cell. Leaks by design (TODO: free on catch).
#[no_mangle]
pub extern "C" fn mana_rt_alloc_eternal(ctx: *mut ProcCtx, words: u64, is_cons: u64) -> *mut u64 {
    let ctx = unsafe { &mut *ctx };
    let p = alloc_space(words as usize);
    ctx.eternal.push((p, is_cons != 0));
    p
}

// ---- processes & scheduler (single OS thread; zero-copy messaging on the
// shared heap — safe because terms are immutable) ----

fn make_pid(id: usize) -> u64 {
    ((id as u64) << 3) | TAG_PID
}

fn spawn_process(ctx: *mut ProcCtx, closure: u64) -> usize {
    let sched = unsafe { &mut (*ctx).sched };
    let id = sched.procs.len();
    let stack = DefaultStack::new(STACK_BYTES).expect("stack allocation failed");
    let ctx_addr = ctx as usize;
    let coro = Coroutine::with_stack(stack, move |yielder, _| {
        let ctx = ctx_addr as *mut ProcCtx;
        let sched = unsafe { &mut (*ctx).sched };
        let me = sched.current;
        let proc_ = sched.procs[me].as_mut().unwrap();
        proc_.yielder = yielder as *const _;
        // reload the closure at start time: it may have moved since spawn
        let cl = proc_.pending_closure;
        proc_.pending_closure = 0;
        unsafe {
            let code = *((cl & !TAG_MASK) as *const u64).add(1);
            let f: extern "C" fn(*mut ProcCtx, u64) -> u64 = std::mem::transmute(code);
            f(ctx, cl)
        }
    });
    sched.procs.push(Some(Process {
        coro: Some(coro),
        yielder: std::ptr::null(),
        saved_roots: 0,
        saved_exc_class: 0,
        saved_exc_reason: 0,
        mailbox: Vec::new(),
        cursor: 0,
        state: ProcState::Runnable,
        pending_closure: closure,
    }));
    sched.run_q.push_back(id);
    id
}

/// Drive the scheduler until the root process (pid 0) returns; its result
/// (possibly the exception sentinel) is the program result. Called by the
/// generated `main`.
#[no_mangle]
pub extern "C" fn mana_rt_run(ctx: *mut ProcCtx, entry: extern "C" fn(*mut ProcCtx) -> u64) -> u64 {
    let ctxp = ctx;
    let ctx = unsafe { &mut *ctx };
    // root process: a coroutine wrapping the entry function
    {
        let stack = DefaultStack::new(ROOT_STACK_BYTES).expect("stack allocation failed");
        let ctx_addr = ctxp as usize;
        let coro = Coroutine::with_stack(stack, move |yielder, _| {
            let ctx = ctx_addr as *mut ProcCtx;
            let sched = unsafe { &mut (*ctx).sched };
            let proc_ = sched.procs[sched.current].as_mut().unwrap();
            proc_.yielder = yielder as *const _;
            entry(ctx)
        });
        ctx.sched.procs.push(Some(Process {
            coro: Some(coro),
            yielder: std::ptr::null(),
            saved_roots: 0,
            saved_exc_class: 0,
            saved_exc_reason: 0,
            mailbox: Vec::new(),
            cursor: 0,
            state: ProcState::Runnable,
            pending_closure: 0,
        }));
        ctx.sched.run_q.push_back(0);
    }

    loop {
        let pid = match ctx.sched.run_q.pop_front() {
            Some(p) => p,
            None => {
                // no runnable process: wake sleepers or report deadlock
                let now = Instant::now();
                let mut nearest: Option<Instant> = None;
                let mut woke = false;
                for (id, slot) in ctx.sched.procs.iter_mut().enumerate() {
                    let Some(p) = slot else { continue };
                    if let ProcState::Waiting(Some(dl)) = p.state {
                        if dl <= now {
                            p.state = ProcState::Runnable;
                            ctx.sched.run_q.push_back(id);
                            woke = true;
                        } else if nearest.is_none_or(|n| dl < n) {
                            nearest = Some(dl);
                        }
                    }
                }
                if woke {
                    continue;
                }
                match nearest {
                    Some(dl) => {
                        std::thread::sleep(dl.saturating_duration_since(Instant::now()));
                        continue;
                    }
                    None => {
                        eprintln!("mana: all processes are waiting on receive (deadlock)");
                        std::process::exit(1);
                    }
                }
            }
        };

        // swap the process's context view in
        {
            let p = ctx.sched.procs[pid].as_mut().unwrap();
            p.state = ProcState::Running;
            ctx.roots_head = p.saved_roots;
            ctx.exc_class = p.saved_exc_class;
            ctx.exc_reason = p.saved_exc_reason;
        }
        ctx.reductions = REDUCTIONS_PER_SLICE;
        ctx.sched.current = pid;

        let mut coro = ctx.sched.procs[pid].as_mut().unwrap().coro.take().unwrap();
        match coro.resume(()) {
            CoroutineResult::Yield(()) => {
                let p = ctx.sched.procs[pid].as_mut().unwrap();
                p.coro = Some(coro);
                p.saved_roots = ctx.roots_head;
                p.saved_exc_class = ctx.exc_class;
                p.saved_exc_reason = ctx.exc_reason;
                if p.state == ProcState::Running {
                    p.state = ProcState::Runnable;
                    ctx.sched.run_q.push_back(pid);
                }
            }
            CoroutineResult::Return(v) => {
                if pid == 0 {
                    return v; // program result
                }
                if v == EXC_SENTINEL {
                    let mut class = String::new();
                    let mut reason = String::new();
                    write_term(ctx.exc_class, &mut class);
                    write_term(ctx.exc_reason, &mut reason);
                    eprintln!(
                        "mana: process <0.{}.0> exited: {} {}",
                        pid, class, reason
                    );
                }
                ctx.sched.procs[pid] = None;
            }
        }
    }
}

fn suspend_current(ctx: &mut ProcCtx) {
    let yielder = ctx.sched.procs[ctx.sched.current]
        .as_ref()
        .unwrap()
        .yielder;
    unsafe { (*yielder).suspend(()) };
}

/// Reduction budget exhausted: reschedule the current process.
#[no_mangle]
pub extern "C" fn mana_rt_yield(ctx: *mut ProcCtx) {
    let ctx = unsafe { &mut *ctx };
    // state stays Running → the scheduler re-queues it
    suspend_current(ctx);
}

#[no_mangle]
pub extern "C" fn mana_rt_self(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &*ctx };
    make_pid(ctx.sched.current)
}

/// erlang:spawn/1 — returns the pid, or 0 if the argument is not an
/// arity-0 fun (codegen raises badarg on 0).
#[no_mangle]
pub extern "C" fn mana_rt_spawn(ctx: *mut ProcCtx, closure: u64) -> u64 {
    if closure & TAG_MASK != TAG_BOXED || closure == 0 {
        return 0;
    }
    let header = unsafe { *(closure as *const u64) };
    if header & 0xff != KIND_FUN || (header >> 8) & 0xff != 0 {
        return 0;
    }
    make_pid(spawn_process(ctx, closure))
}

/// erlang:'!'/2 — zero-copy: pushes the term into the target mailbox.
/// Sends to dead/unknown pids succeed silently (BEAM semantics).
#[no_mangle]
pub extern "C" fn mana_rt_send(ctx: *mut ProcCtx, pid: u64, msg: u64) {
    let ctx = unsafe { &mut *ctx };
    if pid & TAG_MASK != TAG_PID {
        return;
    }
    let id = (pid >> 3) as usize;
    let Some(Some(p)) = ctx.sched.procs.get_mut(id) else {
        return;
    };
    p.mailbox.push(msg);
    if matches!(p.state, ProcState::Waiting(_)) {
        p.state = ProcState::Runnable;
        ctx.sched.run_q.push_back(id);
    }
}

// ---- receive primops (erlc lowers `receive` to these) ----

#[no_mangle]
pub extern "C" fn mana_rt_recv_ready(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &*ctx };
    let p = ctx.sched.procs[ctx.sched.current].as_ref().unwrap();
    (p.mailbox.len() > p.cursor) as u64
}

#[no_mangle]
pub extern "C" fn mana_rt_recv_peek(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &*ctx };
    let p = ctx.sched.procs[ctx.sched.current].as_ref().unwrap();
    if p.mailbox.len() > p.cursor {
        p.mailbox[p.cursor]
    } else {
        NIL
    }
}

#[no_mangle]
pub extern "C" fn mana_rt_recv_next(ctx: *mut ProcCtx) {
    let ctx = unsafe { &mut *ctx };
    let cur = ctx.sched.current;
    ctx.sched.procs[cur].as_mut().unwrap().cursor += 1;
}

#[no_mangle]
pub extern "C" fn mana_rt_recv_remove(ctx: *mut ProcCtx) {
    let ctx = unsafe { &mut *ctx };
    let cur = ctx.sched.current;
    let p = ctx.sched.procs[cur].as_mut().unwrap();
    let c = p.cursor;
    p.mailbox.remove(c);
    p.cursor = 0;
}

/// recv_wait_timeout: returns 1 if the timeout elapsed, 0 if a message is
/// available past the cursor. Timeout term: small int (ms) or 'infinity'.
#[no_mangle]
pub extern "C" fn mana_rt_recv_wait(ctx: *mut ProcCtx, timeout: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let deadline: Option<Instant> = if timeout & TAG_MASK == TAG_SMALL {
        let ms = (timeout as i64) >> 3;
        if ms <= 0 {
            let cur = ctx.sched.current;
            let p = ctx.sched.procs[cur].as_ref().unwrap();
            return (p.mailbox.len() <= p.cursor) as u64;
        }
        Some(Instant::now() + Duration::from_millis(ms as u64))
    } else {
        None // 'infinity' (or anything non-integer)
    };
    loop {
        let cur = ctx.sched.current;
        {
            let p = ctx.sched.procs[cur].as_ref().unwrap();
            if p.mailbox.len() > p.cursor {
                return 0;
            }
        }
        if let Some(dl) = deadline {
            if Instant::now() >= dl {
                return 1;
            }
        }
        ctx.sched.procs[cur].as_mut().unwrap().state = ProcState::Waiting(deadline);
        suspend_current(ctx);
    }
}

fn old_alloc(ctx: &mut ProcCtx, words: usize) -> *mut u64 {
    if let Some(chunk) = ctx.old.last_mut() {
        unsafe {
            if chunk.top.add(words) <= chunk.end {
                let p = chunk.top;
                chunk.top = chunk.top.add(words);
                ctx.old_used += words;
                return p;
            }
        }
    }
    let chunk_words = usize::max(
        ctx.old.last().map_or(OLD_CHUNK_WORDS, |c| c.words * 2),
        words,
    );
    let start = alloc_space(chunk_words);
    ctx.old.push(Chunk {
        start,
        top: unsafe { start.add(words) },
        end: unsafe { start.add(chunk_words) },
        words: chunk_words,
    });
    ctx.old_used += words;
    start
}

fn in_nursery(ctx: &ProcCtx, addr: u64) -> bool {
    let start = ctx.nursery_start as u64;
    addr >= start && addr < start + (ctx.nursery_words as u64) * 8
}

/// Copy live nursery objects into the old space; returns promoted words.
/// Old references are left untouched and never scanned (immutability: old
/// cannot point young).
fn minor_collect(ctx: &mut ProcCtx) -> usize {
    let log = std::env::var_os("MANA_GC_LOG").is_some();
    let used_before = ctx.old_used;
    let mut worklist: Vec<u64> = Vec::new();

    unsafe {
        let mut frame = ctx.roots_head as *mut u64;
        while !frame.is_null() {
            let len = *frame.add(1) as usize;
            for i in 0..len {
                let slot = frame.add(2 + i);
                *slot = forward_minor(ctx, *slot, &mut worklist);
            }
            frame = *frame as *mut u64;
        }
        ctx.exc_class = forward_minor(ctx, ctx.exc_class, &mut worklist);
        ctx.exc_reason = forward_minor(ctx, ctx.exc_reason, &mut worklist);

        // all other processes: suspended root chains, mailboxes, exceptions
        let mut procs = std::mem::take(&mut ctx.sched.procs);
        let current = ctx.sched.current;
        for (id, slot) in procs.iter_mut().enumerate() {
            let Some(p) = slot else { continue };
            if id != current {
                let mut frame = p.saved_roots as *mut u64;
                while !frame.is_null() {
                    let len = *frame.add(1) as usize;
                    for i in 0..len {
                        let s = frame.add(2 + i);
                        *s = forward_minor(ctx, *s, &mut worklist);
                    }
                    frame = *frame as *mut u64;
                }
                p.saved_exc_class = forward_minor(ctx, p.saved_exc_class, &mut worklist);
                p.saved_exc_reason = forward_minor(ctx, p.saved_exc_reason, &mut worklist);
            }
            for m in p.mailbox.iter_mut() {
                *m = forward_minor(ctx, *m, &mut worklist);
            }
            p.pending_closure = forward_minor(ctx, p.pending_closure, &mut worklist);
        }
        ctx.sched.procs = procs;

        let eternal = std::mem::take(&mut ctx.eternal);
        for (p, is_cons) in &eternal {
            scan_eternal(ctx, *p, *is_cons, &mut worklist, true, &mut std::ptr::null_mut());
        }
        ctx.eternal = eternal;
        while let Some(t) = worklist.pop() {
            scan_minor(ctx, t, &mut worklist);
        }
    }

    ctx.heap_top = ctx.nursery_start;
    let promoted = ctx.old_used - used_before;
    if log {
        eprintln!(
            "mana: minor gc, promoted {} words (nursery {}, old {} words, limit {})",
            promoted, ctx.nursery_words, ctx.old_used, ctx.old_limit
        );
    }
    promoted
}

unsafe fn forward_minor(ctx: &mut ProcCtx, t: u64, worklist: &mut Vec<u64>) -> u64 {
    if t == 0 {
        return 0; // empty root slot
    }
    match t & TAG_MASK {
        TAG_SMALL | TAG_ATOM | TAG_PID => t,
        _ if t == NIL => t,
        TAG_CONS => unsafe {
            let addr = t & !TAG_MASK;
            if !in_nursery(ctx, addr) {
                return t; // old — and everything it references is old
            }
            let p = addr as *mut u64;
            if *p & TAG_MASK == TAG_FORWARD {
                return (*p & !TAG_MASK) | TAG_CONS;
            }
            let new = old_alloc(ctx, 2);
            *new = *p;
            *new.add(1) = *p.add(1);
            *p = new as u64 | TAG_FORWARD;
            let nt = new as u64 | TAG_CONS;
            worklist.push(nt);
            nt
        },
        TAG_BOXED => unsafe {
            if !in_nursery(ctx, t) {
                return t;
            }
            let p = t as *mut u64;
            if *p & TAG_MASK == TAG_FORWARD {
                return *p & !TAG_MASK;
            }
            let words = 1 + payload_words(*p);
            let new = old_alloc(ctx, words);
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

unsafe fn scan_minor(ctx: &mut ProcCtx, t: u64, worklist: &mut Vec<u64>) {
    unsafe {
        match t & TAG_MASK {
            TAG_CONS => {
                let p = (t & !TAG_MASK) as *mut u64;
                *p = forward_minor(ctx, *p, worklist);
                *p.add(1) = forward_minor(ctx, *p.add(1), worklist);
            }
            TAG_BOXED => {
                let p = t as *mut u64;
                let header = *p;
                match header & 0xff {
                    KIND_TUPLE => {
                        for i in 0..(header >> 8) as usize {
                            let f = p.add(1 + i);
                            *f = forward_minor(ctx, *f, worklist);
                        }
                    }
                    KIND_FUN => {
                        for i in 0..(header >> 16) as usize {
                            let f = p.add(2 + i);
                            *f = forward_minor(ctx, *f, worklist);
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
}

/// Full copy of the old space into one fresh chunk. Runs right after a
/// minor collection, so the nursery is empty and every live object is old.
fn major_collect(ctx: &mut ProcCtx) {
    let log = std::env::var_os("MANA_GC_LOG").is_some();
    let used_before = ctx.old_used;
    // live <= old_used, so one chunk of old_used words always fits
    let to_words = usize::max(ctx.old_used, OLD_CHUNK_WORDS);
    let to_space = alloc_space(to_words);
    let mut top = to_space;
    let mut worklist: Vec<u64> = Vec::new();

    unsafe {
        let mut frame = ctx.roots_head as *mut u64;
        while !frame.is_null() {
            let len = *frame.add(1) as usize;
            for i in 0..len {
                let slot = frame.add(2 + i);
                *slot = forward_major(*slot, &mut top, &mut worklist);
            }
            frame = *frame as *mut u64;
        }
        ctx.exc_class = forward_major(ctx.exc_class, &mut top, &mut worklist);
        ctx.exc_reason = forward_major(ctx.exc_reason, &mut top, &mut worklist);

        let mut procs = std::mem::take(&mut ctx.sched.procs);
        let current = ctx.sched.current;
        for (id, slot) in procs.iter_mut().enumerate() {
            let Some(p) = slot else { continue };
            if id != current {
                let mut frame = p.saved_roots as *mut u64;
                while !frame.is_null() {
                    let len = *frame.add(1) as usize;
                    for i in 0..len {
                        let s = frame.add(2 + i);
                        *s = forward_major(*s, &mut top, &mut worklist);
                    }
                    frame = *frame as *mut u64;
                }
                p.saved_exc_class = forward_major(p.saved_exc_class, &mut top, &mut worklist);
                p.saved_exc_reason = forward_major(p.saved_exc_reason, &mut top, &mut worklist);
            }
            for m in p.mailbox.iter_mut() {
                *m = forward_major(*m, &mut top, &mut worklist);
            }
            p.pending_closure = forward_major(p.pending_closure, &mut top, &mut worklist);
        }
        ctx.sched.procs = procs;

        let eternal = std::mem::take(&mut ctx.eternal);
        for (p, is_cons) in &eternal {
            scan_eternal(ctx, *p, *is_cons, &mut worklist, false, &mut top);
        }
        ctx.eternal = eternal;
        while let Some(t) = worklist.pop() {
            scan_major(t, &mut top, &mut worklist);
        }
        for chunk in &ctx.old {
            free_space(chunk.start, chunk.words);
        }
    }

    let live = (top as usize - to_space as usize) / 8;
    ctx.old = vec![Chunk {
        start: to_space,
        top,
        end: unsafe { to_space.add(to_words) },
        words: to_words,
    }];
    ctx.old_used = live;
    ctx.old_limit = usize::max(4 * live, OLD_LIMIT_INIT);
    if log {
        eprintln!(
            "mana: major gc, {} -> {} live words (limit {})",
            used_before, live, ctx.old_limit
        );
    }
}

unsafe fn forward_major(t: u64, top: &mut *mut u64, worklist: &mut Vec<u64>) -> u64 {
    if t == 0 {
        return 0; // empty root slot
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

unsafe fn scan_major(t: u64, top: &mut *mut u64, worklist: &mut Vec<u64>) {
    unsafe {
        match t & TAG_MASK {
            TAG_CONS => {
                let p = (t & !TAG_MASK) as *mut u64;
                *p = forward_major(*p, top, worklist);
                *p.add(1) = forward_major(*p.add(1), top, worklist);
            }
            TAG_BOXED => {
                let p = t as *mut u64;
                let header = *p;
                match header & 0xff {
                    KIND_TUPLE => {
                        for i in 0..(header >> 8) as usize {
                            let f = p.add(1 + i);
                            *f = forward_major(*f, top, worklist);
                        }
                    }
                    KIND_FUN => {
                        for i in 0..(header >> 16) as usize {
                            let f = p.add(2 + i);
                            *f = forward_major(*f, top, worklist);
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
}

fn payload_words(header: u64) -> usize {
    match header & 0xff {
        KIND_TUPLE => (header >> 8) as usize,
        KIND_FLOAT => 1,
        KIND_FUN => 1 + (header >> 16) as usize,
        _ => 0,
    }
}

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

/// Forward the term fields of one eternal object (minor or major mode).
/// The object itself never moves.
unsafe fn scan_eternal(
    ctx: &mut ProcCtx,
    p: *mut u64,
    is_cons: bool,
    worklist: &mut Vec<u64>,
    minor: bool,
    major_top: &mut *mut u64,
) {
    unsafe {
        macro_rules! fwd {
            ($slot:expr) => {{
                let s = $slot;
                if minor {
                    *s = forward_minor(ctx, *s, worklist);
                } else {
                    *s = forward_major(*s, major_top, worklist);
                }
            }};
        }
        if is_cons {
            fwd!(p);
            fwd!(p.add(1));
            return;
        }
        let header = *p;
        match header & 0xff {
            KIND_TUPLE => {
                for i in 0..(header >> 8) as usize {
                    fwd!(p.add(1 + i));
                }
            }
            KIND_FUN => {
                for i in 0..(header >> 16) as usize {
                    fwd!(p.add(2 + i));
                }
            }
            _ => {} // float: no term fields
        }
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
            out.push_str(&String::from_utf8_lossy(bytes));
        },
        _ if t == NIL => out.push_str("[]"),
        TAG_PID => {
            out.push_str(&format!("<0.{}.0>", t >> 3));
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
            let kind = header & 0xff;
            match kind {
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
