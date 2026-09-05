use super::*;

// ---------------------------------------------------------------------------
// global state

pub(crate) struct OldSpace {
    pub(crate) chunks: Vec<Chunk>,
}

impl OldSpace {
    /// Bump-allocate in the shared old space (caller holds the lock).
    pub(crate) fn alloc(&mut self, words: usize, used: &AtomicUsize) -> *mut u64 {
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
pub(crate) enum PState {
    Runnable,
    Running,
    /// waiting for a message, with an optional wake deadline
    Waiting(Option<Instant>),
}

pub(crate) type ProcCoro = Coroutine<(), (), u64, DefaultStack>;

pub(crate) struct Process {
    pub(crate) home: usize,
    pub(crate) coro: Option<ProcCoro>,
    pub(crate) yielder: *const Yielder<(), ()>,
    pub(crate) saved_roots: u64,
    pub(crate) saved_exc_class: u64,
    pub(crate) saved_exc_reason: u64,
    /// lock-free sender-side queue. Cross-scheduler senders only ever push
    /// old-space/immediate terms (send promotes); same-scheduler pushes may
    /// be young (local minors drain + scan).
    pub(crate) ingress: SegQueue<u64>,
    /// receiver-private message list — home scheduler only, no lock
    /// home-thread mailbox. VecDeque: remove_message pops from the front
    /// (or near it) — with a Vec that was O(N) per receive under a backlog
    /// (a gen_server behind 100k messages spent seconds shifting the tail).
    pub(crate) private: std::collections::VecDeque<u64>,
    /// receive cursor into `private` — home scheduler only
    pub(crate) cursor: usize,
    pub(crate) state: Mutex<PState>,
    /// spawn closure (old-space) until first resume
    pub(crate) pending_closure: u64,
    /// links/monitors/trap flag — mutated cross-thread under this lock
    pub(crate) lstate: Mutex<LinkState>,
    /// process dictionary. Values are promoted at put, so cross-thread
    /// readers (process_info) only ever see old-space/immediate terms.
    pub(crate) pdict: Mutex<Vec<(u64, u64)>>,
    /// may this process reference its home scheduler's CURRENT nursery?
    /// Set when it runs (swap-out) or receives any message; cleared by the
    /// minor that scans it. Clean parked processes are skipped by minors —
    /// a parked process only gains nursery refs by running or by a local
    /// send, and its previous refs were forwarded by the prior minor.
    pub(crate) dirty: std::sync::atomic::AtomicBool,
}

#[derive(Default)]
pub(crate) struct LinkState {
    pub(crate) links: Vec<usize>,
    /// (ref id, watcher pid) — processes monitoring me
    pub(crate) monitors_on_me: Vec<(u64, usize)>,
    /// (ref id, target pid) — processes I monitor
    pub(crate) monitoring: Vec<(u64, usize)>,
    pub(crate) trap_exit: bool,
    /// pending unhandled exit signal: reason term (old-space/eternal), 0 = none
    pub(crate) pending_kill: u64,
}

/// Home-scheduler pinning makes the interior safe: only the home thread (or
/// the STW requester while everyone is parked) touches non-Mutex fields.
pub(crate) struct ProcessCell(pub(crate) UnsafeCell<Process>);

unsafe impl Send for ProcessCell {}

unsafe impl Sync for ProcessCell {}

pub(crate) struct SchedShared {
    /// pids made runnable by other threads (lock-free)
    pub(crate) inject: SegQueue<usize>,
    /// wake signal for an idle scheduler; the bool defeats lost wakeups
    pub(crate) cv: Condvar,
    pub(crate) cv_m: Mutex<bool>,
    /// registered ProcCtx pointer (for the STW requester)
    pub(crate) ctx_addr: AtomicUsize,
}

pub(crate) struct StwState {
    pub(crate) collecting: bool,
    pub(crate) parked: usize,
    pub(crate) gen: u64,
}

pub(crate) struct Global {
    pub(crate) n_scheds: usize,
    /// fast-path flag mirroring StwState.collecting
    pub(crate) stw_flag: AtomicBool,
    pub(crate) scheds: Vec<SchedShared>,
    pub(crate) procs: RwLock<Vec<Option<&'static ProcessCell>>>,
    pub(crate) old: Mutex<OldSpace>,
    pub(crate) old_used: AtomicUsize,
    pub(crate) old_limit: AtomicUsize,
    pub(crate) eternal: Mutex<Vec<(usize, bool)>>,
    pub(crate) stw: Mutex<StwState>,
    pub(crate) stw_cv: Condvar,
    pub(crate) spawn_rr: AtomicUsize,
    pub(crate) shutdown: AtomicBool,
    pub(crate) gc_log: bool,
}

#[repr(C)]
pub struct ProcCtx {
    pub heap_top: *mut u64, // word 0 — codegen contract (nursery)
    pub heap_end: *mut u64, // word 1 — codegen contract (nursery)
    pub roots_head: u64,    // word 2 — codegen contract
    pub exc_class: u64,     // word 3 — codegen contract
    pub exc_reason: u64,    // word 4 — codegen contract
    pub reductions: i64,    // word 5 — codegen contract
    /// word 6 — codegen contract: per-scheduler argument spill for the
    /// uniform compiled ABI (`ctx + 6 words`). Callers of arity > 6 write
    /// args 5.. here right before the call; the callee prologue reads them
    /// before anything else runs. Only valid across that one call edge.
    pub argv_spill: *mut u64,
    pub(crate) nursery_start: *mut u64,
    pub(crate) nursery_words: usize,
    pub(crate) global: &'static Global,
    pub(crate) sched_id: usize,
    pub(crate) run_q: VecDeque<usize>,
    pub(crate) current: usize,
    /// cached &ProcessCell of the running process (hot path: recv primops)
    pub(crate) current_cell: usize,
}

pub(crate) fn proc_ref(g: &Global, pid: usize) -> Option<&'static ProcessCell> {
    g.procs.read().get(pid).copied().flatten()
}

/// Home-thread (or STW-requester) access to a process's interior.
#[allow(clippy::mut_from_ref)]
pub(crate) unsafe fn proc_mut(cell: &ProcessCell) -> &mut Process {
    unsafe { &mut *cell.0.get() }
}

pub(crate) static REF_COUNTER: AtomicUsize = AtomicUsize::new(1);

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

pub(crate) fn new_sched_ctx(global: &'static Global, sched_id: usize) -> *mut ProcCtx {
    let nwords = initial_nursery_words();
    let nursery = alloc_space(nwords);
    let ctx = Box::into_raw(Box::new(ProcCtx {
        heap_top: nursery,
        heap_end: unsafe { nursery.add(nwords) },
        roots_head: 0,
        exc_class: 0,
        exc_reason: 0,
        reductions: REDUCTIONS_PER_SLICE,
        argv_spill: Box::into_raw(Box::new([0u64; ARGV_SPILL_WORDS])) as *mut u64,
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

pub(crate) fn wake_sched(g: &Global, id: usize) {
    let s = &g.scheds[id];
    let mut pending = s.cv_m.lock();
    *pending = true;
    s.cv.notify_all();
}

pub(crate) fn register_process(g: &Global, p: Process) -> usize {
    let cell: &'static ProcessCell = Box::leak(Box::new(ProcessCell(UnsafeCell::new(p))));
    let mut tab = g.procs.write();
    tab.push(Some(cell));
    tab.len() - 1
}

/// Coroutine for a spawned process: applies the (old-space) closure.
pub(crate) fn make_coroutine(global: &'static Global, home: usize) -> ProcCoro {
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
                let code = *((cl & !TAG_MASK) as *const u64).add(1) as usize;
                call_fun_code(ctx, code, &[], cl)
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
                private: std::collections::VecDeque::new(),
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

pub(crate) fn scheduler_loop(ctx: &mut ProcCtx, mut root_result: Option<&mut u64>) {
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
        {
            // a pid can sit in the run queue more than once (woken, ran,
            // parked again, woken again before the stale entry drained);
            // resuming a Waiting coroutine would make its park return
            // spuriously. Only Runnable entries run.
            let mut st = p.state.lock();
            if *st != PState::Runnable {
                continue;
            }
            *st = PState::Running;
        }
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
pub(crate) fn idle_wait(ctx: &mut ProcCtx) {
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

pub(crate) fn suspend_current(ctx: &mut ProcCtx) {
    let yielder = cur_proc(ctx).yielder;
    unsafe { (*yielder).suspend(()) };
}
