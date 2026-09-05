use super::*;

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

pub(crate) enum SockSource {
    Listener(mio::net::TcpListener),
    Stream(mio::net::TcpStream),
}

/// {active, false | once | true}
#[derive(Clone, Copy, PartialEq)]
pub(crate) enum ActiveMode {
    Passive,
    Once,
    Always,
}

pub(crate) struct SockEntry {
    pub(crate) source: SockSource,
    /// pid parked waiting for readability (recv/accept), if any
    pub(crate) read_waiter: Option<usize>,
    /// pid parked waiting for writability (send/connect), if any
    pub(crate) write_waiter: Option<usize>,
    /// registered with the reactor's poll (edge-triggered readiness is
    /// re-armed by the kernel on new activity, and parkers only park after
    /// WouldBlock, so edges are never missed)
    pub(crate) registered: bool,
    pub(crate) owner: usize,
    pub(crate) active: ActiveMode,
    /// binary (true) vs charlist (false) delivery
    pub(crate) binary: bool,
    /// passive-recv buffer (exact-length recv accumulates here)
    pub(crate) rbuf: Vec<u8>,
    /// byte counters for inet:getstat
    pub(crate) recv_oct: u64,
    pub(crate) send_oct: u64,
}

pub(crate) struct SocketTable {
    pub(crate) slots: Vec<Option<SockEntry>>,
    pub(crate) free: Vec<usize>,
}

impl SocketTable {
    pub(crate) fn insert(&mut self, e: SockEntry) -> usize {
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

pub(crate) static SOCKETS: std::sync::Mutex<SocketTable> = std::sync::Mutex::new(SocketTable {
    slots: Vec::new(),
    free: Vec::new(),
});

thread_local! {
    /// Per-scheduler-thread read scratch for socket recv/pump. Allocating
    /// and zeroing a fresh 64 KiB chunk per read cost ~11% of a Phoenix
    /// request's instructions (callgrind). Safe to share across the
    /// coroutines of one thread: every use reads then copies out under the
    /// SOCKETS lock with no yield in between.
    static RECV_SCRATCH: std::cell::RefCell<Vec<u8>> = std::cell::RefCell::new(vec![0u8; 65536]);
}

pub(crate) fn with_recv_scratch<R>(f: impl FnOnce(&mut [u8]) -> R) -> R {
    RECV_SCRATCH.with(|c| f(&mut c.borrow_mut()[..]))
}

/// (pid, socket idx, wanted-read) wake tokens from the reactor thread.
pub(crate) static IO_WAKES: SegQueue<(usize, usize, bool)> = SegQueue::new();

/// socket indices whose sources the reactor should register with its poll.
pub(crate) static REACTOR_CMDS: SegQueue<usize> = SegQueue::new();

pub(crate) static REACTOR_WAKER: std::sync::OnceLock<mio::Waker> = std::sync::OnceLock::new();

pub(crate) static REACTOR_STARTED: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

pub(crate) const REACTOR_WAKE_TOKEN: mio::Token = mio::Token(usize::MAX);

pub(crate) fn ensure_reactor(g: &'static Global) {
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

pub(crate) fn reactor_wake() {
    if let Some(w) = REACTOR_WAKER.get() {
        let _ = w.wake();
    }
}

pub(crate) fn reactor_thread(g: &'static Global) {
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
            // The waiter slot is NOT cleared here: it is the liveness signal
            // drain_io_wakes uses to keep a token alive until the parker has
            // actually suspended (the op clears its own slot when it
            // completes). Clearing it here dropped tokens that raced the
            // park — a lost socket wake.
            if ev.is_readable() || closed {
                if let Some(pid) = entry.read_waiter {
                    IO_WAKES.push((pid, idx, true));
                    woke = true;
                } else if entry.active != ActiveMode::Passive {
                    // no parked reader: schedule an active-mode pump
                    IO_ACTIVE.push(idx);
                    woke = true;
                }
            }
            if ev.is_writable() || closed {
                if let Some(pid) = entry.write_waiter {
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
pub(crate) fn drain_io_wakes(ctx: &mut ProcCtx) {
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
