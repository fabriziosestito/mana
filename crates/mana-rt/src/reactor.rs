//! The I/O reactor (mio). It serves sockets only. Files use direct
//! syscalls (TODO(io-pool)).
//!
//! The reactor obeys the same discipline as the timer thread. It is OUTSIDE
//! the STW protocol and never changes process or scheduler state. It pushes
//! (pid, sock, kind) wake tokens to IO_WAKES and pokes the scheduler
//! condvars. Schedulers drain the tokens at the top of their loop, which is
//! a safepoint.
//!
//! Blocking syscalls MUST NOT run on scheduler threads. The STW requester
//! waits for every scheduler to reach a safepoint. A blocked syscall
//! deadlocks the GC. Sockets are nonblocking. Scheduler threads only issue
//! nonblocking syscalls, and they park the process on WouldBlock.
//!
//! Wake protocol (no lost wakeups). A parker first writes itself into the
//! waiter slot of the socket entry. Then it makes sure that the socket is
//! registered. Then it retries the syscall. Only then it parks (Waiting +
//! suspend). The reactor takes the waiter and pushes a wake. The wake can
//! arrive while the parker is still Running, in the small window before the
//! suspend. In that case drain_io_wakes pushes the token again, as long as
//! the waiter slot still names that pid. The protocol converges when the
//! parker suspends (the flip succeeds) or completes and clears the slot
//! (the token is dropped as stale).

use super::*;

pub(crate) enum SockSource {
    Listener(mio::net::TcpListener),
    Stream(mio::net::TcpStream),
}

/// The socket option {active, false | once | true}.
#[derive(Clone, Copy, PartialEq)]
pub(crate) enum ActiveMode {
    Passive,
    Once,
    Always,
}

pub(crate) struct SockEntry {
    pub(crate) source: SockSource,
    /// The pid that is parked for readability (recv/accept), if any.
    pub(crate) read_waiter: Option<usize>,
    /// The pid that is parked for writability (send/connect), if any.
    pub(crate) write_waiter: Option<usize>,
    /// True if the source is registered with the poll of the reactor.
    /// Readiness is edge-triggered. The kernel re-arms the edge on new
    /// activity, and parkers only park after WouldBlock. As a result, no
    /// edge is missed.
    pub(crate) registered: bool,
    pub(crate) owner: usize,
    pub(crate) active: ActiveMode,
    /// Delivery mode: binary (true) or charlist (false).
    pub(crate) binary: bool,
    /// Buffer for passive recv. An exact-length recv accumulates bytes here.
    pub(crate) rbuf: Vec<u8>,
    /// Byte counters for inet:getstat.
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
    /// Read scratch buffer for socket recv/pump, one per scheduler thread.
    /// A fresh 64 KiB chunk per read, allocated and zeroed, cost ~11% of the
    /// instructions of a Phoenix request (callgrind). The coroutines of one
    /// thread can share it. Every use reads and then copies out under the
    /// SOCKETS lock, with no yield between the two steps.
    static RECV_SCRATCH: std::cell::RefCell<Vec<u8>> = std::cell::RefCell::new(vec![0u8; 65536]);
}

pub(crate) fn with_recv_scratch<R>(f: impl FnOnce(&mut [u8]) -> R) -> R {
    RECV_SCRATCH.with(|c| f(&mut c.borrow_mut()[..]))
}

/// Wake tokens (pid, socket idx, wanted-read) from the reactor thread.
pub(crate) static IO_WAKES: SegQueue<(usize, usize, bool)> = SegQueue::new();

/// Socket indices whose sources the reactor must register with its poll.
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
    // Wait until the waker exists. Then callers can always poke the reactor.
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
        // Register the sources that were requested since the last pass.
        while let Some(idx) = REACTOR_CMDS.pop() {
            let mut tab = SOCKETS.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                continue; // The socket closed before this pass.
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
            let _ = res; // AlreadyExists on a duplicate request is not an error.
        }
        if poll.poll(&mut events, None).is_err() {
            continue; // EINTR
        }
        let mut woke = false;
        for ev in events.iter() {
            if ev.token() == REACTOR_WAKE_TOKEN {
                continue; // The command pass runs at the top of the loop.
            }
            let idx = ev.token().0;
            let mut tab = SOCKETS.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                continue;
            };
            let closed = ev.is_read_closed() || ev.is_write_closed() || ev.is_error();
            // The waiter slot is NOT cleared here. It is the liveness signal
            // that drain_io_wakes uses to keep a token alive until the parker
            // suspended. The op clears its own slot when it completes. If the
            // slot is cleared here, a token that races the park is dropped,
            // which is a lost socket wake.
            if ev.is_readable() || closed {
                if let Some(pid) = entry.read_waiter {
                    IO_WAKES.push((pid, idx, true));
                    woke = true;
                } else if entry.active != ActiveMode::Passive {
                    // No reader is parked. Schedule an active-mode pump.
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

/// Drain the wake tokens on the scheduler side. This runs at the loop-top
/// safepoint, like the timer deliveries. A wake sends no mailbox message.
/// The woken BIF retries its nonblocking syscall.
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
        // The parker did not suspend yet. Keep the token alive while the
        // waiter slot still names the pid. If the op completed, drop the
        // token as a stale wake.
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
