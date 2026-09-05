//! Exit signals, links, and monitors. Every term that this module hands to
//! another process must be old, eternal, or immediate. There is no remembered
//! set, so a minor collection does not see young terms in shared tuples.

use super::*;

/// Allocate `words` words in the shared old space. Every process can see this
/// space.
pub(crate) fn alloc_shared(ctx: &mut ProcCtx, words: usize) -> *mut u64 {
    let g = ctx.global;
    let mut old = g.old.lock();
    old.alloc(words, &g.old_used)
}

/// Build a tuple in shared space. Each item must be old, eternal, or immediate.
pub(crate) fn shared_tuple(ctx: &mut ProcCtx, items: &[u64]) -> u64 {
    let p = alloc_shared(ctx, 1 + items.len());
    unsafe {
        *p = ((items.len() as u64) << 8) | KIND_TUPLE;
        for (i, v) in items.iter().enumerate() {
            *p.add(1 + i) = *v;
        }
    }
    p as u64
}

/// Push a message that is already shared-safe, then wake the target.
pub(crate) fn push_and_wake(ctx: &mut ProcCtx, id: usize, msg: u64) {
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

/// Deliver an exit signal to `target`. `forced` is true for exit(Pid, kill).
pub(crate) fn exit_signal(
    ctx: &mut ProcCtx,
    from_pid: usize,
    target: usize,
    reason: u64,
    forced: bool,
) {
    let g = ctx.global;
    // The reason lands in old-space tuples and in the cross-scheduler
    // pending_kill. A minor collection does not see young terms there. There
    // is no remembered set.
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
    // Wake the target so that its home scheduler sees the pending kill.
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

/// Handle a dead process. Notify the monitors, send exit signals to the links,
/// and free the slot.
pub(crate) fn process_death(ctx: &mut ProcCtx, pid: usize, reason: u64) {
    let g = ctx.global;
    // The reason goes into old-space DOWN tuples and exit signals.
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
            &[
                known().down_up,
                ref_term,
                known().process,
                make_pid(pid),
                reason,
            ],
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
    // Remove the stale monitor entries from the targets that this process
    // watched.
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

/// erlang:link/1. The link is bidirectional. A link to a dead pid delivers a
/// noproc exit signal.
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
        unsafe { proc_mut(cell) }
            .lstate
            .lock()
            .links
            .retain(|&x| x != me);
    }
    if let Some(cell) = proc_ref(ctx.global, me) {
        unsafe { proc_mut(cell) }
            .lstate
            .lock()
            .links
            .retain(|&x| x != id);
    }
    1
}

/// erlang:monitor(process, Pid). The function returns the ref. If the target
/// is dead, the caller gets an immediate noproc DOWN message.
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
        let t = ls
            .monitoring
            .iter()
            .find(|&&(rid, _)| rid == ref_id)
            .map(|&(_, t)| t);
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

/// Reply aliases from the OTP 24 monitor options. The map goes from the ref
/// word to the target pid. A send to a ref consults this table. A send to an
/// absent alias does nothing. This matches BEAM.
pub(crate) static ALIASES: std::sync::Mutex<Option<std::collections::HashMap<u64, usize>>> =
    std::sync::Mutex::new(None);

/// erlang:monitor/3 is monitor/2 plus options. The {alias, _} option is
/// supported. TODO(alias-modes): every deactivation mode behaves like
/// demonitor. The function ignores other options.
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

pub(crate) fn drop_alias(r: u64) {
    if let Some(map) = ALIASES.lock().unwrap().as_mut() {
        map.remove(&r);
    }
}

/// demonitor/2 with the flush option. The function also removes a
/// {'DOWN', Ref, ...} message that is already in the mailbox. The info option
/// returns false if the DOWN already fired. Here the result is an
/// approximation: it reports whether the function flushed a message.
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
        p.private.push_back(m);
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
    // A removal before the cursor shifts the cursor. Adjust the cursor so that
    // the receive scan stays on the same message.
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

/// erlang:exit/2. The target cannot trap the kill reason. The kill reason
/// propagates as killed.
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

/// process_flag(trap_exit, Bool). The function returns the previous value.
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

/// erlang:hibernate/3. Discard the (conceptual) stack, wait for a message,
/// then continue at apply(M, F, A). In the usual case the applied function
/// does not return. If it returns, the process exits with reason normal.
#[no_mangle]
pub extern "C" fn mana_rt_hibernate(ctx: *mut ProcCtx, m: u64, f: u64, a: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    // The args list is a heap term that lives across suspends, so it needs a
    // root. The GC scans and updates the root-frame chain of the parked
    // coroutine.
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
        // Publish Waiting, then check the ingress again under the lock. This
        // closes the same lost-wakeup window as recv_wait and park_on_socket.
        {
            let mut st = p.state.lock();
            *st = PState::Waiting(None);
            if !p.ingress.is_empty() {
                *st = PState::Running;
                continue;
            }
        }
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
