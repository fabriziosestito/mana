use super::*;

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
pub(crate) fn spawn_mfa_inner(ctx: &mut ProcCtx, m: u64, f: u64, args: u64) -> u64 {
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
            private: std::collections::VecDeque::new(),
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

pub(crate) fn pdict_to_list(ctx: &mut ProcCtx, pid: usize) -> u64 {
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
pub(crate) static NAME_REGISTRY: std::sync::Mutex<Option<std::collections::HashMap<u64, usize>>> =
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
            // ingress length is approximate cross-thread; good enough. The
            // cursor is a receive-scan position, not a consumption mark:
            // the whole queue counts, like BEAM.
            let cell = proc_ref(ctx.global, id).unwrap();
            let p = unsafe { proc_mut(cell) };
            let n = p.private.len() + p.ingress.len();
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
            private: std::collections::VecDeque::new(),
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
pub(crate) fn cur_proc(ctx: &ProcCtx) -> &mut Process {
    debug_assert!(ctx.current_cell != 0);
    unsafe { proc_mut(&*(ctx.current_cell as *const ProcessCell)) }
}

/// Move everything from the ingress queue into the private list.
pub(crate) fn drain_ingress(p: &mut Process) {
    while let Some(m) = p.ingress.pop() {
        p.private.push_back(m);
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
            if p.private.len() <= p.cursor {
                // A timed-out receive ends the scan: the messages this
                // receive skipped must be visible to the next one (BEAM
                // resets the save pointer on timeout).
                p.cursor = 0;
                return 1;
            }
            return 0;
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
                    p.cursor = 0; // timeout ends the scan (see above)
                    return 1;
                }
            }
            // publish Waiting, THEN re-check ingress: a sender on another
            // scheduler pushes to ingress before it reads our state. If it
            // pushed between our drain above and this store, it saw Running
            // and did not wake us — re-checking here closes that window.
            {
                let mut st = p.state.lock();
                *st = PState::Waiting(deadline);
                if !p.ingress.is_empty() {
                    *st = PState::Running;
                    continue;
                }
            }
        }
        suspend_current(ctx);
    }
}
