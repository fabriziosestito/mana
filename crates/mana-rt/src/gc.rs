//! Garbage collection: promotion at send time, scheduler-local minor
//! collection, and stop-the-world major collection.
//!
//! The contract: no scheduler holds a reference into the nursery of another
//! scheduler. Send-time promotion keeps this true. As a result, a minor
//! collection needs only the old-space lock. A major collection parks every
//! other scheduler at a safepoint, evacuates all nurseries, and compacts the
//! old space into one fresh chunk.

use super::*;

// Promotion

/// The poison word for evacuated memory. Its tag is `0b101` (the exception
/// sentinel) and its low byte `0xe5` is not a valid kind, so a stale read of
/// it aborts through the collector checks.
pub(crate) const POISON: u64 = 0xdead_beef_dead_bee5;

/// Every valid heap header kind. Kind 7 is `TAG_FORWARD` and must never
/// appear as a kind.
#[inline]
pub(crate) fn valid_kind(header: u64) -> bool {
    matches!(
        header & 0xff,
        KIND_TUPLE | KIND_FLOAT | KIND_FUN | KIND_BIGNUM | KIND_MAP | KIND_BIN | KIND_SUBBIN
    )
}

/// The always-on check of a boxed object that the collector is about to copy.
/// Returns the object size in words. Aborts if the header kind is invalid or
/// if the object runs past `limit`, the end of the live part of its space.
/// The check reads the header word that the copy needs anyway. A garbage
/// header with a large size would otherwise copy memory past the chunk.
#[inline]
pub(crate) unsafe fn checked_words(phase: &str, p: *const u64, limit: *const u64) -> usize {
    let header = unsafe { *p };
    if !valid_kind(header) {
        gc_abort(phase, p as u64, header, "invalid header kind");
    }
    let words = 1 + payload_words(header);
    if unsafe { p.add(words) } > limit {
        gc_abort(
            phase,
            p as u64,
            header,
            "object runs past the end of its space",
        );
    }
    words
}

/// Abort with the bad word. Exit code 70 is the same one that the other
/// runtime aborts use.
pub(crate) fn gc_abort(phase: &str, addr: u64, word: u64, why: &str) -> ! {
    eprintln!(
        "mana: heap corruption during {}: {} (address {:#x}, word {:#x}). \
         A runtime helper held a term across an allocation, or stored a young \
         term into old space without promotion.",
        phase, why, addr, word
    );
    std::process::exit(70)
}

/// Fill a range with `POISON`. Used by the stress knob `MANA_GC_POISON=1`
/// and by debug builds after every evacuation.
pub(crate) unsafe fn poison(start: *mut u64, end: *mut u64) {
    let mut p = start;
    while p < end {
        unsafe {
            *p = POISON;
            p = p.add(1);
        }
    }
}

pub(crate) fn term_in_nursery(ctx: &ProcCtx, t: u64) -> bool {
    match t & TAG_MASK {
        TAG_CONS => in_my_nursery(ctx, t & !TAG_MASK),
        TAG_BOXED if t != 0 => in_my_nursery(ctx, t),
        _ => false,
    }
}

/// Deep-copy every part of `t` that lives in the nursery of this scheduler
/// into the shared old space. Old, eternal, and immediate parts pass with no
/// copy. The function does not write to the source (no forwarding). As a
/// result, the copy duplicates a part that is shared inside one message.
/// The copying send of BEAM makes the same trade. The loop is iterative
/// because a payload can be very deep and this code runs on a small
/// coroutine stack.
pub(crate) fn promote_term(ctx: &mut ProcCtx, t: u64) -> u64 {
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

/// Shallow-copy one object into the old space. The result keeps the tag of `t`.
pub(crate) fn promote_copy(ctx: &ProcCtx, old: &mut OldSpace, t: u64) -> u64 {
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

// Allocation and GC

/// The allocation slow path. Compiled code bumps the nursery inline.
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
    // Adaptive nursery: grow it until minor collections rarely promote.
    let grow_to = if words > ctx.nursery_words {
        usize::max(ctx.nursery_words * 2, words * 2)
    } else if promoted > ctx.nursery_words / 16 {
        ctx.nursery_words * 2
    } else {
        0
    };
    // The stress pin (MANA_NURSERY_WORDS) stops adaptive growth. A request
    // that cannot fit the pinned nursery must still grow it.
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

/// Eternal objects are write-once. Their fields can reference the current
/// nursery of the ALLOCATING scheduler only until the next minor collection
/// of that scheduler forwards them. After that, they point to old or static
/// terms forever. A minor collection therefore scans only the fresh eternals
/// (this list). A major collection (old-space compaction) walks the
/// permanent registry. A scan of the whole registry per minor collection
/// made keepalive GC quadratic, because eternals accrue per request.
pub(crate) static FRESH_ETERNALS: std::sync::Mutex<Vec<(usize, bool, usize)>> =
    std::sync::Mutex::new(Vec::new());

/// Allocation for the raise path. The object never moves. Collections scan
/// its fields.
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

/// Apply `f` to each saved GC root slot of one process.
pub(crate) unsafe fn walk_proc_roots(p: &mut Process, mut f: impl FnMut(*mut u64)) {
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

/// Apply `f` to the live shared state of one process: the pdict and a
/// pending exit reason. This state stays valid while the process is swapped
/// in. Unlike the saved_* fields, a collection must forward it for RUNNING
/// processes too. A major collection frees every old chunk, and pd_put
/// promotes into the old space.
pub(crate) fn walk_proc_shared_roots(p: &mut Process, mut f: impl FnMut(*mut u64)) {
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

/// Scheduler-local minor collection: copy the live nursery objects into the
/// shared old space. Nothing outside this scheduler references its nursery
/// (send-time promotion). As a result, the only synchronization is the
/// old-space lock, held for the whole collection.
pub(crate) fn minor_collect(ctx: &mut ProcCtx) -> usize {
    let g = ctx.global;
    let used_before = g.old_used.load(Ordering::Relaxed);
    let mut worklist: Vec<u64> = Vec::new();
    let mut old = g.old.lock();

    unsafe {
        // The live root chain of the current process is in ctx.
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

        // Suspended processes pinned to this scheduler. For messages, drain
        // ingress into private first, then scan private. A message that
        // arrives from another scheduler during the scan is old (send
        // promotes). It is safe to leave that message in ingress without a
        // scan.
        {
            let tab = g.procs.read();
            for (id, slot) in tab.iter().enumerate() {
                let Some(cell) = slot else { continue };
                let p = proc_mut(cell);
                if p.home != ctx.sched_id {
                    continue;
                }
                if id != ctx.current {
                    // A clean parked process cannot reference this nursery.
                    // The minor collection that cleared the flag forwarded
                    // its roots. A new reference (the process runs, or it
                    // receives a message) sets the flag again. This keeps a
                    // minor collection O(active processes), not O(all
                    // processes).
                    if !p.dirty.swap(false, Ordering::AcqRel) {
                        continue;
                    }
                    walk_proc_roots(p, |s| {
                        *s = forward_minor(ctx, &mut old, *s, &mut worklist);
                    });
                } else {
                    // pd_put promotes, so this walk is normally a
                    // pass-through. It keeps the pdict correct if a nursery
                    // term ever lands there.
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

        // Eternal objects (exception reasons) can reference this nursery, but
        // only the ones allocated on THIS scheduler since its last minor
        // collection. Eternals are write-once: after one forwarding pass,
        // their fields are old or static forever. Only a major collection
        // walks the full registry.
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

    if g.gc_poison {
        // Stale pointers into the evacuated nursery now read POISON and
        // abort at the next collection instead of reading a plausible copy.
        unsafe { poison(ctx.nursery_start, ctx.heap_top) };
    }
    ctx.heap_top = ctx.nursery_start;
    if g.gc_verify {
        verify_after_minor(ctx);
    }
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

/// Apply `f` to each term-field slot of the object at `p`. A cons cell has
/// no header, so pass `is_cons` for it. A boxed object describes itself in
/// its header.
pub(crate) unsafe fn scan_fields(p: *mut u64, is_cons: bool, f: &mut impl FnMut(*mut u64)) {
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
            // Sub-binary view: the parent binary is a term field.
            KIND_SUBBIN => f(p.add(1)),
            _ => {}
        }
    }
}

pub(crate) unsafe fn forward_minor(
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
            if p.add(2) > ctx.heap_top {
                gc_abort(
                    "minor collection",
                    addr,
                    *p,
                    "cons cell past the nursery top",
                );
            }
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
            let words = checked_words("minor collection", p, ctx.heap_top);
            let new = old.alloc(words, &ctx.global.old_used);
            std::ptr::copy_nonoverlapping(p, new, words);
            *p = new as u64 | TAG_FORWARD;
            let nt = new as u64;
            worklist.push(nt);
            nt
        },
        _ => gc_abort("minor collection", t, t, "invalid term tag"),
    }
}

// Stop-the-world major collection

/// Park at a safepoint while another scheduler runs a major collection.
pub(crate) fn park_if_stw(ctx: &mut ProcCtx) {
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

/// Request a stop-the-world major collection. The collection runs after
/// every other scheduler parked at a safepoint.
pub(crate) fn stw_major(ctx: &mut ProcCtx) {
    let g = ctx.global;
    {
        let mut stw = g.stw.lock();
        if stw.collecting {
            drop(stw);
            park_if_stw(ctx); // Another scheduler collects. Park with it.
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

/// All other schedulers are parked. Evacuate every nursery, then compact
/// the old space into one fresh chunk.
pub(crate) fn major_collect_stw(ctx: &mut ProcCtx) {
    let g = ctx.global;
    let used_before = g.old_used.load(Ordering::Relaxed);

    // 1. Evacuate the nursery of every scheduler. Their ctxs are quiescent.
    for id in 0..g.n_scheds {
        let octx = g.scheds[id].ctx_addr.load(Ordering::Acquire) as *mut ProcCtx;
        if octx.is_null() {
            continue;
        }
        minor_collect(unsafe { &mut *octx });
    }

    // 2. Full copy of the old space, on one thread.
    let mut old = g.old.lock();
    let live_bound = g.old_used.load(Ordering::Relaxed);
    let to_words = usize::max(live_bound, OLD_CHUNK_WORDS);
    let to_space = alloc_space(to_words);
    let mut top = to_space;
    let mut worklist: Vec<u64> = Vec::new();
    // From-space extents. Only terms inside these move. Everything else
    // (eternals, compiler statics) passes through untouched.
    let from: Vec<(usize, usize)> = old
        .chunks
        .iter()
        .map(|c| (c.start as usize, c.top as usize))
        .collect();
    let from = &from[..];

    // Pids that are swapped into a scheduler now. Their LIVE state is in the
    // ctx (walked below). Their saved_* fields are stale from the last yield
    // and must not be scanned.
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
                    // Running process: the saved_* fields are stale, but the
                    // pdict and pending_kill are live and hold old-space
                    // terms. The from-space is about to be freed.
                    walk_proc_shared_roots(p, |s| {
                        *s = forward_major(*s, from, &mut top, &mut worklist);
                    });
                }
                drain_ingress(p); // Everyone is parked: no concurrent pushes.
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
            if g.gc_poison {
                poison(chunk.start, chunk.top);
            }
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
    if g.gc_verify {
        verify_after_major(g, &old);
    }
    if g.gc_log {
        eprintln!(
            "mana: major gc, {} -> {} live words (limit {})",
            used_before,
            live,
            g.old_limit.load(Ordering::Relaxed)
        );
    }
}

/// Boxed and cons terms outside the from-space chunks are eternal mallocs
/// and compiler statics (binaries, funs). They never move, and this function
/// never writes a forwarding header into them. A write to `.rodata` faults,
/// and the eternal registry scan must keep seeing real headers. The eternal
/// registry walk updates their fields instead.
pub(crate) unsafe fn forward_major(
    t: u64,
    from: &[(usize, usize)],
    top: &mut *mut u64,
    worklist: &mut Vec<u64>,
) -> u64 {
    if t == 0 {
        return 0;
    }
    // The end of the from-space chunk that holds `p`, or None when `p` is
    // outside every from-space chunk.
    let from_end = |p: u64| {
        let a = p as usize;
        from.iter()
            .find(|&&(s, e)| a >= s && a < e)
            .map(|&(_, e)| e as *const u64)
    };
    match t & TAG_MASK {
        TAG_SMALL | TAG_ATOM | TAG_PID => t,
        _ if t == NIL => t,
        TAG_CONS => unsafe {
            let p = (t & !TAG_MASK) as *mut u64;
            let Some(end) = from_end(p as u64) else {
                return t;
            };
            if p.add(2) > end as *mut u64 {
                gc_abort(
                    "major collection",
                    p as u64,
                    *p,
                    "cons cell past the end of its chunk",
                );
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
            let Some(end) = from_end(p as u64) else {
                return t;
            };
            if *p & TAG_MASK == TAG_FORWARD {
                return *p & !TAG_MASK;
            }
            let words = checked_words("major collection", p, end);
            let new = *top;
            std::ptr::copy_nonoverlapping(p, new, words);
            *top = top.add(words);
            *p = new as u64 | TAG_FORWARD;
            let nt = new as u64;
            worklist.push(nt);
            nt
        },
        _ => gc_abort("major collection", t, t, "invalid term tag"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn poison_is_never_a_valid_term_or_header() {
        assert_eq!(POISON & TAG_MASK, EXC_SENTINEL);
        assert!(!valid_kind(POISON));
    }

    #[test]
    fn forward_tag_is_not_a_kind() {
        assert!(!valid_kind(TAG_FORWARD));
        for k in [
            KIND_TUPLE,
            KIND_FLOAT,
            KIND_FUN,
            KIND_BIGNUM,
            KIND_MAP,
            KIND_BIN,
            KIND_SUBBIN,
        ] {
            assert!(valid_kind(k));
        }
    }
}
