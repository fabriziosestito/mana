//! The heap verifier behind `MANA_GC_VERIFY=1`. After a collection it walks
//! every reachable term from every root and checks each word. This costs
//! O(live heap) per collection, so it is a knob. The stress matrix turns it
//! on. The always-on checks live in `gc.rs`.
//!
//! What a verifier can prove after a collection:
//! - After a minor, no root of this scheduler reaches this nursery. The minor
//!   evacuated everything live. A hit is a missed root.
//! - After a major, no root at all reaches any nursery. Step 1 of the major
//!   evacuated every nursery.
//! - Every boxed object has a valid header kind. An object inside an old
//!   chunk ends before the chunk top.
//!
//! Eternal objects and compiler statics live outside every chunk. The
//! verifier reads their headers but cannot range-check them.

use super::*;
use rustc_hash::FxHashSet;

/// The live ranges that a reachable pointer must NOT land in.
struct Forbidden {
    nurseries: Vec<(u64, u64)>,
}

impl Forbidden {
    fn contains(&self, addr: u64) -> bool {
        self.nurseries.iter().any(|&(s, e)| addr >= s && addr < e)
    }
}

/// Walk everything reachable from the given root words. `phase` names the
/// collection for the abort message.
unsafe fn verify_reachable(
    phase: &str,
    roots: Vec<u64>,
    forbidden: &Forbidden,
    old: &[(u64, u64)],
) {
    let mut seen: FxHashSet<u64> = FxHashSet::default();
    let mut work = roots;
    while let Some(t) = work.pop() {
        if t == 0 {
            continue;
        }
        let (addr, is_cons) = match t & TAG_MASK {
            TAG_SMALL | TAG_ATOM | TAG_PID => continue,
            _ if t == NIL => continue,
            TAG_CONS => (t & !TAG_MASK, true),
            TAG_BOXED => (t, false),
            _ => gc_abort(
                phase,
                t,
                t,
                "verify: invalid term tag reachable from a root",
            ),
        };
        if !seen.insert(t) {
            continue;
        }
        if forbidden.contains(addr) {
            gc_abort(
                phase,
                addr,
                t,
                "verify: a root reaches an evacuated nursery",
            );
        }
        let p = addr as *mut u64;
        let words = if is_cons {
            2
        } else {
            let header = unsafe { *p };
            if !valid_kind(header) {
                gc_abort(phase, addr, header, "verify: invalid header kind");
            }
            1 + payload_words(header)
        };
        if let Some(&(_, end)) = old.iter().find(|&&(s, e)| addr >= s && addr < e) {
            if addr + (words as u64) * 8 > end {
                gc_abort(
                    phase,
                    addr,
                    unsafe { *p },
                    "verify: object runs past its chunk",
                );
            }
        }
        unsafe {
            scan_fields(p, is_cons, &mut |s| work.push(*s));
        }
    }
}

fn old_ranges(old: &OldSpace) -> Vec<(u64, u64)> {
    old.chunks
        .iter()
        .map(|c| (c.start as u64, c.top as u64))
        .collect()
}

fn nursery_range(ctx: &ProcCtx) -> (u64, u64) {
    let s = ctx.nursery_start as u64;
    (s, s + (ctx.nursery_words as u64) * 8)
}

/// Roots of one process, read only.
fn proc_roots(p: &mut Process, running: bool, out: &mut Vec<u64>) {
    if running {
        walk_proc_shared_roots(p, |s| out.push(unsafe { *s }));
    } else {
        unsafe { walk_proc_roots(p, |s| out.push(*s)) };
    }
    out.extend(p.private.iter().copied());
}

fn ctx_roots(ctx: &ProcCtx, out: &mut Vec<u64>) {
    unsafe {
        let mut frame = ctx.roots_head as *mut u64;
        while !frame.is_null() {
            let len = *frame.add(1) as usize;
            for i in 0..len {
                out.push(*frame.add(2 + i));
            }
            frame = *frame as *mut u64;
        }
    }
    out.push(ctx.exc_class);
    out.push(ctx.exc_reason);
}

/// After a minor collection on this scheduler. Roots: this ctx, and every
/// process homed here, clean or dirty. A clean parked process must not
/// reach this nursery either, so this also checks the dirty-tracking
/// invariant.
pub(crate) fn verify_after_minor(ctx: &ProcCtx) {
    let g = ctx.global;
    let mut roots = Vec::new();
    ctx_roots(ctx, &mut roots);
    {
        let tab = g.procs.read();
        for (id, slot) in tab.iter().enumerate() {
            let Some(cell) = slot else { continue };
            let p = unsafe { proc_mut(cell) };
            if p.home != ctx.sched_id {
                continue;
            }
            proc_roots(p, id == ctx.current, &mut roots);
        }
    }
    let forbidden = Forbidden {
        nurseries: vec![nursery_range(ctx)],
    };
    let old = old_ranges(&g.old.lock());
    unsafe { verify_reachable("minor collection", roots, &forbidden, &old) };
}

/// After a major collection. The world is stopped and every nursery is
/// empty. Roots: every ctx, every process, the eternal registry.
pub(crate) fn verify_after_major(g: &'static Global, old: &OldSpace) {
    let mut roots = Vec::new();
    let mut nurseries = Vec::new();
    let mut running: Vec<usize> = Vec::new();
    for id in 0..g.n_scheds {
        let octx = g.scheds[id].ctx_addr.load(Ordering::Acquire) as *const ProcCtx;
        if octx.is_null() {
            continue;
        }
        let octx = unsafe { &*octx };
        nurseries.push(nursery_range(octx));
        if octx.current != usize::MAX {
            running.push(octx.current);
        }
        ctx_roots(octx, &mut roots);
    }
    {
        let tab = g.procs.read();
        for (id, slot) in tab.iter().enumerate() {
            let Some(cell) = slot else { continue };
            proc_roots(unsafe { proc_mut(cell) }, running.contains(&id), &mut roots);
        }
    }
    {
        let eternal = g.eternal.lock();
        for &(pa, is_cons) in eternal.iter() {
            unsafe { scan_fields(pa as *mut u64, is_cons, &mut |s| roots.push(*s)) };
        }
    }
    let forbidden = Forbidden { nurseries };
    let old = old_ranges(old);
    unsafe { verify_reachable("major collection", roots, &forbidden, &old) };
}
