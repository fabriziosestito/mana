use super::*;

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
            if bignum_parts(a).is_some() || bignum_parts(b).is_some() {
                // int vs int: exact; int vs float: f64 (num_val knows bigs)
                if is_int_term(a) && is_int_term(b) {
                    return int_cmp_exact(a, b);
                }
                let (x, y) = (num_val(a), num_val(b));
                return (x > y) as i64 - (x < y) as i64;
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
            // bin kinds first: a view and a plain binary with equal bytes
            // are =:= even though their headers differ, so the header
            // fast-reject below must not see them
            let bin_kind = |h: u64| matches!(h & 0xff, KIND_BIN | KIND_SUBBIN);
            if bin_kind(ha) || bin_kind(hb) {
                return (bin_kind(ha) && bin_kind(hb) && bin_bytes(a) == bin_bytes(b)) as i64;
            }
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
                KIND_BIGNUM => {
                    // headers equal ⇒ same sign and limb count
                    for i in 0..(ha >> 9) as usize {
                        if *pa.add(1 + i) != *pb.add(1 + i) {
                            return 0;
                        }
                    }
                    1
                }
                _ => 0, // funs: identity only (raw-equal handled above)
            }
        },
        _ => 0,
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
