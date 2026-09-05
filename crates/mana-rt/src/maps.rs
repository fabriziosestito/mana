use super::*;

// ---------------------------------------------------------------------------
// maps (flatmap)

/// Canonical key order: term order, with exactness tiebreak so that keys
/// like 1 and 1.0 remain distinct (int sorts before float).
pub(crate) fn map_key_cmp(a: u64, b: u64) -> std::cmp::Ordering {
    if a == b {
        return std::cmp::Ordering::Equal;
    }
    // binary keys (params, headers, JSON maps) dominate lookups on the web
    // path: compare bytes directly — Erlang orders binaries by bytes, and
    // byte-equal binaries are exactly equal, so no rank/exactness passes
    if let (Some((pa, la)), Some((pb, lb))) = (bin_parts(a), bin_parts(b)) {
        let (x, y) = unsafe {
            (std::slice::from_raw_parts(pa, la), std::slice::from_raw_parts(pb, lb))
        };
        return x.cmp(y);
    }
    let c = mana_rt_compare(a, b);
    if c != 0 {
        return c.cmp(&0);
    }
    if a == b {
        return std::cmp::Ordering::Equal;
    }
    // compare == 0 with distinct bits: a binary's byte compare was already
    // exact — only numbers (1 vs 1.0), possibly nested in containers, need
    // the exactness tiebreak
    if a & TAG_MASK == TAG_BOXED
        && matches!(unsafe { *(a as *const u64) } & 0xff, KIND_BIN | KIND_SUBBIN)
    {
        return std::cmp::Ordering::Equal;
    }
    if mana_rt_eq_exact(a, b) == 1 {
        return std::cmp::Ordering::Equal;
    }
    // numerically equal but exact-distinct: small int first
    if a & TAG_MASK == TAG_SMALL {
        std::cmp::Ordering::Less
    } else {
        std::cmp::Ordering::Greater
    }
}

pub(crate) fn map_parts(m: u64) -> Option<(*mut u64, usize)> {
    if m & TAG_MASK != TAG_BOXED || m == 0 {
        return None;
    }
    let p = m as *mut u64;
    let header = unsafe { *p };
    if header & 0xff != KIND_MAP {
        return None;
    }
    Some((p, (header >> 8) as usize))
}

/// Find a key (exact match) via binary search; returns the pair index.
pub(crate) fn map_index(p: *const u64, n: usize, key: u64) -> Result<usize, usize> {
    let keys = unsafe { std::slice::from_raw_parts(p.add(1), n) };
    // Equal atoms are pointer-identical (linkonce_odr globals) and equal
    // smalls bit-identical, so for the small maps that dominate (struct
    // fields, changesets) a raw-u64 scan resolves the hit without any
    // generic compares. Misses (and boxed keys) fall to binary search,
    // which also supplies the insertion position for put.
    // Plug.Conn / Phoenix.Socket structs have 30-40 fields: a linear
    // identity scan over 64 words is still cheaper than ~6 generic
    // compares (atoms compare by TEXT in the generic path)
    if n <= 64 {
        if let Some(i) = keys.iter().position(|&k| k == key) {
            return Ok(i);
        }
    }
    keys.binary_search_by(|&k| map_key_cmp(k, key))
}

/// Normalize a freshly built map (unsorted pairs, not yet published):
/// sort by key, deduplicate (last write wins). Shrinks the header size on
/// dedupe; trailing words become unreachable garbage (worklist GC).
#[no_mangle]
pub extern "C" fn mana_rt_map_norm(m: u64) -> u64 {
    let Some((p, n)) = map_parts(m) else { return m };
    unsafe {
        let mut pairs: Vec<(u64, u64)> = (0..n).map(|i| (*p.add(1 + i), *p.add(1 + n + i))).collect();
        // stable sort keeps the LAST duplicate later in the run
        pairs.sort_by(|a, b| map_key_cmp(a.0, b.0));
        let mut out: Vec<(u64, u64)> = Vec::with_capacity(n);
        for pair in pairs {
            if let Some(last) = out.last_mut() {
                if map_key_cmp(last.0, pair.0) == std::cmp::Ordering::Equal {
                    *last = pair; // last wins
                    continue;
                }
            }
            out.push(pair);
        }
        let m2 = out.len();
        *p = ((m2 as u64) << 8) | KIND_MAP;
        for (i, (k, v)) in out.iter().enumerate() {
            *p.add(1 + i) = *k;
            *p.add(1 + m2 + i) = *v;
        }
    }
    m
}

/// Pattern-match lookup: value, or the exception sentinel for miss /
/// non-map. Non-allocating — safe inside match contexts.
#[no_mangle]
pub extern "C" fn mana_rt_map_pat_get(m: u64, key: u64) -> u64 {
    let Some((p, n)) = map_parts(m) else {
        return EXC_SENTINEL;
    };
    match map_index(p, n, key) {
        Ok(i) => unsafe { *p.add(1 + n + i) },
        Err(_) => EXC_SENTINEL,
    }
}

pub(crate) fn raise_map_err(ctx: &mut ProcCtx, tag_is_badmap: bool, culprit: u64) -> u64 {
    // {badmap, M} / {badkey, K} with class error
    let tag = if tag_is_badmap { "badmap" } else { "badkey" };
    // eternal pair (never moved; GC scans fields)
    let p = alloc_space(3);
    ctx.global.eternal.lock().push((p as usize, false));
    unsafe {
        *p = (2 << 8) | KIND_TUPLE;
        *p.add(1) = atom_by_name(tag);
        *p.add(2) = culprit;
    }
    ctx.exc_class = atom_error();
    ctx.exc_reason = p as u64;
    EXC_SENTINEL
}

/// maps:put/3 — returns a new map (insert or replace).
#[no_mangle]
pub extern "C" fn mana_rt_map_put(ctx: *mut ProcCtx, key: u64, val: u64, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, n)) = map_parts(m) else {
        return raise_map_err(ctx, true, m);
    };
    // root inputs across allocation
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, key, val, m];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let newp = alloc_nursery(ctx, 1 + 2 * (n + 1));
    ctx.roots_head = saved;
    let (key, val, m) = (fr[2], fr[3], fr[4]);
    let (p, n) = map_parts(m).unwrap();
    unsafe {
        match map_index(p, n, key) {
            Ok(i) => {
                std::ptr::copy_nonoverlapping(p, newp, 1 + 2 * n);
                *newp.add(1 + n + i) = val;
            }
            Err(pos) => {
                *newp = (((n + 1) as u64) << 8) | KIND_MAP;
                // keys with insertion at pos
                for i in 0..pos {
                    *newp.add(1 + i) = *p.add(1 + i);
                    *newp.add(1 + (n + 1) + i) = *p.add(1 + n + i);
                }
                *newp.add(1 + pos) = key;
                *newp.add(1 + (n + 1) + pos) = val;
                for i in pos..n {
                    *newp.add(1 + i + 1) = *p.add(1 + i);
                    *newp.add(1 + (n + 1) + i + 1) = *p.add(1 + n + i);
                }
            }
        }
    }
    newp as u64
}

/// maps:get/2 — badkey/badmap on miss.
#[no_mangle]
pub extern "C" fn mana_rt_map_get(ctx: *mut ProcCtx, key: u64, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((p, n)) = map_parts(m) else {
        return raise_map_err(ctx, true, m);
    };
    match map_index(p, n, key) {
        Ok(i) => unsafe { *p.add(1 + n + i) },
        Err(_) => raise_map_err(ctx, false, key),
    }
}

/// maps:remove/2.
#[no_mangle]
pub extern "C" fn mana_rt_map_remove(ctx: *mut ProcCtx, key: u64, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((p0, n)) = map_parts(m) else {
        return raise_map_err(ctx, true, m);
    };
    let Ok(idx) = map_index(p0, n, key) else {
        return m;
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, m];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let newp = alloc_nursery(ctx, 1 + 2 * (n - 1));
    ctx.roots_head = saved;
    let m = fr[2];
    let (p, n) = map_parts(m).unwrap();
    unsafe {
        *newp = (((n - 1) as u64) << 8) | KIND_MAP;
        let mut j = 0;
        for i in 0..n {
            if i == idx {
                continue;
            }
            *newp.add(1 + j) = *p.add(1 + i);
            *newp.add(1 + (n - 1) + j) = *p.add(1 + n + i);
            j += 1;
        }
    }
    newp as u64
}

/// maps:to_list/1 — [{K, V}] in key order.
#[no_mangle]
pub extern "C" fn mana_rt_map_to_list(ctx: *mut ProcCtx, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, n)) = map_parts(m) else {
        return raise_map_err(ctx, true, m);
    };
    if n == 0 {
        return NIL;
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, m];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    // 2 words per cons + 3 per {K,V} tuple
    let block = alloc_nursery(ctx, n * 5);
    ctx.roots_head = saved;
    let m = fr[2];
    let (p, n) = map_parts(m).unwrap();
    unsafe {
        for i in 0..n {
            let tup = block.add(5 * i);
            *tup = (2 << 8) | KIND_TUPLE;
            *tup.add(1) = *p.add(1 + i);
            *tup.add(2) = *p.add(1 + n + i);
            let cell = tup.add(3);
            *cell = tup as u64;
            *cell.add(1) = if i == n - 1 {
                NIL
            } else {
                block.add(5 * (i + 1) + 3) as u64 | TAG_CONS
            };
        }
    }
    unsafe { block.add(3) as u64 | TAG_CONS }
}

/// maps:from_list/1 — builds then normalizes.
#[no_mangle]
pub extern "C" fn mana_rt_map_from_list(ctx: *mut ProcCtx, list: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    // count and validate [{K,V}]
    let mut n = 0usize;
    let mut t = list;
    while t != NIL {
        if t & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (t & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK != TAG_BOXED || h == 0 {
            return raise_badarg(ctx);
        }
        let hh = unsafe { *(h as *const u64) };
        if hh & 0xff != KIND_TUPLE || (hh >> 8) != 2 {
            return raise_badarg(ctx);
        }
        n += 1;
        t = unsafe { *p.add(1) };
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, list];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let newp = alloc_nursery(ctx, 1 + 2 * n);
    ctx.roots_head = saved;
    let list = fr[2];
    unsafe {
        *newp = ((n as u64) << 8) | KIND_MAP;
        let mut t = list;
        let mut i = 0;
        while t != NIL {
            let p = (t & !TAG_MASK) as *const u64;
            let tup = *p as *const u64;
            *newp.add(1 + i) = *tup.add(1);
            *newp.add(1 + n + i) = *tup.add(2);
            i += 1;
            t = *p.add(1);
        }
    }
    mana_rt_map_norm(newp as u64)
}

/// `~{K := V | M}~` update: key must exist (Elixir `%{m | k: v}`).
#[no_mangle]
pub extern "C" fn mana_rt_map_update_exact(ctx: *mut ProcCtx, key: u64, val: u64, m: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    let Some((p, n)) = map_parts(m) else {
        return raise_map_err(ctxr, true, m);
    };
    let Ok(i) = map_index(p, n, key) else {
        return raise_map_err(ctxr, false, key);
    };
    // the key exists: copy the map once and patch the value slot (no
    // second key search, no insertion path) — this is `%{struct | f: v}`,
    // ~70 times per Phoenix request on Plug.Conn
    let saved = ctxr.roots_head;
    let mut fr = [0u64, 2, val, m];
    fr[0] = saved;
    ctxr.roots_head = fr.as_ptr() as u64;
    let newp = alloc_nursery(ctxr, 1 + 2 * n);
    ctxr.roots_head = saved;
    let (val, m) = (fr[2], fr[3]);
    let (p, _) = map_parts(m).unwrap();
    unsafe {
        std::ptr::copy_nonoverlapping(p, newp, 1 + 2 * n);
        *newp.add(1 + n + i) = val;
    }
    newp as u64
}

/// maps:is_key/2 → true/false atoms (badmap on non-map).
#[no_mangle]
pub extern "C" fn mana_rt_map_is_key(ctx: *mut ProcCtx, key: u64, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((p, n)) = map_parts(m) else {
        return raise_map_err(ctx, true, m);
    };
    if map_index(p, n, key).is_ok() {
        known().true_a
    } else {
        known().false_a
    }
}

/// maps:merge/2 — values from the second map win.
#[no_mangle]
pub extern "C" fn mana_rt_map_merge(ctx: *mut ProcCtx, m1: u64, m2: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, n1)) = map_parts(m1) else {
        return raise_map_err(ctx, true, m1);
    };
    let Some((_, n2)) = map_parts(m2) else {
        return raise_map_err(ctx, true, m2);
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, m1, m2];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let newp = alloc_nursery(ctx, 1 + 2 * (n1 + n2));
    ctx.roots_head = saved;
    let (m1, m2) = (fr[2], fr[3]);
    let (p1, n1) = map_parts(m1).unwrap();
    let (p2, n2) = map_parts(m2).unwrap();
    unsafe {
        // merge two sorted pair sequences; m2 wins ties
        let (mut i, mut j, mut o) = (0usize, 0usize, 0usize);
        let total = n1 + n2;
        let put = |newp: *mut u64, o: usize, k: u64, v: u64| {
            *newp.add(1 + o) = k;
            *newp.add(1 + total + o) = v;
        };
        while i < n1 && j < n2 {
            let (k1, k2) = (*p1.add(1 + i), *p2.add(1 + j));
            match map_key_cmp(k1, k2) {
                std::cmp::Ordering::Less => {
                    put(newp, o, k1, *p1.add(1 + n1 + i));
                    i += 1;
                }
                std::cmp::Ordering::Greater => {
                    put(newp, o, k2, *p2.add(1 + n2 + j));
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    put(newp, o, k2, *p2.add(1 + n2 + j));
                    i += 1;
                    j += 1;
                }
            }
            o += 1;
        }
        while i < n1 {
            put(newp, o, *p1.add(1 + i), *p1.add(1 + n1 + i));
            i += 1;
            o += 1;
        }
        while j < n2 {
            put(newp, o, *p2.add(1 + j), *p2.add(1 + n2 + j));
            j += 1;
            o += 1;
        }
        // compact values if o < total (ties merged): values were written at
        // stride `total`; rewrite them at stride `o`
        if o < total {
            for idx in 0..o {
                let v = *newp.add(1 + total + idx);
                *newp.add(1 + o + idx) = v;
            }
        }
        *newp = ((o as u64) << 8) | KIND_MAP;
    }
    newp as u64
}

/// maps:iterator/1 → {mana_miter, 0, Map}; maps:next/1 walks it in
/// canonical (sorted) key order, returning {K, V, NextIter} | none.
#[no_mangle]
pub extern "C" fn mana_rt_map_iterator(ctx: *mut ProcCtx, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if map_parts(m).is_none() {
        return raise_map_err(ctx, true, m);
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, m];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let t = alloc_nursery(ctx, 4);
    ctx.roots_head = saved;
    unsafe {
        *t = (3 << 8) | KIND_TUPLE;
        *t.add(1) = atom_intern(b"mana_miter");
        *t.add(2) = TAG_SMALL; // small 0
        *t.add(3) = fr[2];
    }
    t as u64
}

#[no_mangle]
pub extern "C" fn mana_rt_map_next(ctx: *mut ProcCtx, iter: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let ok = iter & TAG_MASK == TAG_BOXED
        && iter != 0
        && unsafe { *(iter as *const u64) } == (3 << 8) | KIND_TUPLE
        && unsafe { atom_bytes(*(iter as *const u64).add(1)) } == b"mana_miter";
    if !ok {
        return raise_badarg(ctx);
    }
    let (i, m) = unsafe {
        let p = iter as *const u64;
        ((*p.add(2) as i64 >> 3) as usize, *p.add(3))
    };
    let Some((_, n)) = map_parts(m) else {
        return raise_badarg(ctx);
    };
    if i >= n {
        return find_atom("none").expect("none atom");
    }
    // build the next iterator, then the result tuple, rooting the map
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, m, 0];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let ni = alloc_nursery(ctx, 4);
    unsafe {
        *ni = (3 << 8) | KIND_TUPLE;
        *ni.add(1) = atom_intern(b"mana_miter");
        *ni.add(2) = (((i + 1) as u64) << 3) | TAG_SMALL;
        *ni.add(3) = fr[2];
    }
    fr[3] = ni as u64;
    let t = alloc_nursery(ctx, 4);
    ctx.roots_head = saved;
    unsafe {
        let (p, n) = map_parts(fr[2]).unwrap();
        *t = (3 << 8) | KIND_TUPLE;
        *t.add(1) = *p.add(1 + i);
        *t.add(2) = *p.add(1 + n + i);
        *t.add(3) = fr[3];
    }
    t as u64
}

/// maps:keys/1 and maps:values/1 (`vals != 0`). Key order = canonical.
#[no_mangle]
pub extern "C" fn mana_rt_map_keys(ctx: *mut ProcCtx, m: u64, vals: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, n)) = map_parts(m) else {
        return raise_map_err(ctx, true, m);
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, m, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for i in (0..n).rev() {
        let cell = alloc_nursery(ctx, 2);
        let (p, _) = map_parts(fr[2]).unwrap();
        let item = unsafe {
            if vals != 0 {
                *p.add(1 + n + i)
            } else {
                *p.add(1 + i)
            }
        };
        unsafe {
            *cell = item;
            *cell.add(1) = fr[3];
        }
        fr[3] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[3]
}

/// maps:take/2 → {Value, MapWithoutKey} | error.
#[no_mangle]
pub extern "C" fn mana_rt_map_take(ctx: *mut ProcCtx, key: u64, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if map_parts(m).is_none() {
        return raise_map_err(ctx, true, m);
    }
    let v = mana_rt_map_pat_get(m, key);
    if v == EXC_SENTINEL {
        return atom_error();
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, key, m, v];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let removed = mana_rt_map_remove(ctx as *mut ProcCtx, fr[2], fr[3]);
    if removed == EXC_SENTINEL {
        ctx.roots_head = saved;
        return EXC_SENTINEL;
    }
    fr[3] = removed;
    let t = alloc_nursery(ctx, 3);
    ctx.roots_head = saved;
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = fr[4];
        *t.add(2) = fr[3];
    }
    t as u64
}

/// maps:update_with/3 — apply Fun to the existing value (badkey on miss).
#[no_mangle]
pub extern "C" fn mana_rt_maps_update_with(ctx: *mut ProcCtx, key: u64, fun: u64, m: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    let Some((p, n)) = map_parts(m) else {
        return raise_map_err(ctxr, true, m);
    };
    if map_index(p, n, key).is_err() {
        return raise_map_err(ctxr, false, key);
    }
    let old = mana_rt_map_pat_get(m, key);
    let saved = ctxr.roots_head;
    let mut fr = [0u64, 2, key, m];
    fr[0] = saved;
    ctxr.roots_head = fr.as_ptr() as u64;
    let c1 = alloc_nursery(ctxr, 2);
    unsafe {
        *c1 = old;
        *c1.add(1) = NIL;
    }
    let newv = mana_rt_apply_fun(ctx, fun, c1 as u64 | TAG_CONS);
    if newv == EXC_SENTINEL {
        ctxr.roots_head = saved;
        return EXC_SENTINEL;
    }
    let key2 = fr[2];
    let m2 = fr[3];
    ctxr.roots_head = saved;
    mana_rt_map_put(ctx, key2, newv, m2)
}

/// maps:update_with/4 — like /3 but inserts Init when the key is absent.
#[no_mangle]
pub extern "C" fn mana_rt_maps_update_with4(
    ctx: *mut ProcCtx,
    key: u64,
    fun: u64,
    init: u64,
    m: u64,
) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    let Some((p, n)) = map_parts(m) else {
        return raise_map_err(ctxr, true, m);
    };
    if map_index(p, n, key).is_err() {
        return mana_rt_map_put(ctx, key, init, m);
    }
    mana_rt_maps_update_with(ctx, key, fun, m)
}

/// maps:with/2 / maps:without/2 — key-list subset / complement.
#[no_mangle]
pub extern "C" fn mana_rt_maps_with(ctx: *mut ProcCtx, keys: u64, m: u64, keep: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    let Some((_, _)) = map_parts(m) else {
        return raise_map_err(ctxr, true, m);
    };
    // collect wanted keys (immediates or heap terms; compared by eq_exact)
    let mut want: Vec<u64> = Vec::new();
    let mut cur = keys;
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        want.push(unsafe { *p });
        cur = unsafe { *p.add(1) };
    }
    let saved = ctxr.roots_head;
    let mut fr = [0u64, 2, m, NIL];
    fr[0] = saved;
    ctxr.roots_head = fr.as_ptr() as u64;
    // build result by folding put over matching pairs (m stays rooted)
    let mut acc = {
        let e = alloc_nursery(ctxr, 1);
        unsafe { *e = KIND_MAP }; // empty map header
        e as u64
    };
    fr[3] = acc;
    let n = map_parts(fr[2]).unwrap().1;
    for i in 0..n {
        let (p, _) = map_parts(fr[2]).unwrap();
        let (k, v) = unsafe { (*p.add(1 + i), *p.add(1 + n + i)) };
        let matched = want.iter().any(|&w| mana_rt_eq_exact(w, k) == 1);
        let include = if keep != 0 { matched } else { !matched };
        if include {
            let r = mana_rt_map_put(ctx, k, v, fr[3]);
            if r == EXC_SENTINEL {
                ctxr.roots_head = saved;
                return EXC_SENTINEL;
            }
            fr[3] = r;
        }
    }
    acc = fr[3];
    ctxr.roots_head = saved;
    acc
}

/// maps:foreach/2 — Fun(K, V) per pair, returns ok.
#[no_mangle]
pub extern "C" fn mana_rt_maps_foreach(ctx: *mut ProcCtx, fun: u64, m: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    if map_parts(m).is_none() {
        return raise_map_err(ctxr, true, m);
    }
    let saved = ctxr.roots_head;
    let mut fr = [0u64, 2, fun, m];
    fr[0] = saved;
    ctxr.roots_head = fr.as_ptr() as u64;
    let n = map_parts(fr[3]).unwrap().1;
    for i in 0..n {
        let (p, _) = map_parts(fr[3]).unwrap();
        let (k, v) = unsafe { (*p.add(1 + i), *p.add(1 + n + i)) };
        let mut fr2 = [0u64, 2, k, v];
        fr2[0] = ctxr.roots_head;
        ctxr.roots_head = fr2.as_ptr() as u64;
        let c2 = alloc_nursery(ctxr, 2);
        unsafe {
            *c2 = fr2[3];
            *c2.add(1) = NIL;
        }
        let c1 = alloc_nursery(ctxr, 2);
        unsafe {
            *c1 = fr2[2];
            *c1.add(1) = c2 as u64 | TAG_CONS;
        }
        ctxr.roots_head = fr2[0];
        let r = mana_rt_apply_fun(ctx, fr[2], c1 as u64 | TAG_CONS);
        if r == EXC_SENTINEL {
            ctxr.roots_head = saved;
            return EXC_SENTINEL;
        }
    }
    ctxr.roots_head = saved;
    atom_intern(b"ok")
}

/// maps:merge_with/3 — merge with a conflict fun (calls back into compiled
/// code; everything rooted around the callbacks).
#[no_mangle]
pub extern "C" fn mana_rt_maps_merge_with(ctx: *mut ProcCtx, fun: u64, m1: u64, m2: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if map_parts(m1).is_none() {
        return raise_map_err(ctx, true, m1);
    }
    if map_parts(m2).is_none() {
        return raise_map_err(ctx, true, m2);
    }
    // acc starts as m1; for each pair in m2: put or resolve via fun
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, fun, m1, m2];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let n2 = map_parts(fr[4]).unwrap().1;
    for i in 0..n2 {
        let (p2, _) = map_parts(fr[4]).unwrap();
        let (k, v2) = unsafe { (*p2.add(1 + i), *p2.add(1 + n2 + i)) };
        let existing = mana_rt_map_pat_get(fr[3], k);
        let newv = if existing == EXC_SENTINEL {
            v2
        } else {
            // fun(K, V1, V2) — build the args list rooted
            let mut fr2 = [0u64, 3, k, existing, v2];
            fr2[0] = ctx.roots_head;
            ctx.roots_head = fr2.as_ptr() as u64;
            let c3 = alloc_nursery(ctx, 2);
            unsafe {
                *c3 = fr2[4];
                *c3.add(1) = NIL;
            }
            let c2 = alloc_nursery(ctx, 2);
            unsafe {
                *c2 = fr2[3];
                *c2.add(1) = c3 as u64 | TAG_CONS;
            }
            let c1 = alloc_nursery(ctx, 2);
            unsafe {
                *c1 = fr2[2];
                *c1.add(1) = c2 as u64 | TAG_CONS;
            }
            ctx.roots_head = fr2[0];
            let r = mana_rt_apply_fun(ctx as *mut ProcCtx, fr[2], c1 as u64 | TAG_CONS);
            if r == EXC_SENTINEL {
                ctx.roots_head = saved;
                return EXC_SENTINEL;
            }
            r
        };
        // re-read the key (allocs may have moved m2)
        let (p2, _) = map_parts(fr[4]).unwrap();
        let k2 = unsafe { *p2.add(1 + i) };
        let merged = mana_rt_map_put(ctx as *mut ProcCtx, k2, newv, fr[3]);
        if merged == EXC_SENTINEL {
            ctx.roots_head = saved;
            return EXC_SENTINEL;
        }
        fr[3] = merged;
    }
    ctx.roots_head = saved;
    fr[3]
}

/// maps:fold/3 — calls back into compiled code (the fun), so the map, fun,
/// and accumulator are rooted and reloaded around every callback.
#[no_mangle]
pub extern "C" fn mana_rt_maps_fold(ctx: *mut ProcCtx, fun: u64, acc0: u64, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, n)) = map_parts(m) else {
        return raise_map_err(ctx, true, m);
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, fun, acc0, m];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for i in 0..n {
        let (p, _) = map_parts(fr[4]).unwrap();
        let (k, v) = unsafe { (*p.add(1 + i), *p.add(1 + n + i)) };
        // args list for apply_fun: build 3 cells rooted via fr (k/v read
        // fresh from the rooted map, acc in fr[3])
        let c3 = alloc_nursery(ctx, 2);
        unsafe {
            *c3 = fr[3];
            *c3.add(1) = NIL;
        }
        // re-read k/v: the alloc above may have moved the map
        let (p, _) = map_parts(fr[4]).unwrap();
        let v2 = unsafe { *p.add(1 + n + i) };
        let c2 = alloc_nursery(ctx, 2);
        unsafe {
            *c2 = v2;
            *c2.add(1) = c3 as u64 | TAG_CONS;
        }
        let (p, _) = map_parts(fr[4]).unwrap();
        let k2 = unsafe { *p.add(1 + i) };
        let c1 = alloc_nursery(ctx, 2);
        unsafe {
            *c1 = k2;
            *c1.add(1) = c2 as u64 | TAG_CONS;
        }
        let _ = (k, v);
        let args = c1 as u64 | TAG_CONS;
        let r = mana_rt_apply_fun(ctx, fr[2], args);
        if r == EXC_SENTINEL {
            ctx.roots_head = saved;
            return EXC_SENTINEL;
        }
        fr[3] = r;
    }
    ctx.roots_head = saved;
    fr[3]
}
