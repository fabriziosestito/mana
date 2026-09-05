use super::*;

// ---------------------------------------------------------------------------
// persistent_term (native cut)

/// Deep copy a term into self-contained eternal storage: every pointer in
/// the copy targets another eternal block, so the GC never needs to see it.
/// persistent_term values are immortal by design (puts are rare).
pub(crate) fn eternal_deep_copy(t: u64) -> u64 {
    match t & TAG_MASK {
        TAG_CONS => {
            let p = (t & !TAG_MASK) as *const u64;
            let (h, tl) = unsafe { (*p, *p.add(1)) };
            let np = alloc_space(2);
            unsafe {
                *np = eternal_deep_copy(h);
                *np.add(1) = eternal_deep_copy(tl);
            }
            np as u64 | TAG_CONS
        }
        TAG_BOXED if t != 0 => {
            let p = t as *const u64;
            let header = unsafe { *p };
            // flatten views up front: an eternal reason must not pin a heap
            // parent (and eternal storage never gets GC-forwarded)
            if header & 0xff == KIND_SUBBIN {
                let bytes = bin_bytes(t);
                let bwords = 1 + (bytes.len() + 7) / 8;
                let bp = alloc_space(bwords);
                unsafe {
                    *bp = ((bytes.len() as u64) << 8) | KIND_BIN;
                    if bytes.len() % 8 != 0 {
                        *bp.add(bwords - 1) = 0;
                    }
                    std::ptr::copy_nonoverlapping(
                        bytes.as_ptr(),
                        bp.add(1) as *mut u8,
                        bytes.len(),
                    );
                }
                return bp as u64;
            }
            let words = 1 + payload_words(header);
            let np = alloc_space(words);
            unsafe {
                *np = header;
                match header & 0xff {
                    KIND_FLOAT | KIND_BIN | KIND_BIGNUM => {
                        std::ptr::copy_nonoverlapping(p.add(1), np.add(1), words - 1);
                    }
                    KIND_FUN => {
                        *np.add(1) = *p.add(1); // code ptr
                        for i in 2..words {
                            *np.add(i) = eternal_deep_copy(*p.add(i));
                        }
                    }
                    _ => {
                        for i in 1..words {
                            *np.add(i) = eternal_deep_copy(*p.add(i));
                        }
                    }
                }
            }
            np as u64
        }
        _ => t, // immediates and atoms (static) pass through
    }
}

pub(crate) static PERSISTENT_TERMS: std::sync::Mutex<Option<std::collections::HashMap<u64, u64>>> =
    std::sync::Mutex::new(None);

/// persistent_term:put/2 — keys compared exactly (we require immediate or
/// atom keys, which covers real usage; compound keys are TODO).
#[no_mangle]
pub extern "C" fn mana_rt_pt_put(_ctx: *mut ProcCtx, key: u64, val: u64) -> u64 {
    let key = eternal_deep_copy(key);
    let val = eternal_deep_copy(val);
    let mut guard = PERSISTENT_TERMS.lock().unwrap();
    let map = guard.get_or_insert_with(Default::default);
    // exact-compare lookup for compound keys
    let existing = map.keys().copied().find(|&k| mana_rt_eq_exact(k, key) == 1);
    match existing {
        Some(k) => {
            map.insert(k, val);
        }
        None => {
            map.insert(key, val);
        }
    }
    known().ok
}

/// persistent_term:get/1,2 — sentinel-free: get/1 raises badarg on miss
/// (BEAM's behavior), get/2 returns the default.
#[no_mangle]
pub extern "C" fn mana_rt_pt_get(ctx: *mut ProcCtx, key: u64, default: u64, has_default: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let guard = PERSISTENT_TERMS.lock().unwrap();
    let found = guard
        .as_ref()
        .and_then(|m| m.keys().copied().find(|&k| mana_rt_eq_exact(k, key) == 1).map(|k| m[&k]));
    match found {
        Some(v) => v,
        None if has_default != 0 => default,
        None => raise_badarg(ctx),
    }
}

// ---------------------------------------------------------------------------
// ets + application env (native cuts): one global store of eternal deep
// copies. Enough for elixir_config-style tables — TODO(ets): match specs,
// ordered tables, delete_all, GC of replaced values.

pub(crate) type KvStore = std::sync::Mutex<Option<Vec<(u64, u64, u64)>>>; // (tab, key, tuple)

pub(crate) static ETS_STORE: KvStore = std::sync::Mutex::new(None);

pub(crate) fn kv_find(rows: &[(u64, u64, u64)], tab: u64, key: u64) -> Option<usize> {
    rows.iter()
        .position(|&(t, k, _)| t == tab && mana_rt_eq_exact(k, key) == 1)
}

/// ets:insert/2 with a tuple or list of tuples (keypos 1); insert_new when
/// `new != 0`.
#[no_mangle]
pub extern "C" fn mana_rt_ets_insert(ctx: *mut ProcCtx, tab: u64, obj: u64, new: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let known = known();
    let mut objs = Vec::new();
    if obj & TAG_MASK == TAG_CONS || obj == NIL {
        let mut cur = obj;
        while cur != NIL {
            if cur & TAG_MASK != TAG_CONS {
                return raise_badarg(ctx);
            }
            let p = (cur & !TAG_MASK) as *const u64;
            unsafe {
                objs.push(*p);
                cur = *p.add(1);
            }
        }
    } else {
        objs.push(obj);
    }
    let kind = ets_kind(tab);
    let mut guard = ETS_STORE.lock().unwrap();
    let rows = guard.get_or_insert_with(Vec::new);
    for o in objs {
        let ok = o & TAG_MASK == TAG_BOXED
            && o != 0
            && unsafe { *(o as *const u64) } & 0xff == KIND_TUPLE
            && unsafe { *(o as *const u64) } >> 8 >= 1;
        if !ok {
            return raise_badarg(ctx);
        }
        let key = unsafe { *(o as *const u64).add(1) };
        match kind {
            ETS_SET => match kv_find(rows, tab, key) {
                Some(i) => {
                    if new != 0 {
                        return known.false_a;
                    }
                    rows[i].2 = eternal_deep_copy(o);
                }
                None => {
                    let copy = eternal_deep_copy(o);
                    let ckey = unsafe { *(copy as *const u64).add(1) };
                    rows.push((tab, ckey, copy));
                }
            },
            _ => {
                // bag dedups exact-equal objects; duplicate_bag always
                // appends. Rows keep insertion order.
                let dup = kind == ETS_BAG
                    && rows.iter().any(|&(t, k, v)| {
                        t == tab
                            && mana_rt_eq_exact(k, key) == 1
                            && mana_rt_eq_exact(v, o) == 1
                    });
                if !dup {
                    let copy = eternal_deep_copy(o);
                    let ckey = unsafe { *(copy as *const u64).add(1) };
                    rows.push((tab, ckey, copy));
                }
            }
        }
    }
    known.true_a
}

/// ets:lookup/2 → list of all stored tuples for the key, in insertion
/// order (bags may hold several — eternal, safe to share).
#[no_mangle]
pub extern "C" fn mana_rt_ets_lookup(ctx: *mut ProcCtx, tab: u64, key: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let found: Vec<u64> = {
        let guard = ETS_STORE.lock().unwrap();
        guard
            .as_ref()
            .map(|rows| {
                rows.iter()
                    .filter(|&&(t, k, _)| t == tab && mana_rt_eq_exact(k, key) == 1)
                    .map(|&(_, _, v)| v)
                    .collect()
            })
            .unwrap_or_default()
    };
    // rows are eternal — build the list newest-cons-last (reverse iter)
    let mut out = NIL;
    for &tuple in found.iter().rev() {
        let mut fr = [ctx.roots_head, 1, out];
        ctx.roots_head = fr.as_ptr() as u64;
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = tuple;
            *cell.add(1) = fr[2];
        }
        ctx.roots_head = fr[0];
        out = cell as u64 | TAG_CONS;
        let _ = &mut fr;
    }
    out
}

/// ets:delete/2 (by key) — removes every row for the key (bag semantics).
#[no_mangle]
pub extern "C" fn mana_rt_ets_delete(_ctx: *mut ProcCtx, tab: u64, key: u64) -> u64 {
    let mut guard = ETS_STORE.lock().unwrap();
    if let Some(rows) = guard.as_mut() {
        rows.retain(|&(t, k, _)| !(t == tab && mana_rt_eq_exact(k, key) == 1));
    }
    known().true_a
}

/// Restricted ets match pattern: literals (eq_exact), '_' wildcard,
/// '$N' captures. Captures append to `caps` tagged with N.
pub(crate) fn ets_match_term(pat: u64, val: u64, caps: &mut Vec<(i64, u64)>) -> bool {
    if pat & TAG_MASK == TAG_ATOM {
        let b = atom_bytes(pat);
        if b == b"_" {
            return true;
        }
        if b.len() >= 2 && b[0] == b'$' && b[1..].iter().all(|c| c.is_ascii_digit()) {
            let n: i64 = std::str::from_utf8(&b[1..]).unwrap().parse().unwrap_or(0);
            caps.push((n, val));
            return true;
        }
        return pat == val;
    }
    if pat & TAG_MASK == TAG_BOXED && pat != 0 && val & TAG_MASK == TAG_BOXED && val != 0 {
        unsafe {
            let (pp, vp) = (pat as *const u64, val as *const u64);
            if *pp & 0xff == KIND_TUPLE && *vp & 0xff == KIND_TUPLE {
                let n = (*pp >> 8) as usize;
                if (*vp >> 8) as usize != n {
                    return false;
                }
                for i in 1..=n {
                    if !ets_match_term(*pp.add(i), *vp.add(i), caps) {
                        return false;
                    }
                }
                return true;
            }
        }
    }
    if pat & TAG_MASK == TAG_CONS && val & TAG_MASK == TAG_CONS {
        unsafe {
            let (pp, vp) = ((pat & !TAG_MASK) as *const u64, (val & !TAG_MASK) as *const u64);
            return ets_match_term(*pp, *vp, caps)
                && ets_match_term(*pp.add(1), *vp.add(1), caps);
        }
    }
    mana_rt_eq_exact(pat, val) == 1
}

/// ets:match/2 — list of capture lists ('$N' order), insertion order.
#[no_mangle]
pub extern "C" fn mana_rt_ets_match(ctx: *mut ProcCtx, tab: u64, pattern: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let rows: Vec<u64> = {
        let guard = ETS_STORE.lock().unwrap();
        guard
            .as_ref()
            .map(|rows| {
                rows.iter()
                    .filter(|(t, _, _)| mana_rt_eq_exact(*t, tab) == 1)
                    .map(|&(_, _, v)| v)
                    .collect()
            })
            .unwrap_or_default()
    };
    // rows are eternal (deep-copied at insert) — safe across allocs
    let mut matches: Vec<Vec<u64>> = Vec::new();
    for row in rows {
        let mut caps: Vec<(i64, u64)> = Vec::new();
        if ets_match_term(pattern, row, &mut caps) {
            caps.sort_by_key(|&(n, _)| n);
            matches.push(caps.into_iter().map(|(_, v)| v).collect());
        }
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for caps in matches.iter().rev() {
        let mut inner = NIL;
        for &v in caps.iter().rev() {
            let cell = alloc_nursery(ctx, 2);
            unsafe {
                *cell = v;
                *cell.add(1) = inner;
            }
            inner = cell as u64 | TAG_CONS;
        }
        fr[3] = inner;
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = fr[3];
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
    }
    let out = fr[2];
    ctx.roots_head = saved;
    out
}

/// Known-table registry: (eternal name term, kind). Kind drives insert
/// dedup and the shape of lookup_element. Unregistered tables (the app-env
/// tag) default to Set.
pub(crate) static ETS_TABLES: std::sync::Mutex<Vec<(u64, u8)>> = std::sync::Mutex::new(Vec::new());

pub(crate) const ETS_SET: u8 = 0;

pub(crate) const ETS_BAG: u8 = 1;

pub(crate) const ETS_DUP_BAG: u8 = 2;

/// Kind of a table by name term; Set for anything not registered.
pub(crate) fn ets_kind(tab: u64) -> u8 {
    let tabs = ETS_TABLES.lock().unwrap();
    tabs.iter()
        .find(|&&(t, _)| mana_rt_eq_exact(t, tab) == 1)
        .map(|&(_, k)| k)
        .unwrap_or(ETS_SET)
}

/// ets:new/2 — registers the (named) table and records its kind from the
/// options (`bag` / `duplicate_bag` / `ordered_set` → Set + TODO(ets); all
/// other options ignored).
#[no_mangle]
pub extern "C" fn mana_rt_ets_new(_ctx: *mut ProcCtx, name: u64, opts: u64) -> u64 {
    let mut kind = ETS_SET;
    let mut cur = opts;
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        let opt = unsafe { *p };
        cur = unsafe { *p.add(1) };
        if opt & TAG_MASK == TAG_ATOM {
            match atom_bytes(opt) {
                b"bag" => kind = ETS_BAG,
                b"duplicate_bag" => kind = ETS_DUP_BAG,
                _ => {}
            }
        }
    }
    let mut tabs = ETS_TABLES.lock().unwrap();
    match tabs.iter().position(|&(t, _)| mana_rt_eq_exact(t, name) == 1) {
        Some(i) => tabs[i].1 = kind,
        None => tabs.push((eternal_deep_copy(name), kind)),
    }
    name
}

/// Seed the `elixir_config` ets table with the URI scheme → default-port
/// entries that `elixir:start/2` inserts on BEAM (`{{uri, <<"http">>}, 80}`
/// …). The closed world never runs the :elixir application boot, so
/// URI.default_port/1 (→ elixir_config:get({uri, Scheme})) would return nil
/// and any HTTP request whose Host header omits a port would then crash in
/// the response path. Called once from the generated main.
#[no_mangle]
pub extern "C" fn mana_rt_seed_uri_defaults(ctx: *mut ProcCtx) {
    let ctx = unsafe { &mut *ctx };
    let tab = atom_intern(b"elixir_config");
    let uri = atom_intern(b"uri");
    let defaults: &[(&[u8], i64)] = &[
        (b"ftp", 21),
        (b"sftp", 22),
        (b"tftp", 69),
        (b"http", 80),
        (b"https", 443),
        (b"ldap", 389),
        (b"ws", 80),
        (b"wss", 443),
    ];
    for &(scheme, port) in defaults {
        let sbin = bytes_to_new_bin(ctx, scheme);
        // root sbin across the two tuple allocs
        let mut fr = [ctx.roots_head, 1, sbin];
        ctx.roots_head = fr.as_ptr() as u64;
        let key = alloc_nursery(ctx, 3);
        unsafe {
            *key = (2 << 8) | KIND_TUPLE;
            *key.add(1) = uri;
            *key.add(2) = fr[2];
        }
        fr[2] = key as u64;
        let row = alloc_nursery(ctx, 3);
        unsafe {
            *row = (2 << 8) | KIND_TUPLE;
            *row.add(1) = fr[2];
            *row.add(2) = ((port << 3) as u64) | TAG_SMALL;
        }
        ctx.roots_head = fr[0];
        let _ = &mut fr;
        mana_rt_ets_insert(ctx, tab, row as u64, 0);
    }
}

#[no_mangle]
pub extern "C" fn mana_rt_ets_info(_ctx: *mut ProcCtx, tab: u64) -> u64 {
    let tabs = ETS_TABLES.lock().unwrap();
    if tabs.iter().any(|&(t, _)| mana_rt_eq_exact(t, tab) == 1) {
        NIL
    } else {
        known().undefined
    }
}

/// ets:match_delete/2 — drop matching rows.
#[no_mangle]
pub extern "C" fn mana_rt_ets_match_delete(_ctx: *mut ProcCtx, tab: u64, pattern: u64) -> u64 {
    let mut guard = ETS_STORE.lock().unwrap();
    if let Some(rows) = guard.as_mut() {
        rows.retain(|&(t, _, v)| {
            if mana_rt_eq_exact(t, tab) != 1 {
                return true;
            }
            let mut caps = Vec::new();
            !ets_match_term(pattern, v, &mut caps)
        });
    }
    known().true_a
}

/// ets:member/2 — true if any object has the key.
#[no_mangle]
pub extern "C" fn mana_rt_ets_member(_ctx: *mut ProcCtx, tab: u64, key: u64) -> u64 {
    let k = known();
    let guard = ETS_STORE.lock().unwrap();
    let hit = guard
        .as_ref()
        .map(|rows| {
            rows.iter()
                .any(|&(t, rk, _)| t == tab && mana_rt_eq_exact(rk, key) == 1)
        })
        .unwrap_or(false);
    if hit {
        k.true_a
    } else {
        k.false_a
    }
}

/// ets:delete_object/2 — remove every row whose stored object equals the
/// given one (Registry's per-key unsubscribe cleanup).
#[no_mangle]
pub extern "C" fn mana_rt_ets_delete_object(ctx: *mut ProcCtx, tab: u64, obj: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let ok = obj & TAG_MASK == TAG_BOXED
        && obj != 0
        && unsafe { *(obj as *const u64) } & 0xff == KIND_TUPLE
        && unsafe { *(obj as *const u64) } >> 8 >= 1;
    if !ok {
        return raise_badarg(ctx);
    }
    let key = unsafe { *(obj as *const u64).add(1) };
    let mut guard = ETS_STORE.lock().unwrap();
    if let Some(rows) = guard.as_mut() {
        rows.retain(|&(t, k, v)| {
            !(t == tab && mana_rt_eq_exact(k, key) == 1 && mana_rt_eq_exact(v, obj) == 1)
        });
    }
    known().true_a
}

/// ets:take/2 — return all objects for the key (as ets:lookup would) and
/// remove them.
#[no_mangle]
pub extern "C" fn mana_rt_ets_take(ctx: *mut ProcCtx, tab: u64, key: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let found: Vec<u64> = {
        let mut guard = ETS_STORE.lock().unwrap();
        match guard.as_mut() {
            Some(rows) => {
                let hits = rows
                    .iter()
                    .filter(|&&(t, k, _)| t == tab && mana_rt_eq_exact(k, key) == 1)
                    .map(|&(_, _, v)| v)
                    .collect();
                rows.retain(|&(t, k, _)| !(t == tab && mana_rt_eq_exact(k, key) == 1));
                hits
            }
            None => Vec::new(),
        }
    };
    let mut out = NIL;
    for &tuple in found.iter().rev() {
        let mut fr = [ctx.roots_head, 1, out];
        ctx.roots_head = fr.as_ptr() as u64;
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = tuple;
            *cell.add(1) = fr[2];
        }
        ctx.roots_head = fr[0];
        out = cell as u64 | TAG_CONS;
        let _ = &mut fr;
    }
    out
}

/// Count rows of `tab` matching a restricted select head (guards must be
/// empty). Shared by select_count and select_delete.
pub(crate) fn ets_select_matches(spec: u64, tab: u64, out_heads: &mut Vec<u64>) -> Result<usize, ()> {
    // parse [{Head, [], _Body}] — heads only, guards must be []
    let mut heads: Vec<u64> = Vec::new();
    let mut cur = spec;
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        let clause = unsafe { *p };
        cur = unsafe { *p.add(1) };
        if clause & TAG_MASK != TAG_BOXED || clause == 0 {
            return Err(());
        }
        unsafe {
            let cp = clause as *const u64;
            if *cp != (3 << 8) | KIND_TUPLE {
                return Err(());
            }
            if *cp.add(2) != NIL {
                return Err(()); // TODO(ets): guards
            }
            heads.push(*cp.add(1));
        }
    }
    let guard = ETS_STORE.lock().unwrap();
    let mut count = 0usize;
    if let Some(rows) = guard.as_ref() {
        for &(t, _, v) in rows {
            if t != tab {
                continue;
            }
            for &h in &heads {
                let mut caps = Vec::new();
                if ets_match_term(h, v, &mut caps) {
                    count += 1;
                    out_heads.push(v);
                    break;
                }
            }
        }
    }
    Ok(count)
}

/// ets:select_count/2 — number of objects matching the spec (empty guards).
#[no_mangle]
pub extern "C" fn mana_rt_ets_select_count(ctx: *mut ProcCtx, tab: u64, spec: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut hits = Vec::new();
    match ets_select_matches(spec, tab, &mut hits) {
        Ok(n) => ((n as u64) << 3) | TAG_SMALL,
        Err(()) => raise_badarg(ctx),
    }
}

/// ets:select_delete/2 — delete objects matching the spec, return the count.
#[no_mangle]
pub extern "C" fn mana_rt_ets_select_delete(ctx: *mut ProcCtx, tab: u64, spec: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut hits: Vec<u64> = Vec::new();
    let n = match ets_select_matches(spec, tab, &mut hits) {
        Ok(n) => n,
        Err(()) => return raise_badarg(ctx),
    };
    let mut guard = ETS_STORE.lock().unwrap();
    if let Some(rows) = guard.as_mut() {
        rows.retain(|&(t, _, v)| {
            !(t == tab && hits.iter().any(|&h| mana_rt_eq_exact(h, v) == 1))
        });
    }
    ((n as u64) << 3) | TAG_SMALL
}

/// Match-spec BODY term substitution: '$N' → capture, '$_' → object,
/// '$$' → all captures, {X} (arity-1 tuple) → tuple-escape of X.
pub(crate) fn ets_subst_body(ctx: &mut ProcCtx, body: u64, caps: &[(i64, u64)], obj: u64) -> u64 {
    if body & TAG_MASK == TAG_ATOM {
        let b = atom_bytes(body);
        if b == b"$_" {
            return obj;
        }
        if b == b"$$" {
            let mut list = NIL;
            let mut sorted: Vec<&(i64, u64)> = caps.iter().collect();
            sorted.sort_by_key(|&&(n, _)| n);
            for &&(_, v) in sorted.iter().rev() {
                let cell = alloc_nursery(ctx, 2);
                unsafe {
                    *cell = v;
                    *cell.add(1) = list;
                }
                list = cell as u64 | TAG_CONS;
            }
            return list;
        }
        if b.len() >= 2 && b[0] == b'$' && b[1..].iter().all(|c| c.is_ascii_digit()) {
            let n: i64 = std::str::from_utf8(&b[1..]).unwrap().parse().unwrap_or(0);
            if let Some(&(_, v)) = caps.iter().find(|&&(cn, _)| cn == n) {
                return v;
            }
        }
        return body;
    }
    if body & TAG_MASK == TAG_BOXED && body != 0 {
        unsafe {
            let p = body as *const u64;
            if *p & 0xff == KIND_TUPLE && (*p >> 8) == 1 {
                // {X}: tuple escape — X built literally (with substitution)
                let inner = *p.add(1);
                if inner & TAG_MASK == TAG_BOXED
                    && inner != 0
                    && *(inner as *const u64) & 0xff == KIND_TUPLE
                {
                    let ip = inner as *const u64;
                    let n = (*ip >> 8) as usize;
                    // substitute fields first (rooted), then build
                    let saved = ctx.roots_head;
                    let mut fields: Vec<u64> = Vec::with_capacity(n);
                    let mut fr = vec![0u64; 2 + n];
                    fr[0] = saved;
                    fr[1] = n as u64;
                    ctx.roots_head = fr.as_ptr() as u64;
                    for i in 0..n {
                        let ip = inner as *const u64; // re-derive (may move? inner unrooted!)
                        let fv = ets_subst_body(ctx, *ip.add(1 + i), caps, obj);
                        fr[2 + i] = fv;
                        fields.push(0);
                    }
                    let t = alloc_nursery(ctx, 1 + n);
                    unsafe {
                        *t = ((n as u64) << 8) | KIND_TUPLE;
                        for i in 0..n {
                            *t.add(1 + i) = fr[2 + i];
                        }
                    }
                    let _ = fields;
                    ctx.roots_head = saved;
                    return t as u64;
                }
            }
        }
    }
    body
}

/// ets:select/2 — restricted match specs [{Head, [], [Body]}] (no guards).
#[no_mangle]
pub extern "C" fn mana_rt_ets_select(ctx: *mut ProcCtx, tab: u64, spec: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    // parse the spec list: [{Head, Guards, [Body]}]
    let mut clauses: Vec<(u64, u64)> = Vec::new(); // (head, body)
    let mut cur = spec;
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        let clause = unsafe { *p };
        cur = unsafe { *p.add(1) };
        if clause & TAG_MASK != TAG_BOXED || clause == 0 {
            return raise_badarg(ctx);
        }
        unsafe {
            let cp = clause as *const u64;
            if *cp != (3 << 8) | KIND_TUPLE {
                return raise_badarg(ctx);
            }
            let guards = *cp.add(2);
            if guards != NIL {
                return raise_badarg(ctx); // TODO(ets): guards
            }
            let body_list = *cp.add(3);
            if body_list & TAG_MASK != TAG_CONS {
                return raise_badarg(ctx);
            }
            let bp = (body_list & !TAG_MASK) as *const u64;
            clauses.push((*cp.add(1), *bp));
        }
    }
    let rows: Vec<u64> = {
        let guard = ETS_STORE.lock().unwrap();
        guard
            .as_ref()
            .map(|rows| {
                rows.iter()
                    .filter(|(t, _, _)| mana_rt_eq_exact(*t, tab) == 1)
                    .map(|&(_, _, v)| v)
                    .collect()
            })
            .unwrap_or_default()
    };
    // results built under a root frame; rows/spec terms are eternal or
    // caller-live respectively (spec is not used after parsing... heads
    // and bodies are caller terms — no alloc happens between uses except
    // inside subst which re-reads from the parsed immediates)
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let mut results: Vec<u64> = Vec::new();
    for row in rows {
        for &(head, body) in &clauses {
            let mut caps = Vec::new();
            if ets_match_term(head, row, &mut caps) {
                caps.sort_by_key(|&(n, _)| n);
                results.push(ets_subst_body(ctx, body, &caps, row));
                break;
            }
        }
        // keep already-built results rooted as a growing list
        while let Some(r) = results.pop() {
            fr[3] = r;
            let cell = alloc_nursery(ctx, 2);
            unsafe {
                *cell = fr[3];
                *cell.add(1) = fr[2];
            }
            fr[2] = cell as u64 | TAG_CONS;
        }
    }
    // reverse into final order
    let mut out = NIL;
    fr[3] = NIL;
    let mut cur = fr[2];
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        let v = unsafe { *p };
        cur = unsafe { *p.add(1) };
        fr[2] = cur; // remaining source stays rooted
        let mut fr3 = [0u64, 2, v, out];
        fr3[0] = ctx.roots_head;
        ctx.roots_head = fr3.as_ptr() as u64;
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = fr3[2];
            *cell.add(1) = fr3[3];
        }
        ctx.roots_head = fr3[0];
        out = cell as u64 | TAG_CONS;
        fr[3] = out;
    }
    ctx.roots_head = saved;
    out
}

/// ets:lookup_element/3 — badarg on missing table/key (Bandit.Clock's
/// date_header rescues the resulting ArgumentError to compute a fallback).
/// For bag / duplicate_bag tables the result is the LIST of the Pos-th
/// elements across every object with the key, in insertion order (this is
/// what Phoenix.Registry.dispatch consumes).
#[no_mangle]
pub extern "C" fn mana_rt_ets_lookup_element(
    ctx: *mut ProcCtx,
    tab: u64,
    key: u64,
    pos: u64,
) -> u64 {
    match ets_lookup_element_impl(ctx, tab, key, pos) {
        Ok(v) => v,
        Err(true) => raise_badarg(unsafe { &mut *ctx }),
        // empty on a /3 call is badarg
        Err(false) => raise_badarg(unsafe { &mut *ctx }),
    }
}

/// ets:lookup_element/4 — like /3 but returns Default when the key is
/// absent instead of raising (pg:get_members/2 relies on this).
#[no_mangle]
pub extern "C" fn mana_rt_ets_lookup_element4(
    ctx: *mut ProcCtx,
    tab: u64,
    key: u64,
    pos: u64,
    default: u64,
) -> u64 {
    match ets_lookup_element_impl(ctx, tab, key, pos) {
        Ok(v) => v,
        Err(true) => raise_badarg(unsafe { &mut *ctx }),
        Err(false) => default, // key absent → default
    }
}

/// Shared body: Ok(term) on success, Err(true) on a genuine badarg (bad
/// pos or malformed tuple), Err(false) when the key has no rows.
pub(crate) fn ets_lookup_element_impl(ctx: *mut ProcCtx, tab: u64, key: u64, pos: u64) -> Result<u64, bool> {
    let ctx = unsafe { &mut *ctx };
    if pos & TAG_MASK != TAG_SMALL || (pos as i64 >> 3) < 1 {
        return Err(true);
    }
    let n = (pos as i64 >> 3) as usize;
    let found: Vec<u64> = {
        let guard = ETS_STORE.lock().unwrap();
        guard
            .as_ref()
            .map(|rows| {
                rows.iter()
                    .filter(|&&(t, k, _)| t == tab && mana_rt_eq_exact(k, key) == 1)
                    .map(|&(_, _, v)| v)
                    .collect()
            })
            .unwrap_or_default()
    };
    if found.is_empty() {
        return Err(false);
    }
    // element at position n of each stored tuple (all eternal)
    let mut elems: Vec<u64> = Vec::with_capacity(found.len());
    for tuple in found {
        unsafe {
            let p = tuple as *const u64;
            if tuple & TAG_MASK != TAG_BOXED || *p & 0xff != KIND_TUPLE || n > (*p >> 8) as usize {
                return Err(true);
            }
            elems.push(*p.add(n));
        }
    }
    if ets_kind(tab) == ETS_SET {
        return Ok(elems[0]);
    }
    // bag: return the list of elements, insertion order
    let mut out = NIL;
    for &e in elems.iter().rev() {
        let mut fr = [ctx.roots_head, 1, out];
        ctx.roots_head = fr.as_ptr() as u64;
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = e;
            *cell.add(1) = fr[2];
        }
        ctx.roots_head = fr[0];
        out = cell as u64 | TAG_CONS;
        let _ = &mut fr;
    }
    Ok(out)
}

/// application env — same store under a reserved table tag (0b111 is never
/// a valid term word for a table name).
pub(crate) const APP_ENV_TAB: u64 = 0b111;

#[no_mangle]
pub extern "C" fn mana_rt_app_set_env(ctx: *mut ProcCtx, app: u64, key: u64, val: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, app, key, val];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let kp = alloc_nursery(ctx, 3);
    unsafe {
        *kp = (2 << 8) | KIND_TUPLE;
        *kp.add(1) = fr[2];
        *kp.add(2) = fr[3];
    }
    fr[2] = kp as u64; // reuse slot: composite {App, Key} key
    let op = alloc_nursery(ctx, 3);
    unsafe {
        *op = (2 << 8) | KIND_TUPLE;
        *op.add(1) = fr[2];
        *op.add(2) = fr[4];
    }
    ctx.roots_head = saved;
    mana_rt_ets_insert(ctx, APP_ENV_TAB, op as u64, 0)
}

/// get_env: `miss` is returned on absence (codegen passes 'undefined' or
/// the default); `wrap_ok != 0` wraps hits as {ok, V}.
#[no_mangle]
pub extern "C" fn mana_rt_app_get_env(
    ctx: *mut ProcCtx,
    app: u64,
    key: u64,
    miss: u64,
    wrap_ok: u64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let guard = ETS_STORE.lock().unwrap();
    let found = guard.as_ref().and_then(|rows| {
        rows.iter()
            .find(|&&(t, k, _)| {
                t == APP_ENV_TAB && {
                    let p = k as *const u64;
                    unsafe {
                        mana_rt_eq_exact(*p.add(1), app) == 1
                            && mana_rt_eq_exact(*p.add(2), key) == 1
                    }
                }
            })
            .map(|&(_, _, tuple)| unsafe { *(tuple as *const u64).add(2) })
    });
    drop(guard);
    match found {
        Some(v) if wrap_ok != 0 => {
            // v is eternal — no rooting needed around this alloc
            let p = alloc_nursery(ctx, 3);
            unsafe {
                *p = (2 << 8) | KIND_TUPLE;
                *p.add(1) = known().ok;
                *p.add(2) = v;
            }
            p as u64
        }
        Some(v) => v,
        None => miss,
    }
}
