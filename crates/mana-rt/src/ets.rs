//! Native persistent_term, ets, and application env. One global store holds
//! eternal deep copies of every stored term. An eternal term never points
//! into a process heap, so the GC does not scan it. This is enough for
//! elixir_config-style tables. TODO(ets): complete match specs, ordered
//! tables, delete_all, GC of replaced values.

use super::*;

// persistent_term

/// Deep copy a term into eternal storage. Every pointer in the copy targets
/// another eternal block. The GC never scans eternal storage.
/// persistent_term values live forever by design. Puts are rare.
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
            // Flatten sub-binary views first. An eternal copy must not pin a
            // heap parent, and the GC never forwards eternal storage.
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
                        *np.add(1) = *p.add(1); // code pointer, not a term
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
        _ => t, // immediates and static atoms pass through
    }
}

pub(crate) static PERSISTENT_TERMS: std::sync::Mutex<Option<std::collections::HashMap<u64, u64>>> =
    std::sync::Mutex::new(None);

/// persistent_term:put/2. Keys compare exactly, so compound keys work. The
/// store is a scan, not a hash table.
#[no_mangle]
pub extern "C" fn mana_rt_pt_put(_ctx: *mut ProcCtx, key: u64, val: u64) -> u64 {
    let key = eternal_deep_copy(key);
    let val = eternal_deep_copy(val);
    let mut guard = PERSISTENT_TERMS.lock().unwrap();
    let map = guard.get_or_insert_with(Default::default);
    // Exact-compare scan, not a hash lookup, so compound keys match.
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

/// persistent_term:get/1,2. On a miss, get/1 raises badarg, as BEAM does.
/// get/2 returns the default. No sentinel value is used.
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

// ets + application env

pub(crate) type KvStore = std::sync::Mutex<Option<Vec<(u64, u64, u64)>>>; // (tab, key, tuple)

pub(crate) static ETS_STORE: KvStore = std::sync::Mutex::new(None);

pub(crate) fn kv_find(rows: &[(u64, u64, u64)], tab: u64, key: u64) -> Option<usize> {
    rows.iter()
        .position(|&(t, k, _)| t == tab && mana_rt_eq_exact(k, key) == 1)
}

/// ets:insert/2 with a tuple or a list of tuples. The key position is 1.
/// If `new != 0`, the call acts as insert_new.
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
                // A bag skips exact-equal duplicate objects. A duplicate_bag
                // always appends. Rows keep insertion order.
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

/// ets:lookup/2 returns the list of all stored tuples for the key, in
/// insertion order. A bag can hold several. The tuples are eternal, so the
/// list shares them.
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
    // The rows are eternal and need no rooting. Reverse iteration keeps
    // insertion order in the list.
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

/// ets:delete/2 by key. Removes every row for the key, as a bag requires.
#[no_mangle]
pub extern "C" fn mana_rt_ets_delete(_ctx: *mut ProcCtx, tab: u64, key: u64) -> u64 {
    let mut guard = ETS_STORE.lock().unwrap();
    if let Some(rows) = guard.as_mut() {
        rows.retain(|&(t, k, _)| !(t == tab && mana_rt_eq_exact(k, key) == 1));
    }
    known().true_a
}

/// Restricted ets match pattern. Literals compare with eq_exact. '_' is the
/// wildcard. '$N' captures the value. Each capture appends to `caps` with its N.
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

/// ets:match/2 returns a list of capture lists in '$N' order. The rows are in
/// insertion order.
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
    // The rows are eternal (deep copies made at insert). They survive
    // allocations without rooting.
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

/// Known-table registry: (eternal name term, kind). The kind controls insert
/// dedup and the shape of the lookup_element result. A table that is not
/// registered, for example the app-env tag, defaults to Set.
pub(crate) static ETS_TABLES: std::sync::Mutex<Vec<(u64, u8)>> = std::sync::Mutex::new(Vec::new());

pub(crate) const ETS_SET: u8 = 0;

pub(crate) const ETS_BAG: u8 = 1;

pub(crate) const ETS_DUP_BAG: u8 = 2;

/// Kind of a table by name term. Returns Set for a table that is not
/// registered.
pub(crate) fn ets_kind(tab: u64) -> u8 {
    let tabs = ETS_TABLES.lock().unwrap();
    tabs.iter()
        .find(|&&(t, _)| mana_rt_eq_exact(t, tab) == 1)
        .map(|&(_, k)| k)
        .unwrap_or(ETS_SET)
}

/// ets:new/2 registers the named table and records its kind from the options.
/// `bag` and `duplicate_bag` set the kind. `ordered_set` maps to Set.
/// TODO(ets): ordered tables. The function ignores all other options.
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

/// Seed the `elixir_config` ets table with the URI scheme to default-port
/// entries that `elixir:start/2` inserts on BEAM, for example
/// `{{uri, <<"http">>}, 80}`. The closed world never runs the :elixir
/// application boot. Without this seed, URI.default_port/1 (which reads
/// elixir_config:get({uri, Scheme})) returns nil. Then any HTTP request whose
/// Host header omits a port crashes in the response path. The generated main
/// calls this function once.
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
        // Root sbin across the two tuple allocations.
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

/// ets:match_delete/2 removes every row that matches the pattern.
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

/// ets:member/2 returns true if any object has the key.
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

/// ets:delete_object/2 removes every row whose stored object equals the given
/// one. Registry uses this for its per-key unsubscribe cleanup.
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

/// ets:take/2 returns all objects for the key, as ets:lookup does, and
/// removes them.
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

/// Count the rows of `tab` that match a restricted select head. The guards
/// must be empty. select_count and select_delete share this function.
pub(crate) fn ets_select_matches(spec: u64, tab: u64, out_heads: &mut Vec<u64>) -> Result<usize, ()> {
    // Parse [{Head, [], _Body}]. The function keeps only the heads. The
    // guards must be [].
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

/// ets:select_count/2 returns the number of objects that match the spec. The
/// guards must be empty.
#[no_mangle]
pub extern "C" fn mana_rt_ets_select_count(ctx: *mut ProcCtx, tab: u64, spec: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut hits = Vec::new();
    match ets_select_matches(spec, tab, &mut hits) {
        Ok(n) => ((n as u64) << 3) | TAG_SMALL,
        Err(()) => raise_badarg(ctx),
    }
}

/// ets:select_delete/2 removes the objects that match the spec and returns the
/// count.
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

/// Match-spec body term substitution. '$N' becomes the capture. '$_' becomes
/// the object. '$$' becomes the list of all captures. {X}, an arity-1 tuple,
/// is the tuple escape of X.
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
                // {X} is a tuple escape. The result is X itself, with
                // substitution in its fields.
                let inner = *p.add(1);
                if inner & TAG_MASK == TAG_BOXED
                    && inner != 0
                    && *(inner as *const u64) & 0xff == KIND_TUPLE
                {
                    let ip = inner as *const u64;
                    let n = (*ip >> 8) as usize;
                    // Substitute the fields first, under a root frame. Then
                    // build the tuple.
                    let saved = ctx.roots_head;
                    let mut fields: Vec<u64> = Vec::with_capacity(n);
                    let mut fr = vec![0u64; 2 + n];
                    fr[0] = saved;
                    fr[1] = n as u64;
                    ctx.roots_head = fr.as_ptr() as u64;
                    for i in 0..n {
                        let ip = inner as *const u64; // Re-derived pointer. `inner` is not rooted, so a GC can move it.
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

/// ets:select/2 with restricted match specs [{Head, [], [Body]}]. The
/// function does not support guards.
#[no_mangle]
pub extern "C" fn mana_rt_ets_select(ctx: *mut ProcCtx, tab: u64, spec: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    // The spec list has the shape [{Head, Guards, [Body]}].
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
    // The code builds the results under a root frame. The rows are eternal.
    // The heads and bodies are caller terms and are not rooted. No allocation
    // happens between their uses, except inside ets_subst_body, which
    // re-reads from the parsed values.
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
        // Cons each built result onto the rooted list, so it survives later
        // allocations.
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
    // Reverse the rooted list into the final order.
    let mut out = NIL;
    fr[3] = NIL;
    let mut cur = fr[2];
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        let v = unsafe { *p };
        cur = unsafe { *p.add(1) };
        fr[2] = cur; // the rest of the source list stays rooted
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

/// ets:lookup_element/3 raises badarg on a missing table or key. The
/// date_header function in Bandit.Clock rescues that ArgumentError to compute
/// a fallback. For bag and duplicate_bag tables, the result is the LIST of the
/// Pos-th elements across every object with the key, in insertion order.
/// Phoenix.Registry.dispatch consumes this list.
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
        // No rows on a /3 call is also badarg.
        Err(false) => raise_badarg(unsafe { &mut *ctx }),
    }
}

/// ets:lookup_element/4 is like /3, but returns Default when the key is
/// absent instead of a raise. pg:get_members/2 depends on this.
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
        Err(false) => default,
    }
}

/// Shared body. Returns Ok(term) on success. Returns Err(true) on a real
/// badarg (bad pos or malformed tuple). Returns Err(false) when the key has no
/// rows.
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
    // Take the element at position n of each stored tuple. All tuples are
    // eternal.
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
    // For a bag, return the list of elements in insertion order.
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

/// Application env uses the same store under a reserved table tag. 0b111 is
/// never a valid term word for a table name.
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
    fr[2] = kp as u64; // reuse the slot for the composite {App, Key} key
    let op = alloc_nursery(ctx, 3);
    unsafe {
        *op = (2 << 8) | KIND_TUPLE;
        *op.add(1) = fr[2];
        *op.add(2) = fr[4];
    }
    ctx.roots_head = saved;
    mana_rt_ets_insert(ctx, APP_ENV_TAB, op as u64, 0)
}

/// get_env returns `miss` when the key is absent. Codegen passes 'undefined'
/// or the default as `miss`. If `wrap_ok != 0`, the function wraps a hit as
/// {ok, V}.
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
            // v is eternal, so this allocation needs no rooting.
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
