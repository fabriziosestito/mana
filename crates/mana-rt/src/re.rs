use super::*;

// ---------------------------------------------------------------------------
// :re — regular expressions on the `regex` crate. `:re.version/0` returns
// "mana" so Elixir's Regex always recompiles from source at runtime
// (sigil literals carry opaque BEAM-compiled PCRE blobs we can't read).
// Known divergences: no backreferences/lookaround (crate limitation),
// firstline/ungreedy options ignored.

pub(crate) struct ReTable {
    pub(crate) by_key: std::collections::HashMap<String, usize>,
    // Arc, not Regex: a `Regex` clone gets a fresh lazy-DFA cache pool, so
    // cloning out of the table per call re-determinized the DFA on every
    // run (~190K instructions for a trivial pattern). Sharing one Regex
    // value keeps its cache warm across calls and threads.
    pub(crate) regexes: Vec<std::sync::Arc<regex::Regex>>,
}

pub(crate) static RE_TABLE: std::sync::Mutex<Option<ReTable>> = std::sync::Mutex::new(None);

#[derive(Default, Clone, Copy)]
pub(crate) struct ReFlags {
    pub(crate) caseless: bool,
    pub(crate) multiline: bool,
    pub(crate) dotall: bool,
    pub(crate) extended: bool,
}

pub(crate) struct ReRunOpts {
    pub(crate) global: bool,
    pub(crate) offset: usize,
    pub(crate) capture_spec: u64,   // term: atom all/first/none/all_but_first/all_names or list
    pub(crate) capture_type: u8,    // 0 index, 1 binary, 2 list
}

pub(crate) fn term_to_source(t: u64) -> Option<Vec<u8>> {
    if bin_parts(t).is_some() {
        return Some(bin_bytes(t).to_vec());
    }
    // charlist
    let mut out = Vec::new();
    let mut cur = t;
    loop {
        if cur == NIL {
            return Some(out);
        }
        if cur & TAG_MASK != TAG_CONS {
            return None;
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK != TAG_SMALL {
            return None;
        }
        let cp = h as i64 >> 3;
        let c = u32::try_from(cp).ok().and_then(char::from_u32)?;
        let mut buf = [0u8; 4];
        out.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
        cur = unsafe { *p.add(1) };
    }
}

/// Intern (or fetch) a compiled regex; Err(msg) on bad pattern.
pub(crate) fn re_intern(source: &str, fl: ReFlags) -> Result<usize, String> {
    let key = format!(
        "{}{}{}{}\0{}",
        fl.caseless as u8, fl.multiline as u8, fl.dotall as u8, fl.extended as u8, source
    );
    let mut guard = RE_TABLE.lock().unwrap();
    let tab = guard.get_or_insert_with(|| ReTable {
        by_key: Default::default(),
        regexes: Vec::new(),
    });
    if let Some(&i) = tab.by_key.get(&key) {
        return Ok(i);
    }
    let re = regex::RegexBuilder::new(source)
        .case_insensitive(fl.caseless)
        .multi_line(fl.multiline)
        .dot_matches_new_line(fl.dotall)
        .ignore_whitespace(fl.extended)
        .build()
        .map_err(|e| e.to_string())?;
    tab.regexes.push(std::sync::Arc::new(re));
    let idx = tab.regexes.len() - 1;
    tab.by_key.insert(key, idx);
    Ok(idx)
}

/// Options list → (compile flags, run opts). Unknown atoms are ignored
/// (BEAM accepts many run options that don't apply here).
pub(crate) fn parse_re_opts(opts: u64) -> Result<(ReFlags, ReRunOpts), ()> {
    let mut fl = ReFlags::default();
    let mut run = ReRunOpts {
        global: false,
        offset: 0,
        capture_spec: 0,
        capture_type: 0,
    };
    let mut cur = opts;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return Err(());
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let opt = unsafe { *p };
        if opt & TAG_MASK == TAG_ATOM {
            match atom_bytes(opt) {
                b"caseless" => fl.caseless = true,
                b"multiline" => fl.multiline = true,
                b"dotall" => fl.dotall = true,
                b"extended" => fl.extended = true,
                b"global" => run.global = true,
                // unicode/ucp are the crate default; the rest are accepted
                // and ignored (firstline, ungreedy, anchored variations...)
                _ => {}
            }
        } else if opt & TAG_MASK == TAG_BOXED && opt != 0 {
            let hp = opt as *const u64;
            let h = unsafe { *hp };
            if h & 0xff == KIND_TUPLE {
                let arity = h >> 8;
                let tag = unsafe { *hp.add(1) };
                match (atom_bytes(tag), arity) {
                    (b"capture", 2) => {
                        run.capture_spec = unsafe { *hp.add(2) };
                        run.capture_type = 0;
                    }
                    (b"capture", 3) => {
                        run.capture_spec = unsafe { *hp.add(2) };
                        let ty = unsafe { *hp.add(3) };
                        run.capture_type = match atom_bytes(ty) {
                            b"binary" => 1,
                            b"list" => 2,
                            _ => 0,
                        };
                    }
                    (b"offset", 2) => {
                        let off = unsafe { *hp.add(2) };
                        if off & TAG_MASK != TAG_SMALL {
                            return Err(());
                        }
                        run.offset = (off as i64 >> 3).max(0) as usize;
                    }
                    (b"newline", _) => {}
                    _ => {}
                }
            }
        }
        cur = unsafe { *p.add(1) };
    }
    Ok((fl, run))
}

/// The subject pattern argument of run/compile: an interned handle
/// {mana_re, Idx} or a source binary/charlist compiled with `fl`.
pub(crate) fn re_resolve(pat: u64, fl: ReFlags) -> Result<usize, String> {
    if pat & TAG_MASK == TAG_BOXED && pat != 0 {
        let hp = pat as *const u64;
        let h = unsafe { *hp };
        if h & 0xff == KIND_TUPLE && h >> 8 == 2 {
            let tag = unsafe { *hp.add(1) };
            if tag & TAG_MASK == TAG_ATOM && atom_bytes(tag) == b"mana_re" {
                let idx = unsafe { *hp.add(2) };
                return Ok((idx as i64 >> 3) as usize);
            }
        }
    }
    let src = term_to_source(pat).ok_or_else(|| "bad pattern".to_string())?;
    let s = String::from_utf8(src).map_err(|e| e.to_string())?;
    re_intern(&s, fl)
}

/// One capture group as a term per capture_type. Unmatched: {-1,0} / <<>> / [].
pub(crate) fn cap_term(ctx: &mut ProcCtx, hay: &[u8], g: Option<(usize, usize)>, ty: u8) -> u64 {
    match ty {
        0 => {
            let (s, l) = match g {
                Some((a, b)) => (a as i64, (b - a) as i64),
                None => (-1, 0),
            };
            let t = alloc_nursery(ctx, 3);
            unsafe {
                *t = (2 << 8) | KIND_TUPLE;
                *t.add(1) = ((s << 3) as u64) | TAG_SMALL;
                *t.add(2) = ((l << 3) as u64) | TAG_SMALL;
            }
            t as u64
        }
        1 => match g {
            Some((a, b)) => bytes_to_new_bin(ctx, &hay[a..b]),
            None => bytes_to_new_bin(ctx, b""),
        },
        _ => match g {
            Some((a, b)) => bytes_to_charlist(ctx, &hay[a..b]),
            None => NIL,
        },
    }
}

/// :re.run/3. Returns {match, Caps} | {match, [Caps]} (global) | match |
/// nomatch, or raises badarg on bad patterns/options.
#[no_mangle]
pub extern "C" fn mana_rt_re_run(ctx: *mut ProcCtx, subject: u64, pat: u64, opts: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some(hay) = term_to_source(subject) else {
        return raise_badarg(ctx);
    };
    let Ok((fl, run)) = parse_re_opts(opts) else {
        return raise_badarg(ctx);
    };
    let idx = match re_resolve(pat, fl) {
        Ok(i) => i,
        Err(_) => return raise_badarg(ctx),
    };
    let re = {
        let guard = RE_TABLE.lock().unwrap();
        guard.as_ref().unwrap().regexes[idx].clone()
    };
    let hay_str = match std::str::from_utf8(&hay) {
        Ok(s) => s,
        Err(_) => return raise_badarg(ctx),
    };
    let none_a = || find_atom("none").unwrap_or(NIL);
    let _ = none_a;
    // collect matches
    let mut all: Vec<Vec<Option<(usize, usize)>>> = Vec::new();
    let mut pos = run.offset.min(hay_str.len());
    loop {
        let Some(caps) = re.captures_at(hay_str, pos) else {
            break;
        };
        let whole = caps.get(0).unwrap();
        let groups: Vec<Option<(usize, usize)>> = (0..caps.len())
            .map(|i| caps.get(i).map(|m| (m.start(), m.end())))
            .collect();
        all.push(groups);
        if !run.global {
            break;
        }
        pos = if whole.end() > whole.start() {
            whole.end()
        } else {
            // empty match: advance one char
            match hay_str[whole.end()..].chars().next() {
                Some(c) => whole.end() + c.len_utf8(),
                None => break,
            }
        };
    }
    if all.is_empty() {
        return find_atom("nomatch").expect("nomatch atom");
    }
    // capture :none → bare 'match'
    if run.capture_spec & TAG_MASK == TAG_ATOM && atom_bytes(run.capture_spec) == b"none" {
        return find_atom("match").expect("match atom");
    }
    // select groups per spec
    let names: Vec<Option<String>> = re
        .capture_names()
        .map(|n| n.map(|s| s.to_string()))
        .collect();
    let select = |groups: &Vec<Option<(usize, usize)>>| -> Vec<Option<(usize, usize)>> {
        let spec = run.capture_spec;
        if spec & TAG_MASK == TAG_ATOM {
            match atom_bytes(spec) {
                b"first" => vec![groups[0]],
                b"all_but_first" => groups[1..].to_vec(),
                b"all_names" => {
                    let mut named: Vec<(String, Option<(usize, usize)>)> = names
                        .iter()
                        .enumerate()
                        .filter_map(|(i, n)| n.clone().map(|n| (n, groups.get(i).copied().flatten())))
                        .collect();
                    named.sort_by(|a, b| a.0.cmp(&b.0));
                    named.into_iter().map(|(_, g)| g).collect()
                }
                _ => groups.clone(), // all (and default)
            }
        } else if spec == 0 {
            groups.clone()
        } else {
            // list of names (binaries/atoms) or indices
            let mut out = Vec::new();
            let mut cur = spec;
            while cur != NIL && cur & TAG_MASK == TAG_CONS {
                let p = (cur & !TAG_MASK) as *const u64;
                let item = unsafe { *p };
                let g = if item & TAG_MASK == TAG_SMALL {
                    groups.get((item as i64 >> 3) as usize).copied().flatten()
                } else {
                    let want: Vec<u8> = if item & TAG_MASK == TAG_ATOM {
                        atom_bytes(item).to_vec()
                    } else {
                        bin_bytes(item).to_vec()
                    };
                    names
                        .iter()
                        .position(|n| n.as_deref().map(|s| s.as_bytes()) == Some(&want[..]))
                        .and_then(|i| groups.get(i).copied().flatten())
                };
                out.push(g);
                cur = unsafe { *p.add(1) };
            }
            out
        }
    };
    // build result list(s) back-to-front with rooting
    let build_caps = |ctx: &mut ProcCtx, groups: &Vec<Option<(usize, usize)>>| -> u64 {
        let sel = select(groups);
        let saved = ctx.roots_head;
        let mut fr = [0u64, 2, NIL, 0];
        fr[0] = saved;
        ctx.roots_head = fr.as_ptr() as u64;
        for g in sel.iter().rev() {
            fr[3] = cap_term(ctx, &hay, *g, run.capture_type);
            let cell = alloc_nursery(ctx, 2);
            unsafe {
                *cell = fr[3];
                *cell.add(1) = fr[2];
            }
            fr[2] = cell as u64 | TAG_CONS;
            fr[3] = 0;
        }
        ctx.roots_head = saved;
        fr[2]
    };
    let payload = if run.global {
        let lists: Vec<u64> = Vec::new();
        let _ = lists;
        let saved = ctx.roots_head;
        let mut fr = [0u64, 2, NIL, 0];
        fr[0] = saved;
        ctx.roots_head = fr.as_ptr() as u64;
        for groups in all.iter().rev() {
            fr[3] = build_caps(ctx, groups);
            let cell = alloc_nursery(ctx, 2);
            unsafe {
                *cell = fr[3];
                *cell.add(1) = fr[2];
            }
            fr[2] = cell as u64 | TAG_CONS;
            fr[3] = 0;
        }
        ctx.roots_head = saved;
        fr[2]
    } else {
        build_caps(ctx, &all[0])
    };
    // {match, Payload}
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, payload];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let t = alloc_nursery(ctx, 3);
    ctx.roots_head = saved;
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = find_atom("match").expect("match atom");
        *t.add(2) = fr[2];
    }
    t as u64
}

/// :re.compile/2 → {ok, {mana_re, Idx}} | {error, {Reason, 0}}.
#[no_mangle]
pub extern "C" fn mana_rt_re_compile(ctx: *mut ProcCtx, pat: u64, opts: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Ok((fl, _)) = parse_re_opts(opts) else {
        return raise_badarg(ctx);
    };
    let Some(srcb) = term_to_source(pat) else {
        return raise_badarg(ctx);
    };
    let Ok(srcs) = String::from_utf8(srcb) else {
        return raise_badarg(ctx);
    };
    match re_intern(&srcs, fl) {
        Ok(idx) => {
            // {ok, {mana_re, Idx}}
            let inner = alloc_nursery(ctx, 3);
            unsafe {
                *inner = (2 << 8) | KIND_TUPLE;
                *inner.add(1) = atom_intern(b"mana_re");
                *inner.add(2) = ((idx as u64) << 3) | TAG_SMALL;
            }
            let saved = ctx.roots_head;
            let mut fr = [0u64, 1, inner as u64];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            let t = alloc_nursery(ctx, 3);
            ctx.roots_head = saved;
            unsafe {
                *t = (2 << 8) | KIND_TUPLE;
                *t.add(1) = known().ok;
                *t.add(2) = fr[2];
            }
            t as u64
        }
        Err(msg) => {
            // {error, {ErrString(charlist), 0}}
            let saved = ctx.roots_head;
            let mut fr = [0u64, 2, 0, 0];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            fr[2] = bytes_to_charlist(ctx, msg.as_bytes());
            let inner = alloc_nursery(ctx, 3);
            unsafe {
                *inner = (2 << 8) | KIND_TUPLE;
                *inner.add(1) = fr[2];
                *inner.add(2) = TAG_SMALL; // 0
            }
            fr[3] = inner as u64;
            let t = alloc_nursery(ctx, 3);
            ctx.roots_head = saved;
            unsafe {
                *t = (2 << 8) | KIND_TUPLE;
                *t.add(1) = atom_error();
                *t.add(2) = fr[3];
            }
            t as u64
        }
    }
}

/// :re.inspect/2 (:namelist) → {namelist, [<<name>>]} sorted.
#[no_mangle]
pub extern "C" fn mana_rt_re_inspect(ctx: *mut ProcCtx, pat: u64, _what: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let idx = match re_resolve(pat, ReFlags::default()) {
        Ok(i) => i,
        Err(_) => return raise_badarg(ctx),
    };
    let names: Vec<String> = {
        let guard = RE_TABLE.lock().unwrap();
        guard.as_ref().unwrap().regexes[idx]
            .capture_names()
            .flatten()
            .map(|s| s.to_string())
            .collect()
    };
    let mut sorted = names;
    sorted.sort();
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, 0];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for n in sorted.iter().rev() {
        fr[3] = bytes_to_new_bin(ctx, n.as_bytes());
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = fr[3];
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
        fr[3] = 0;
    }
    let t = alloc_nursery(ctx, 3);
    ctx.roots_head = saved;
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = atom_intern(b"namelist");
        *t.add(2) = fr[2];
    }
    t as u64
}
