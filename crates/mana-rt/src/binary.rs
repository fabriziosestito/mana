use super::*;

// ---------------------------------------------------------------------------
// binaries (byte-aligned; sub-byte bitstrings are TODO(bitstring))

pub(crate) fn bin_parts(t: u64) -> Option<(*const u8, usize)> {
    if t & TAG_MASK != TAG_BOXED || t == 0 {
        return None;
    }
    let p = t as *const u64;
    let header = unsafe { *p };
    match header & 0xff {
        KIND_BIN => Some((unsafe { p.add(1) } as *const u8, (header >> 8) as usize)),
        // view: recompute from the parent TERM every call — the parent
        // moves under GC, so the data pointer must never be cached
        KIND_SUBBIN => {
            let parent = unsafe { *p.add(1) };
            let off = unsafe { *p.add(2) } as usize;
            debug_assert!(
                parent & TAG_MASK == TAG_BOXED
                    && unsafe { *(parent as *const u64) } & 0xff == KIND_BIN,
                "sub-binary parent must be a root KIND_BIN"
            );
            let pp = parent as *const u64;
            Some((
                unsafe { (pp.add(1) as *const u8).add(off) },
                (header >> 8) as usize,
            ))
        }
        _ => None,
    }
}

pub(crate) fn bin_bytes(t: u64) -> &'static [u8] {
    match bin_parts(t) {
        Some((p, n)) => unsafe { std::slice::from_raw_parts(p, n) },
        None => &[],
    }
}

/// Allocate an uninitialized binary of `bytes` in the nursery. Padding in
/// the last data word is zeroed so word-granular copies stay deterministic.
/// Caller must have rooted every live term (may GC).
pub(crate) fn alloc_bin(ctx: &mut ProcCtx, bytes: usize) -> *mut u64 {
    let words = 1 + (bytes + 7) / 8;
    let p = alloc_nursery(ctx, words);
    unsafe {
        *p = ((bytes as u64) << 8) | KIND_BIN;
        if bytes % 8 != 0 {
            // zero the final data word's padding (never the header)
            *p.add(words - 1) = 0;
        }
    }
    p
}

/// Codegen entry: allocate a zero-padded binary; construction writers fill
/// it in. All live terms must be rooted by the caller (may GC).
#[no_mangle]
pub extern "C" fn mana_rt_bin_alloc(ctx: *mut ProcCtx, nbytes: u64) -> u64 {
    alloc_bin(unsafe { &mut *ctx }, nbytes as usize) as u64
}

/// Raise-path construction: eternal (malloc) binary, registered so majors
/// keep it alive; never moves, so no rooting needed.
#[no_mangle]
pub extern "C" fn mana_rt_bin_alloc_eternal(ctx: *mut ProcCtx, nbytes: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let bytes = nbytes as usize;
    let words = 1 + (bytes + 7) / 8;
    let p = alloc_space(words);
    ctx.global.eternal.lock().push((p as usize, false));
    unsafe {
        *p = ((bytes as u64) << 8) | KIND_BIN;
        if words > 1 {
            *p.add(words - 1) = 0;
        }
    }
    p as u64
}

/// Pattern preflight: is `t` a binary of exactly `n` bytes (`at_least` = 0)
/// or at least `n` bytes (`at_least` = 1)?
#[no_mangle]
pub extern "C" fn mana_rt_bin_len_check(t: u64, n: u64, at_least: u64) -> u64 {
    match bin_parts(t) {
        Some((_, len)) => {
            (if at_least != 0 { len >= n as usize } else { len == n as usize }) as u64
        }
        None => 0,
    }
}

/// Pattern extraction of an integer segment. flags: bit0 little-endian,
/// bit1 signed. Returns the sentinel for out-of-bounds / non-binary —
/// pattern-match failure, NOT an exception. Non-allocating.
#[no_mangle]
pub extern "C" fn mana_rt_bin_read_int(bin: u64, off: u64, nbytes: u64, flags: u64) -> u64 {
    let Some((p, len)) = bin_parts(bin) else {
        return EXC_SENTINEL;
    };
    let (off, nbytes) = (off as usize, nbytes as usize);
    if off + nbytes > len {
        return EXC_SENTINEL;
    }
    if nbytes > 8 {
        // dynamic sizes beyond 64 bits would need bignums — fail the match
        // (TODO(bignum-segments): BEAM would succeed)
        return EXC_SENTINEL;
    }
    let mut v: u64 = 0;
    unsafe {
        if flags & 1 != 0 {
            for i in (0..nbytes).rev() {
                v = (v << 8) | *p.add(off + i) as u64;
            }
        } else {
            for i in 0..nbytes {
                v = (v << 8) | *p.add(off + i) as u64;
            }
        }
    }
    let sv = if flags & 2 != 0 && nbytes > 0 {
        let shift = 64 - 8 * nbytes.min(8) as u32;
        if shift > 0 { ((v << shift) as i64) >> shift } else { v as i64 }
    } else {
        v as i64
    };
    // small ints hold 61 bits; 64-bit segments with larger values need
    // bignums we don't have
    if nbytes >= 8 && (sv >> 60 != 0 && sv >> 60 != -1) {
        eprintln!("mana: TODO(bignum-segments): 64-bit binary segment value out of small-int range");
        std::process::abort();
    }
    ((sv << 3) as u64) | TAG_SMALL
}

/// Pattern extraction of a utf8 segment: decode one code point at `off`.
/// Returns -1 for fail, else (width_bytes << 32) | code_point.
#[no_mangle]
pub extern "C" fn mana_rt_bin_read_utf8(bin: u64, off: u64) -> i64 {
    let Some((p, len)) = bin_parts(bin) else {
        return -1;
    };
    let off = off as usize;
    if off >= len {
        return -1;
    }
    let bytes = unsafe { std::slice::from_raw_parts(p.add(off), len - off) };
    let width = match bytes[0] {
        0x00..=0x7f => 1,
        0xc0..=0xdf => 2,
        0xe0..=0xef => 3,
        0xf0..=0xf7 => 4,
        _ => return -1,
    };
    if bytes.len() < width {
        return -1;
    }
    match std::str::from_utf8(&bytes[..width]) {
        Ok(s) => {
            let cp = s.chars().next().unwrap() as u32;
            ((width as i64) << 32) | cp as i64
        }
        Err(_) => -1,
    }
}

/// Construction: utf8 width of a code point term (0 = invalid → badarg).
#[no_mangle]
pub extern "C" fn mana_rt_utf8_width(cp: u64) -> u64 {
    if cp & TAG_MASK != TAG_SMALL {
        return 0;
    }
    u32::try_from(cp as i64 >> 3)
        .ok()
        .and_then(char::from_u32)
        .map(|c| c.len_utf8() as u64)
        .unwrap_or(0)
}

/// Construction writer: utf8-encode a code point; returns bytes written
/// (the width was already validated by mana_rt_utf8_width).
#[no_mangle]
pub extern "C" fn mana_rt_bin_write_utf8(bin: u64, off: u64, cp: u64) -> u64 {
    let c = char::from_u32((cp as i64 >> 3) as u32).unwrap();
    let mut buf = [0u8; 4];
    let s = c.encode_utf8(&mut buf);
    let (p, _) = bin_parts(bin).unwrap();
    unsafe {
        std::ptr::copy_nonoverlapping(s.as_ptr(), (p as *mut u8).add(off as usize), s.len());
    }
    s.len() as u64
}

/// Pattern extraction of a binary segment: `len < 0` means the whole rest.
/// Sentinel = match failure. Small slices copy (BEAM's heap-binary
/// heuristic — cheap and they don't pin the parent); larger ones become
/// zero-copy KIND_SUBBIN views over the ROOT binary (slicing a view folds
/// offsets, so views never chain).
#[no_mangle]
pub extern "C" fn mana_rt_bin_slice(ctx: *mut ProcCtx, bin: u64, off: u64, len: i64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, total)) = bin_parts(bin) else {
        return EXC_SENTINEL;
    };
    let off = off as usize;
    if off > total {
        return EXC_SENTINEL;
    }
    let len = if len < 0 { total - off } else { len as usize };
    if off + len > total {
        return EXC_SENTINEL;
    }
    if len <= 64 {
        let saved = ctx.roots_head;
        let mut fr = [0u64, 1, bin];
        fr[0] = saved;
        ctx.roots_head = fr.as_ptr() as u64;
        let newp = alloc_bin(ctx, len);
        ctx.roots_head = saved;
        let (p, _) = bin_parts(fr[2]).unwrap();
        unsafe {
            std::ptr::copy_nonoverlapping(p.add(off), newp.add(1) as *mut u8, len);
        }
        return newp as u64;
    }
    let (parent, abs_off) = {
        let p = bin as *const u64;
        if unsafe { *p } & 0xff == KIND_SUBBIN {
            (unsafe { *p.add(1) }, unsafe { *p.add(2) } as usize + off)
        } else {
            (bin, off)
        }
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, parent];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let vp = alloc_nursery(ctx, 3);
    ctx.roots_head = saved;
    unsafe {
        *vp = ((len as u64) << 8) | KIND_SUBBIN;
        *vp.add(1) = fr[2];
        *vp.add(2) = abs_off as u64;
    }
    vp as u64
}

/// Construction writer: constant segment bytes from a static array.
#[no_mangle]
pub extern "C" fn mana_rt_bin_write_bytes(bin: u64, off: u64, ptr: *const u8, len: u64) {
    let (p, _) = bin_parts(bin).unwrap();
    unsafe {
        std::ptr::copy_nonoverlapping(ptr, (p as *mut u8).add(off as usize), len as usize);
    }
}

/// Pattern check: do the bytes at `off` equal a constant array? 0 for
/// non-binary / out of bounds / mismatch. Non-allocating.
#[no_mangle]
pub extern "C" fn mana_rt_bin_match_bytes(bin: u64, off: u64, ptr: *const u8, len: u64) -> u64 {
    let Some((p, total)) = bin_parts(bin) else {
        return 0;
    };
    let (off, len) = (off as usize, len as usize);
    if off + len > total {
        return 0;
    }
    let a = unsafe { std::slice::from_raw_parts(p.add(off), len) };
    let b = unsafe { std::slice::from_raw_parts(ptr, len) };
    (a == b) as u64
}

/// Construction writer: store an integer segment (truncating, like BEAM).
/// Non-allocating; badarg if the value is not a small int.
#[no_mangle]
pub extern "C" fn mana_rt_bin_write_int(
    ctx: *mut ProcCtx,
    bin: u64,
    off: u64,
    val: u64,
    nbytes: u64,
    little: u64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    // BEAM truncates integer segments to the low bits — bignums included
    let v: u64 = if val & TAG_MASK == TAG_SMALL {
        (val as i64 >> 3) as u64
    } else if let Some((neg, mag)) = bignum_parts(val) {
        // low 64 bits, two's complement for negatives (nbytes <= 8)
        let lo = mag[0];
        if neg { lo.wrapping_neg() } else { lo }
    } else {
        return raise_badarg(ctx);
    };
    let (p, _) = bin_parts(bin).unwrap();
    let (off, nbytes) = (off as usize, nbytes as usize);
    unsafe {
        let p = p as *mut u8;
        for i in 0..nbytes {
            let byte = (v >> (8 * if little != 0 { i } else { nbytes - 1 - i })) as u8;
            *p.add(off + i) = byte;
        }
    }
    0
}

/// Construction writer: splice a binary. `len < 0` copies all of it; a
/// non-negative len copies the first len bytes (badarg if src is shorter,
/// like BEAM's fixed-size binary segments). Non-allocating.
#[no_mangle]
pub extern "C" fn mana_rt_bin_write_bin(
    ctx: *mut ProcCtx,
    bin: u64,
    off: u64,
    src: u64,
    len: i64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((sp, sn)) = bin_parts(src) else {
        return raise_badarg(ctx);
    };
    let n = if len < 0 {
        sn
    } else if (len as usize) <= sn {
        len as usize
    } else {
        return raise_badarg(ctx);
    };
    let (p, _) = bin_parts(bin).unwrap();
    unsafe {
        std::ptr::copy_nonoverlapping(sp, (p as *mut u8).add(off as usize), n);
    }
    0
}

/// erlang:byte_size/1 (raising convention).
#[no_mangle]
pub extern "C" fn mana_rt_byte_size(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    match bin_parts(t) {
        Some((_, n)) => ((n as u64) << 3) | TAG_SMALL,
        None => raise_badarg(ctx),
    }
}

/// erlang:binary_part/3 — negative length reaches backwards (BEAM).
#[no_mangle]
pub extern "C" fn mana_rt_binary_part(ctx: *mut ProcCtx, bin: u64, pos: u64, len: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, total)) = bin_parts(bin) else {
        return raise_badarg(ctx);
    };
    if pos & TAG_MASK != TAG_SMALL || len & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let (pos, len) = (pos as i64 >> 3, len as i64 >> 3);
    let (start, n) = if len < 0 { (pos + len, -len) } else { (pos, len) };
    if start < 0 || n < 0 || (start + n) as usize > total || start as usize > total {
        return raise_badarg(ctx);
    }
    let v = mana_rt_bin_slice(ctx, bin, start as u64, n);
    if v == EXC_SENTINEL {
        return raise_badarg(ctx);
    }
    v
}

/// erlang:list_to_tuple/1.
#[no_mangle]
pub extern "C" fn mana_rt_list_to_tuple(ctx: *mut ProcCtx, l: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    // count first (validates properness)
    let mut n = 0usize;
    let mut cur = l;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        n += 1;
        cur = unsafe { *((cur & !TAG_MASK) as *const u64).add(1) };
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, l];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let t = alloc_nursery(ctx, 1 + n);
    ctx.roots_head = saved;
    unsafe {
        *t = ((n as u64) << 8) | KIND_TUPLE;
        let mut cur = fr[2];
        for i in 0..n {
            let p = (cur & !TAG_MASK) as *const u64;
            *t.add(1 + i) = *p;
            cur = *p.add(1);
        }
    }
    t as u64
}

/// erlang:tuple_to_list/1.
#[no_mangle]
pub extern "C" fn mana_rt_tuple_to_list(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let ok = t & TAG_MASK == TAG_BOXED
        && t != 0
        && unsafe { *(t as *const u64) } & 0xff == KIND_TUPLE;
    if !ok {
        return raise_badarg(ctx);
    }
    let n = (unsafe { *(t as *const u64) } >> 8) as usize;
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, t, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for i in (0..n).rev() {
        let cell = alloc_nursery(ctx, 2);
        let tp = fr[2] as *const u64;
        unsafe {
            *cell = *tp.add(1 + i);
            *cell.add(1) = fr[3];
        }
        fr[3] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[3]
}

/// erlang:split_binary/2 → {Prefix, Suffix}.
#[no_mangle]
pub extern "C" fn mana_rt_split_binary(ctx: *mut ProcCtx, bin: u64, pos: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, total)) = bin_parts(bin) else {
        return raise_badarg(ctx);
    };
    if pos & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let at = pos as i64 >> 3;
    if at < 0 || at as usize > total {
        return raise_badarg(ctx);
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, bin, 0, 0];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    fr[3] = mana_rt_bin_slice(ctx, fr[2], 0, at);
    fr[4] = mana_rt_bin_slice(ctx, fr[2], at as u64, -1);
    let t = alloc_nursery(ctx, 3);
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = fr[3];
        *t.add(2) = fr[4];
    }
    ctx.roots_head = saved;
    t as u64
}

/// erlang:binary_to_list/1.
#[no_mangle]
pub extern "C" fn mana_rt_binary_to_list(ctx: *mut ProcCtx, bin: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, n)) = bin_parts(bin) else {
        return raise_badarg(ctx);
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, bin, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for i in (0..n).rev() {
        let cell = alloc_nursery(ctx, 2);
        let (p, _) = bin_parts(fr[2]).unwrap();
        unsafe {
            *cell = ((*p.add(i) as u64) << 3) | TAG_SMALL;
            *cell.add(1) = fr[3];
        }
        fr[3] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[3]
}

/// Flatten an iolist (nested lists of bytes and binaries, binary tails
/// allowed) into `out`. Err = badarg.
pub(crate) fn iolist_flatten(t: u64, out: &mut Vec<u8>) -> Result<(), ()> {
    if let Some((p, n)) = bin_parts(t) {
        out.extend_from_slice(unsafe { std::slice::from_raw_parts(p, n) });
        return Ok(());
    }
    let mut cur = t;
    loop {
        if cur == NIL {
            return Ok(());
        }
        if cur & TAG_MASK != TAG_CONS {
            // a binary tail terminates an iolist
            if bin_parts(cur).is_some() {
                return iolist_flatten(cur, out);
            }
            return Err(());
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK == TAG_SMALL {
            let v = h as i64 >> 3;
            if !(0..=255).contains(&v) {
                return Err(());
            }
            out.push(v as u8);
        } else {
            iolist_flatten(h, out)?;
        }
        cur = unsafe { *p.add(1) };
    }
}

pub(crate) fn bytes_to_new_bin(ctx: &mut ProcCtx, bytes: &[u8]) -> u64 {
    // bytes are already copied out of the heap — nothing to root
    let p = alloc_bin(ctx, bytes.len());
    unsafe {
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), p.add(1) as *mut u8, bytes.len());
    }
    p as u64
}

/// erlang:list_to_binary/1 (accepts iolists, like BEAM).
#[no_mangle]
pub extern "C" fn mana_rt_list_to_binary(ctx: *mut ProcCtx, l: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if l != NIL && l & TAG_MASK != TAG_CONS {
        return raise_badarg(ctx);
    }
    let mut out = Vec::new();
    match iolist_flatten(l, &mut out) {
        Ok(()) => bytes_to_new_bin(ctx, &out),
        Err(()) => raise_badarg(ctx),
    }
}

/// erlang:iolist_to_binary/1 — also accepts a bare binary.
#[no_mangle]
pub extern "C" fn mana_rt_iolist_to_binary(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut out = Vec::new();
    match iolist_flatten(t, &mut out) {
        Ok(()) => bytes_to_new_bin(ctx, &out),
        Err(()) => raise_badarg(ctx),
    }
}

/// Patterns: a binary or a non-empty list of binaries (compile_pattern is
/// the identity in our world). Byte vectors returned for searching.
pub(crate) fn pattern_bins(pat: u64) -> Result<Vec<&'static [u8]>, ()> {
    if bin_parts(pat).is_some() {
        return Ok(vec![bin_bytes(pat)]);
    }
    let mut out = Vec::new();
    let mut cur = pat;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return Err(());
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if bin_parts(h).is_none() {
            return Err(());
        }
        out.push(bin_bytes(h));
        cur = unsafe { *p.add(1) };
    }
    if out.is_empty() || out.iter().any(|b| b.is_empty()) {
        return Err(());
    }
    Ok(out)
}

/// Leftmost match at or after `from`; longest pattern wins ties.
pub(crate) fn bin_search(hay: &[u8], pats: &[&[u8]], from: usize) -> Option<(usize, usize)> {
    // longest match at the leftmost position (BEAM's binary:match rule).
    // Single pattern: scan for its first byte, then one slice compare — the
    // per-position starts_with loop was ~15% of a Phoenix request across
    // binary:split/match on header lines.
    if let [p] = pats {
        if p.is_empty() {
            return None;
        }
        let mut i = from;
        while i + p.len() <= hay.len() {
            let Some(k) = hay[i..].iter().position(|&b| b == p[0]) else { return None };
            i += k;
            if hay[i..].starts_with(p) {
                return Some((i, p.len()));
            }
            i += 1;
        }
        return None;
    }
    for i in from..hay.len() {
        let mut best = 0usize;
        for p in pats {
            if p.len() > best && hay[i..].starts_with(p) {
                best = p.len();
            }
        }
        if best > 0 {
            return Some((i, best));
        }
    }
    None
}

/// binary:split/2,3. opts term: nil or list of global/trim/trim_all.
#[no_mangle]
pub extern "C" fn mana_rt_binary_split(ctx: *mut ProcCtx, bin: u64, pat: u64, opts: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if bin_parts(bin).is_none() {
        return raise_badarg(ctx);
    }
    let Ok(pats) = pattern_bins(pat) else {
        return raise_badarg(ctx);
    };
    let (mut global, mut trim, mut trim_all) = (false, false, false);
    let mut cur = opts;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let opt = unsafe { *p };
        match atom_bytes(opt) {
            b"global" => global = true,
            b"trim" => trim = true,
            b"trim_all" => trim_all = true,
            _ => return raise_badarg(ctx),
        }
        cur = unsafe { *p.add(1) };
    }
    // search over the live bytes (no allocation happens until the result is
    // built), recording part RANGES; the parts then become zero-copy views
    // of the subject via bin_slice (BEAM returns sub-binaries here too), so
    // a split copies nothing but its list cells
    let hay: &[u8] = bin_bytes(bin);
    let mut parts: Vec<(usize, usize)> = Vec::new();
    let mut start = 0usize;
    loop {
        match bin_search(hay, &pats, start) {
            Some((at, len)) => {
                parts.push((start, at - start));
                start = at + len;
                if !global {
                    break;
                }
            }
            None => break,
        }
    }
    parts.push((start, hay.len() - start));
    if trim_all {
        parts.retain(|&(_, l)| l != 0);
    } else if trim {
        while parts.last().is_some_and(|&(_, l)| l == 0) {
            parts.pop();
        }
    }
    // build the result list back-to-front, rooting the subject, the
    // partial list and the fresh part across each allocation
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, bin, NIL, 0];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &(off, len) in parts.iter().rev() {
        fr[4] = mana_rt_bin_slice(ctx, fr[2], off as u64, len as i64);
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = fr[4];
            *cell.add(1) = fr[3];
        }
        fr[3] = cell as u64 | TAG_CONS;
        fr[4] = 0;
    }
    ctx.roots_head = saved;
    fr[3]
}

/// binary:match/2,3 (mode 0: {S,L}|nomatch) and matches (mode 1: list).
#[no_mangle]
pub extern "C" fn mana_rt_binary_match(ctx: *mut ProcCtx, bin: u64, pat: u64, mode: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if bin_parts(bin).is_none() {
        return raise_badarg(ctx);
    }
    let Ok(pats) = pattern_bins(pat) else {
        return raise_badarg(ctx);
    };
    let hay: Vec<u8> = bin_bytes(bin).to_vec();
    let pats: Vec<Vec<u8>> = pats.iter().map(|p| p.to_vec()).collect();
    let pref: Vec<&[u8]> = pats.iter().map(|p| p.as_slice()).collect();
    fn mk_pair(ctx: &mut ProcCtx, at: usize, len: usize) -> u64 {
        let t = alloc_nursery(ctx, 3);
        unsafe {
            *t = (2 << 8) | KIND_TUPLE;
            *t.add(1) = ((at as u64) << 3) | TAG_SMALL;
            *t.add(2) = ((len as u64) << 3) | TAG_SMALL;
        }
        t as u64
    }
    if mode == 0 {
        return match bin_search(&hay, &pref, 0) {
            Some((at, len)) => mk_pair(ctx, at, len),
            None => find_atom("nomatch").expect("nomatch atom compiled in"),
        };
    }
    let mut hits = Vec::new();
    let mut start = 0usize;
    while let Some((at, len)) = bin_search(&hay, &pref, start) {
        hits.push((at, len));
        start = at + len;
    }
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, 0];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &(at, len) in hits.iter().rev() {
        fr[3] = mk_pair(ctx, at, len);
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
}

/// binary:copy/2 (copy/1 passes n = 1).
#[no_mangle]
pub extern "C" fn mana_rt_binary_copy(ctx: *mut ProcCtx, bin: u64, n: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if bin_parts(bin).is_none() || n & TAG_MASK != TAG_SMALL || (n as i64 >> 3) < 0 {
        return raise_badarg(ctx);
    }
    let count = (n as i64 >> 3) as usize;
    let bytes: Vec<u8> = bin_bytes(bin).repeat(count);
    bytes_to_new_bin(ctx, &bytes)
}

/// binary:at/2 (pos is a term); `last` != 0 → last byte (binary:last/1),
/// ignoring pos.
#[no_mangle]
pub extern "C" fn mana_rt_binary_at(ctx: *mut ProcCtx, bin: u64, pos: u64, last: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((p, len)) = bin_parts(bin) else {
        return raise_badarg(ctx);
    };
    if len == 0 {
        return raise_badarg(ctx);
    }
    let i = if last != 0 {
        len - 1
    } else {
        if pos & TAG_MASK != TAG_SMALL || (pos as i64 >> 3) < 0 {
            return raise_badarg(ctx);
        }
        (pos as i64 >> 3) as usize
    };
    if i >= len {
        return raise_badarg(ctx);
    }
    let b = unsafe { *p.add(i) };
    ((b as u64) << 3) | TAG_SMALL
}

/// binary:encode_unsigned/1,2 (little != 0 → little-endian).
#[no_mangle]
pub extern "C" fn mana_rt_binary_encode_unsigned(ctx: *mut ProcCtx, n: u64, little: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if n & TAG_MASK != TAG_SMALL || (n as i64) < 0 {
        return raise_badarg(ctx);
    }
    let v = (n as i64 >> 3) as u64;
    let mut bytes: Vec<u8> = Vec::new();
    let mut x = v;
    loop {
        bytes.push((x & 0xff) as u8);
        x >>= 8;
        if x == 0 {
            break;
        }
    }
    if little == 0 {
        bytes.reverse();
    }
    bytes_to_new_bin(ctx, &bytes)
}

/// binary:decode_unsigned/1,2.
#[no_mangle]
pub extern "C" fn mana_rt_binary_decode_unsigned(ctx: *mut ProcCtx, bin: u64, little: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if bin_parts(bin).is_none() {
        return raise_badarg(ctx);
    }
    // `little` is 0 (the /1 default) or the endianness atom from /2
    let is_little =
        little & TAG_MASK == TAG_ATOM && atom_bytes(little) == b"little";
    let bytes = bin_bytes(bin).to_vec();
    let le: Vec<u8> = if is_little {
        bytes
    } else {
        bytes.iter().rev().copied().collect()
    };
    let mag = bigint::mag_from_bytes_le(&le);
    make_int_mag(ctx, false, &mag)
}

/// binary:longest_common_prefix/1 (suffix != 0 → suffix variant).
#[no_mangle]
pub extern "C" fn mana_rt_binary_lcp(ctx: *mut ProcCtx, list: u64, suffix: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if list & TAG_MASK != TAG_CONS {
        return raise_badarg(ctx);
    }
    let Ok(bins) = pattern_bins(list) else {
        return raise_badarg(ctx);
    };
    let mut common = usize::MAX;
    let first = bins[0];
    for b in &bins {
        let mut n = 0;
        let max = first.len().min(b.len());
        while n < max {
            let (x, y) = if suffix != 0 {
                (first[first.len() - 1 - n], b[b.len() - 1 - n])
            } else {
                (first[n], b[n])
            };
            if x != y {
                break;
            }
            n += 1;
        }
        common = common.min(n);
    }
    ((common as u64) << 3) | TAG_SMALL
}
