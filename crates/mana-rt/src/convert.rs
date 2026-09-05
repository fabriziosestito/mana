use super::*;

/// Integer digits in a base (2..=36, uppercase — BEAM's format).
/// Digits of ANY integer term in `base` (bignum-aware).
pub(crate) fn int_term_digits(t: u64, base: u32) -> Option<String> {
    if t & TAG_MASK == TAG_SMALL {
        return Some(int_digits(t as i64 >> 3, base));
    }
    let (neg, mag) = bignum_parts(t)?;
    let body = if base == 10 {
        bigint::mag_to_decimal(mag)
    } else {
        // repeated divrem by the base — rare path (Integer.to_string/2)
        let mut cur = mag.to_vec();
        let mut out = Vec::new();
        while !cur.is_empty() {
            let (q, r) = bigint::mag_divrem_limb(&cur, base as u64);
            out.push(
                char::from_digit(r as u32, base)
                    .unwrap()
                    .to_ascii_uppercase() as u8,
            );
            cur = q;
        }
        out.reverse();
        String::from_utf8(out).unwrap()
    };
    Some(if neg { format!("-{}", body) } else { body })
}

pub(crate) fn int_digits(v: i64, base: u32) -> String {
    if v == 0 {
        return "0".into();
    }
    let neg = v < 0;
    let mut x = v.unsigned_abs();
    let mut out = Vec::new();
    while x > 0 {
        let d = (x % base as u64) as u32;
        out.push(char::from_digit(d, base).unwrap().to_ascii_uppercase() as u8);
        x /= base as u64;
    }
    if neg {
        out.push(b'-');
    }
    out.reverse();
    String::from_utf8(out).unwrap()
}

/// erlang:integer_to_binary/1,2 (base as a term; small 10 for /1).
#[no_mangle]
pub extern "C" fn mana_rt_integer_to_binary(ctx: *mut ProcCtx, t: u64, base: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if !is_int_term(t) || base & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let b = base as i64 >> 3;
    if !(2..=36).contains(&b) {
        return raise_badarg(ctx);
    }
    let s = int_term_digits(t, b as u32).unwrap();
    bytes_to_new_bin(ctx, s.as_bytes())
}

/// erlang:integer_to_list/1,2.
#[no_mangle]
pub extern "C" fn mana_rt_integer_to_list(ctx: *mut ProcCtx, t: u64, base: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if !is_int_term(t) || base & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let b = base as i64 >> 3;
    if !(2..=36).contains(&b) {
        return raise_badarg(ctx);
    }
    let s = int_term_digits(t, b as u32).unwrap();
    bytes_to_charlist(ctx, s.as_bytes())
}

/// erlang:pid_to_list/1 — BEAM-style "<0.ID.0>" charlist (no distribution,
/// so node creation and serial are 0). Inspect.PID wraps this as
/// "#PID<0.ID.0>".
#[no_mangle]
pub extern "C" fn mana_rt_pid_to_list(ctx: *mut ProcCtx, pid: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if pid & 0xF != PID_TAG4 {
        return raise_badarg(ctx);
    }
    let id = pid >> 4;
    let s = format!("<0.{}.0>", id);
    bytes_to_charlist(ctx, s.as_bytes())
}

/// Parse decimal/base digits (with optional sign) — badarg on any junk.
pub(crate) fn parse_int_term(ctx: &mut ProcCtx, bytes: &[u8], base: u32) -> Option<u64> {
    let s = std::str::from_utf8(bytes).ok()?;
    if let Ok(v) = i64::from_str_radix(s, base) {
        if v >> 60 == 0 || v >> 60 == -1 {
            return Some(((v << 3) as u64) | TAG_SMALL);
        }
    }
    // outside i64 / outside the small range: parse into limbs
    let (neg, digits) = match s.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    if digits.is_empty() {
        return None;
    }
    let mag = if base == 10 {
        bigint::mag_from_decimal(digits.as_bytes())?
    } else {
        let mut acc: Vec<u64> = Vec::new();
        for c in digits.chars() {
            let d = c.to_digit(base)?;
            acc = bigint::mag_add(&bigint::mag_mul(&acc, &[base as u64]), &[d as u64]);
        }
        bigint::normalize(acc)
    };
    Some(make_int_mag(ctx, neg && !mag.is_empty(), &mag))
}

/// erlang:binary_to_integer/1,2.
#[no_mangle]
pub extern "C" fn mana_rt_binary_to_integer(ctx: *mut ProcCtx, bin: u64, base: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if bin_parts(bin).is_none() || base & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let b = base as i64 >> 3;
    if !(2..=36).contains(&b) {
        return raise_badarg(ctx);
    }
    let bytes = bin_bytes(bin).to_vec();
    match parse_int_term(ctx, &bytes, b as u32) {
        Some(t) => t,
        None => raise_badarg(ctx),
    }
}

/// erlang:list_to_integer/1,2.
#[no_mangle]
pub extern "C" fn mana_rt_list_to_integer(ctx: *mut ProcCtx, l: u64, base: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if base & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let b = base as i64 >> 3;
    if !(2..=36).contains(&b) {
        return raise_badarg(ctx);
    }
    let mut bytes = Vec::new();
    let mut cur = l;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK != TAG_SMALL {
            return raise_badarg(ctx);
        }
        bytes.push((h as i64 >> 3) as u8);
        cur = unsafe { *p.add(1) };
    }
    match parse_int_term(ctx, &bytes, b as u32) {
        Some(t) => t,
        None => raise_badarg(ctx),
    }
}

/// erlang:atom_to_list/1.
#[no_mangle]
pub extern "C" fn mana_rt_atom_to_list(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if t & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let bytes: Vec<u8> = atom_bytes(t).to_vec();
    bytes_to_charlist(ctx, &bytes)
}

/// erlang:atom_to_binary/1,2 (utf8 == latin1 for our ascii atom names).
#[no_mangle]
pub extern "C" fn mana_rt_atom_to_binary(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if t & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let bytes: Vec<u8> = atom_bytes(t).to_vec();
    bytes_to_new_bin(ctx, &bytes)
}

/// erlang:list_to_atom/1 (interning) and list_to_existing_atom/1 (strict).
#[no_mangle]
pub extern "C" fn mana_rt_list_to_atom(ctx: *mut ProcCtx, l: u64, existing: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut bytes = Vec::new();
    let mut cur = l;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK != TAG_SMALL {
            return raise_badarg(ctx);
        }
        let cp = h as i64 >> 3;
        let Some(c) = u32::try_from(cp).ok().and_then(char::from_u32) else {
            return raise_badarg(ctx);
        };
        let mut buf = [0u8; 4];
        bytes.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
        cur = unsafe { *p.add(1) };
    }
    if existing != 0 {
        match atom_lookup(&bytes) {
            Some(a) => a,
            None => raise_badarg(ctx),
        }
    } else {
        atom_intern(&bytes)
    }
}

/// erlang:binary_to_atom/1,2 — interns (existing == 0) or requires an
/// existing atom (binary_to_existing_atom).
#[no_mangle]
pub extern "C" fn mana_rt_binary_to_atom(ctx: *mut ProcCtx, bin: u64, existing: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((p, n)) = bin_parts(bin) else {
        return raise_badarg(ctx);
    };
    let bytes = unsafe { std::slice::from_raw_parts(p, n) };
    if existing != 0 {
        match atom_lookup(bytes) {
            Some(a) => a,
            None => raise_badarg(ctx),
        }
    } else {
        atom_intern(bytes)
    }
}
