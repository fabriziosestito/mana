//! Number terms: bignums (`KIND_BIGNUM`), boxed floats, and the arithmetic
//! slow path. The limb math lives in `mod bigint`. Every constructor in this
//! module allocates in the nursery or in the shared old space. No function
//! in this module is a GC point.

use super::*;

// Bignums

/// Returns (negative, limbs) of a bignum term.
pub(crate) fn bignum_parts(t: u64) -> Option<(bool, &'static [u64])> {
    if t & TAG_MASK != TAG_BOXED || t == 0 {
        return None;
    }
    let p = t as *const u64;
    let h = unsafe { *p };
    if h & 0xff != KIND_BIGNUM {
        return None;
    }
    Some((h & 0x100 != 0, unsafe {
        std::slice::from_raw_parts(p.add(1), (h >> 9) as usize)
    }))
}

/// Returns true if the term is an integer (small or bignum).
pub(crate) fn is_int_term(t: u64) -> bool {
    t & TAG_MASK == TAG_SMALL || bignum_parts(t).is_some()
}

/// Returns (negative, magnitude) of any integer term.
pub(crate) fn int_mag(t: u64) -> Option<(bool, Vec<u64>)> {
    if t & TAG_MASK == TAG_SMALL {
        let v = t as i64 >> 3;
        return Some(if v < 0 {
            (true, bigint::normalize(vec![v.unsigned_abs()]))
        } else {
            (false, bigint::normalize(vec![v as u64]))
        });
    }
    bignum_parts(t).map(|(neg, l)| (neg, l.to_vec()))
}

/// The single integer constructor. The result is a small when the value fits
/// the small range -2^60 ..= 2^60-1. Otherwise the result is a bignum in the
/// shared old space. This function is never a GC point.
pub(crate) fn make_int_mag(ctx: &mut ProcCtx, negative: bool, mag: &[u64]) -> u64 {
    if mag.is_empty() {
        return TAG_SMALL; // the small integer zero
    }
    if mag.len() == 1 {
        let v = mag[0];
        if (!negative && v <= (1u64 << 60) - 1) || (negative && v <= 1u64 << 60) {
            let sv = if negative { -(v as i64) } else { v as i64 };
            return ((sv << 3) as u64) | TAG_SMALL;
        }
    }
    let p = alloc_shared(ctx, 1 + mag.len());
    unsafe {
        *p = ((mag.len() as u64) << 9) | ((negative as u64) << 8) | KIND_BIGNUM;
        for (i, &l) in mag.iter().enumerate() {
            *p.add(1 + i) = l;
        }
    }
    p as u64
}

/// Builds an eternal bignum for literals. No `ctx` is available at that point.
pub(crate) fn make_int_mag_eternal(negative: bool, mag: &[u64]) -> u64 {
    debug_assert!(!mag.is_empty());
    let p = alloc_space(1 + mag.len());
    unsafe {
        *p = ((mag.len() as u64) << 9) | ((negative as u64) << 8) | KIND_BIGNUM;
        for (i, &l) in mag.iter().enumerate() {
            *p.add(1 + i) = l;
        }
    }
    p as u64
}

/// Returns the interned eternal term of a big literal. The key is the decimal
/// text of the literal.
#[no_mangle]
pub extern "C" fn mana_rt_big_literal(ptr: *const u8, len: u64) -> u64 {
    static TABLE: std::sync::Mutex<Option<std::collections::HashMap<&'static [u8], u64>>> =
        std::sync::Mutex::new(None);
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len as usize) };
    let mut guard = TABLE.lock().unwrap();
    let map = guard.get_or_insert_with(Default::default);
    if let Some(&t) = map.get(bytes) {
        return t;
    }
    let (neg, digits) = match bytes.strip_prefix(b"-") {
        Some(rest) => (true, rest),
        None => (false, bytes),
    };
    let mag = bigint::mag_from_decimal(digits).expect("invalid big literal");
    let t = make_int_mag_eternal(neg, &mag);
    let key: &'static [u8] = Box::leak(bytes.to_vec().into_boxed_slice());
    map.insert(key, t);
    t
}

/// Exact comparison of two integer terms (small or bignum).
pub(crate) fn int_cmp_exact(a: u64, b: u64) -> i64 {
    if a & TAG_MASK == TAG_SMALL && b & TAG_MASK == TAG_SMALL {
        let (x, y) = (a as i64 >> 3, b as i64 >> 3);
        return (x > y) as i64 - (x < y) as i64;
    }
    let (na, ma) = int_mag(a).expect("int_cmp_exact: not an integer");
    let (nb, mb) = int_mag(b).expect("int_cmp_exact: not an integer");
    // A normalized zero has an empty magnitude and negative=false.
    if na != nb {
        return if na { -1 } else { 1 };
    }
    let r = match bigint::mag_cmp(&ma, &mb) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    };
    if na {
        -r
    } else {
        r
    }
}

// Floats and arithmetic

pub(crate) fn raise_badarith(ctx: &mut ProcCtx) -> u64 {
    ctx.exc_class = atom_error();
    ctx.exc_reason = known().badarith;
    EXC_SENTINEL
}

/// Boxes an f64 and never starts a collection. The float goes in the nursery
/// if there is room. Otherwise it goes in the shared old space. The old space
/// does not move. Majors run only at safepoints, and a BIF call is not a
/// safepoint. This keeps arithmetic out of the may-GC effect set, so integer
/// loops stay frameless. Cost: a float born while the nursery is full lives
/// until the next major.
pub(crate) fn box_float(ctx: &mut ProcCtx, f: f64) -> u64 {
    let p = unsafe {
        if ctx.heap_top.add(2) <= ctx.heap_end {
            let p = ctx.heap_top;
            ctx.heap_top = ctx.heap_top.add(2);
            p
        } else {
            let g = ctx.global;
            let mut old = g.old.lock();
            old.alloc(2, &g.old_used)
        }
    };
    unsafe {
        *p = (1 << 8) | KIND_FLOAT;
        *p.add(1) = f.to_bits();
    }
    p as u64
}

/// Float literal pattern test. Returns 1 if `t` is a float with exactly the
/// bits `bits`. This function does not allocate, so it is safe inside match
/// contexts.
#[no_mangle]
pub extern "C" fn mana_rt_float_pat(t: u64, bits: u64) -> u64 {
    if t & TAG_MASK != TAG_BOXED || t == 0 {
        return 0;
    }
    let p = t as *const u64;
    unsafe { (*p & 0xff == KIND_FLOAT && *p.add(1) == bits) as u64 }
}

/// Numeric coercion for arithmetic. `None` means the term is not a number,
/// and the caller raises badarith. A bignum coerces to its f64 for
/// float-mixed operations. That f64 can be rounded.
pub(crate) fn num_of(t: u64) -> Option<(f64, bool)> {
    if t & TAG_MASK == TAG_SMALL {
        return Some(((t as i64 >> 3) as f64, true));
    }
    if t & TAG_MASK == TAG_BOXED && t != 0 {
        let p = t as *const u64;
        if unsafe { *p } & 0xff == KIND_FLOAT {
            return Some((f64::from_bits(unsafe { *p.add(1) }), false));
        }
        if let Some((neg, mag)) = bignum_parts(t) {
            let v = bigint::mag_to_f64(mag);
            return Some((if neg { -v } else { v }, true));
        }
    }
    None
}

pub(crate) fn abort_bignum(what: &str) -> ! {
    eprintln!("mana: TODO(bignum): {}", what);
    std::process::exit(1);
}

// Arithmetic opcodes for mana_rt_arith.
pub const AR_ADD: u64 = 0;

pub const AR_SUB: u64 = 1;

pub const AR_MUL: u64 = 2;

pub const AR_FDIV: u64 = 3;

pub const AR_IDIV: u64 = 4;

pub const AR_REM: u64 = 5;

pub const AR_NEG: u64 = 6;

pub const AR_ABS: u64 = 7;

pub const AR_BAND: u64 = 8;

pub const AR_BOR: u64 = 9;

pub const AR_BXOR: u64 = 10;

pub const AR_BSL: u64 = 11;

pub const AR_BSR: u64 = 12;

pub const AR_BNOT: u64 = 13;

/// Signed magnitude addition: (na, ma) + (nb, mb).
pub(crate) fn int_signed_add(na: bool, ma: &[u64], nb: bool, mb: &[u64]) -> (bool, Vec<u64>) {
    if na == nb {
        return (na, bigint::mag_add(ma, mb));
    }
    match bigint::mag_cmp(ma, mb) {
        std::cmp::Ordering::Equal => (false, Vec::new()),
        std::cmp::Ordering::Greater => (na, bigint::mag_sub(ma, mb)),
        std::cmp::Ordering::Less => (nb, bigint::mag_sub(mb, ma)),
    }
}

/// Integer arithmetic on small or bignum operands, with promotion and
/// demotion. Results allocate in the shared old space. This function is never
/// a GC point.
pub(crate) fn int_arith(ctx: &mut ProcCtx, op: u64, a: u64, b: u64) -> u64 {
    let (na, ma) = int_mag(a).unwrap();
    match op {
        AR_NEG => return make_int_mag(ctx, !na && !ma.is_empty(), &ma),
        AR_ABS => return make_int_mag(ctx, false, &ma),
        AR_BNOT => {
            // bnot(x) = -x - 1.
            return if na {
                make_int_mag(ctx, false, &bigint::mag_sub(&ma, &[1]))
            } else {
                make_int_mag(ctx, true, &bigint::mag_add(&ma, &[1]))
            };
        }
        _ => {}
    }
    let (nb, mb) = int_mag(b).unwrap();
    match op {
        AR_ADD => {
            let (n, m) = int_signed_add(na, &ma, nb, &mb);
            make_int_mag(ctx, n, &m)
        }
        AR_SUB => {
            let (n, m) = int_signed_add(na, &ma, !nb && !mb.is_empty(), &mb);
            make_int_mag(ctx, n, &m)
        }
        AR_MUL => {
            let m = bigint::mag_mul(&ma, &mb);
            make_int_mag(ctx, na != nb && !m.is_empty(), &m)
        }
        AR_IDIV | AR_REM => {
            if mb.is_empty() {
                return raise_badarith(ctx);
            }
            // The division truncates. In Erlang, rem takes the sign of the dividend.
            let (q, r) = bigint::mag_divrem(&ma, &mb);
            if op == AR_IDIV {
                make_int_mag(ctx, (na != nb) && !q.is_empty(), &q)
            } else {
                make_int_mag(ctx, na && !r.is_empty(), &r)
            }
        }
        AR_FDIV => {
            let (x, y) = (num_val(a), num_val(b));
            if y == 0.0 {
                return raise_badarith(ctx);
            }
            box_float(ctx, x / y)
        }
        AR_BAND | AR_BOR | AR_BXOR => {
            if a & TAG_MASK == TAG_SMALL && b & TAG_MASK == TAG_SMALL {
                // Exact for all smalls. The results never leave the small range.
                let (x, y) = (a as i64 >> 3, b as i64 >> 3);
                let r = match op {
                    AR_BAND => x & y,
                    AR_BOR => x | y,
                    _ => x ^ y,
                };
                return ((r << 3) as u64) | TAG_SMALL;
            }
            if na || nb {
                // A negative bignum needs infinite two's-complement bit
                // operations. No current path needs this corner.
                abort_bignum("bit op on a negative bignum (TODO(bignum-bitops))");
            }
            let n = std::cmp::max(ma.len(), mb.len());
            let mut out = Vec::with_capacity(n);
            for i in 0..n {
                let (x, y) = (*ma.get(i).unwrap_or(&0), *mb.get(i).unwrap_or(&0));
                out.push(match op {
                    AR_BAND => x & y,
                    AR_BOR => x | y,
                    _ => x ^ y,
                });
            }
            make_int_mag(ctx, false, &bigint::normalize(out))
        }
        AR_BSL | AR_BSR => {
            // The shift count must be a small. A bignum-sized shift is an
            // absurd allocation. BEAM raises system_limit far earlier.
            if b & TAG_MASK != TAG_SMALL {
                return raise_badarith(ctx);
            }
            let y = b as i64 >> 3;
            // In Erlang, a negative count reverses the direction.
            let n = if op == AR_BSR { -y } else { y };
            if n >= 0 {
                let m = bigint::mag_shl(&ma, n as u64);
                make_int_mag(ctx, na && !m.is_empty(), &m)
            } else {
                let k = (-n) as u64;
                if na {
                    // Floor semantics: x >> k = -((|x| - 1) >> k) - 1.
                    let m = bigint::mag_shr(&bigint::mag_sub(&ma, &[1]), k);
                    make_int_mag(ctx, true, &bigint::mag_add(&m, &[1]))
                } else {
                    let m = bigint::mag_shr(&ma, k);
                    make_int_mag(ctx, false, &m)
                }
            }
        }
        _ => raise_badarith(ctx),
    }
}

/// Arithmetic slow path. It handles every case that is not the inline
/// both-small-int fast case. This includes small overflow, which promotes to
/// a bignum here. Mixed and float operations produce boxed floats. A
/// non-number raises badarith. An integer-only operation on a float raises
/// badarith. This matches BEAM.
#[no_mangle]
pub extern "C" fn mana_rt_arith(ctx: *mut ProcCtx, op: u64, a: u64, b: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let unary = matches!(op, AR_NEG | AR_ABS | AR_BNOT);
    if is_int_term(a) && (unary || is_int_term(b)) {
        return int_arith(ctx, op, a, b);
    }
    // Bit operations are integer-only. There is no float coercion.
    if let AR_BAND | AR_BOR | AR_BXOR | AR_BSL | AR_BSR | AR_BNOT = op {
        return raise_badarith(ctx);
    }
    let Some((x, _)) = num_of(a) else {
        return raise_badarith(ctx);
    };
    match op {
        AR_NEG => return box_float(ctx, -x),
        AR_ABS => return box_float(ctx, x.abs()),
        _ => {}
    }
    let Some((y, _)) = num_of(b) else {
        return raise_badarith(ctx);
    };
    match op {
        AR_ADD => box_float(ctx, x + y),
        AR_SUB => box_float(ctx, x - y),
        AR_MUL => box_float(ctx, x * y),
        AR_FDIV => {
            if y == 0.0 {
                return raise_badarith(ctx);
            }
            box_float(ctx, x / y)
        }
        // div and rem are integer-only. At least one operand is a float here.
        AR_IDIV | AR_REM => raise_badarith(ctx),
        _ => raise_badarith(ctx),
    }
}

/// The math module. All operations work on f64. A domain error raises
/// badarith, like BEAM.
#[no_mangle]
pub extern "C" fn mana_rt_math(ctx: *mut ProcCtx, op: u64, a: u64, b: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((x, _)) = num_of(a) else {
        return raise_badarith(ctx);
    };
    let y = match num_of(b) {
        Some((y, _)) => y,
        None => 0.0, // Unary operations pass a dummy small 0.
    };
    let r = match op {
        0 => x.sqrt(),
        1 => x.powf(y),
        2 => x.ln(),
        3 => x.log2(),
        4 => x.log10(),
        5 => x.exp(),
        6 => x.sin(),
        7 => x.cos(),
        8 => x.tan(),
        9 => x.asin(),
        10 => x.acos(),
        11 => x.atan(),
        12 => x.atan2(y),
        13 => x % y,                // fmod
        14 => std::f64::consts::PI, // pi/0
        15 => x.floor(),
        16 => x.ceil(),
        _ => return raise_badarith(ctx),
    };
    if r.is_nan() || r.is_infinite() {
        return raise_badarith(ctx);
    }
    box_float(ctx, r)
}

/// erlang:float/1.
#[no_mangle]
pub extern "C" fn mana_rt_to_float(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    match num_of(t) {
        Some((x, true)) => box_float(ctx, x),
        Some((_, false)) => t,
        None => raise_badarg(ctx),
    }
}

/// trunc, round, floor, and ceil to an integer. `mode` is 0..3 in that order.
#[no_mangle]
pub extern "C" fn mana_rt_f2i(ctx: *mut ProcCtx, mode: u64, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((x, xi)) = num_of(t) else {
        return raise_badarg(ctx);
    };
    if xi {
        return t;
    }
    let r = match mode {
        0 => x.trunc(),
        1 => x.round(),
        2 => x.floor(),
        _ => x.ceil(),
    };
    if !r.is_finite() {
        return raise_badarg(ctx);
    }
    let mag = bigint::f64_to_mag(r.abs());
    make_int_mag(ctx, r < 0.0 && !mag.is_empty(), &mag)
}

/// Elixir.Float round, ceil, and floor with a decimal precision. `mode` is
/// 0, 1, or 2 in that order. Elixir operates on the shortest decimal
/// representation of the float. This function formats the float at the
/// target precision, and that reproduces the Elixir result. Ties round half
/// to even. This matches the Rust formatter and the documented Elixir
/// behavior.
#[no_mangle]
pub extern "C" fn mana_rt_float_prec(ctx: *mut ProcCtx, t: u64, prec: u64, mode: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((x, is_int)) = num_of(t) else {
        return raise_badarg(ctx);
    };
    if is_int || prec & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let p = prec as i64 >> 3;
    if !(0..=15).contains(&p) {
        return raise_badarg(ctx);
    }
    let r = match mode {
        0 => {
            let s = format!("{:.*}", p as usize, x);
            s.parse::<f64>().unwrap_or(x)
        }
        1 => {
            let shift = 10f64.powi(p as i32);
            (x * shift).ceil() / shift
        }
        _ => {
            let shift = 10f64.powi(p as i32);
            (x * shift).floor() / shift
        }
    };
    box_float(ctx, r)
}

/// The float format of erlang:display. It is C-style %e with 6 fractional
/// digits and a signed two-digit exponent. Examples: 1.000000e+00,
/// 1.234568e+05, 1.000000e-05.
pub(crate) fn display_float(f: f64) -> String {
    let s = format!("{:.6e}", f); // Rust writes "1.000000e0" or "1.234568e5".
    match s.split_once('e') {
        Some((mant, exp)) => {
            let (sign, digits) = match exp.strip_prefix('-') {
                Some(d) => ('-', d),
                None => ('+', exp),
            };
            format!("{}e{}{:0>2}", mant, sign, digits)
        }
        None => s,
    }
}

/// BEAM-parity float text: the shortest round-trip form with a mandatory
/// decimal point. The exponent form matches the Ryu-based printer of OTP.
/// Examples: 1.0, 0.1, 1.0e20, 1.0e-5, -0.0.
pub(crate) fn fmt_float(f: f64) -> String {
    if f == f64::INFINITY || f == f64::NEG_INFINITY || f.is_nan() {
        return "nan_or_inf".into(); // Unreachable. Terms never hold these values.
    }
    let s = format!("{:?}", f); // The Rust shortest round-trip form.
    if let Some(epos) = s.find(['e', 'E']) {
        // Rust writes "1e20". Erlang writes "1.0e20".
        let (m, e) = s.split_at(epos);
        let mant = if m.contains('.') {
            m.to_string()
        } else {
            format!("{}.0", m)
        };
        return format!("{}{}", mant, e);
    }
    if !s.contains('.') {
        return format!("{}.0", s);
    }
    s
}

/// erlang:float_to_binary/1,2 and float_to_list. The options are: [:short]
/// for the shortest round-trip form, and {:decimals, N}. With {:decimals, N},
/// :compact trims the zeros at the end. With no options, the output is %e like
/// BEAM.
#[no_mangle]
pub extern "C" fn mana_rt_float_to_binary(
    ctx: *mut ProcCtx,
    t: u64,
    opts: u64,
    as_list: u64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((x, false)) = num_of(t) else {
        return raise_badarg(ctx);
    };
    let (mut decimals, mut compact, mut short) = (None::<usize>, false, false);
    let mut cur = opts;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let opt = unsafe { *p };
        if opt & TAG_MASK == TAG_ATOM {
            match atom_bytes(opt) {
                b"short" => short = true,
                b"compact" => compact = true,
                _ => {}
            }
        } else if opt & TAG_MASK == TAG_BOXED && opt != 0 {
            let hp = opt as *const u64;
            let h = unsafe { *hp };
            if h & 0xff == KIND_TUPLE
                && h >> 8 == 2
                && atom_bytes(unsafe { *hp.add(1) }) == b"decimals"
            {
                let d = unsafe { *hp.add(2) };
                if d & TAG_MASK == TAG_SMALL {
                    decimals = Some((d as i64 >> 3).clamp(0, 253) as usize);
                }
            }
        }
        cur = unsafe { *p.add(1) };
    }
    let s = if short {
        fmt_float(x)
    } else if let Some(d) = decimals {
        let mut s = format!("{:.*}", d, x);
        if compact && s.contains('.') {
            while s.ends_with('0') {
                s.pop();
            }
            if s.ends_with('.') {
                s.push('0');
            }
        }
        s
    } else {
        display_float(x)
    };
    if as_list != 0 {
        utf8_to_codepoint_list(ctx, s.as_bytes())
    } else {
        bytes_to_new_bin(ctx, s.as_bytes())
    }
}

/// erlang:binary_to_float/1 and list_to_float/1. The caller flattens the bytes
/// first.
#[no_mangle]
pub extern "C" fn mana_rt_parse_float(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let bytes: Vec<u8> = if bin_parts(t).is_some() {
        bin_bytes(t).to_vec()
    } else {
        let mut out = Vec::new();
        let mut cur = t;
        loop {
            if cur == NIL {
                break;
            }
            if cur & TAG_MASK != TAG_CONS {
                return raise_badarg(ctx);
            }
            let p = (cur & !TAG_MASK) as *const u64;
            let h = unsafe { *p };
            if h & TAG_MASK != TAG_SMALL {
                return raise_badarg(ctx);
            }
            out.push((h as i64 >> 3) as u8);
            cur = unsafe { *p.add(1) };
        }
        out
    };
    let s = match std::str::from_utf8(&bytes) {
        Ok(s) => s,
        Err(_) => return raise_badarg(ctx),
    };
    // BEAM requires a decimal point. For binary_to_float, "1" is badarg.
    if !s.contains('.') {
        return raise_badarg(ctx);
    }
    match s.parse::<f64>() {
        Ok(f) if f.is_finite() => box_float(ctx, f),
        _ => raise_badarg(ctx),
    }
}
