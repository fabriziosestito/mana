use super::*;

// ---------------------------------------------------------------------------
// Public native-author ABI. These are the ONLY symbols a hex package's
// native/ crate (via the mana-native wrapper) calls to build/inspect terms.
// Everything else in this file is private runtime internals. Terms are
// tagged u64; the first arg is the ProcCtx (the codegen contract). Term
// construction that allocates may trigger GC — the caller (mana-native's
// Env) roots live terms across allocations.

/// Bump-allocate `words` on the process nursery; may GC. Returns a raw
/// heap pointer the caller fills with a header + term words. The caller
/// must read any live child terms from its root frame AFTER this call
/// (GC may have moved them).
#[no_mangle]
pub extern "C" fn mana_rt_native_alloc(ctx: *mut ProcCtx, words: u64) -> *mut u64 {
    let ctx = unsafe { &mut *ctx };
    alloc_nursery(ctx, words as usize)
}

/// Build a binary term from raw bytes (copied — the source is not a term,
/// so no rooting needed).
#[no_mangle]
pub extern "C" fn mana_rt_native_make_binary(
    ctx: *mut ProcCtx,
    ptr: *const u8,
    len: usize,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    bytes_to_new_bin(ctx, bytes)
}

/// Build an integer term (small or bignum, normalized).
#[no_mangle]
pub extern "C" fn mana_rt_native_make_int(ctx: *mut ProcCtx, v: i64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    make_int_mag(ctx, v < 0, &[v.unsigned_abs()])
}

/// Build an unsigned integer term (small or bignum) — for JSON numbers
/// that exceed i64 range.
#[no_mangle]
pub extern "C" fn mana_rt_native_make_uint(ctx: *mut ProcCtx, v: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    make_int_mag(ctx, false, &[v])
}

/// Build a boxed float term.
#[no_mangle]
pub extern "C" fn mana_rt_native_make_float(ctx: *mut ProcCtx, v: f64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    box_float(ctx, v)
}

/// Intern an atom from raw bytes (atoms are eternal — no ctx / no GC).
#[no_mangle]
pub extern "C" fn mana_rt_native_make_atom(ptr: *const u8, len: usize) -> u64 {
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    atom_intern(bytes)
}

/// Raise `badarg` from native code (sets the exception cells, returns the
/// sentinel the caller returns to unwind).
#[no_mangle]
pub extern "C" fn mana_rt_native_raise_badarg(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &mut *ctx };
    raise_badarg(ctx)
}

/// Inspection: if `t` is a binary or sub-binary view, write its current
/// data pointer + length and return 1; else return 0. (Handles the view's
/// GC-recomputed data pointer so mana-native need not duplicate that.)
#[no_mangle]
pub extern "C" fn mana_rt_native_bin_parts(
    t: u64,
    out_ptr: *mut *const u8,
    out_len: *mut usize,
) -> u8 {
    match bin_parts(t) {
        Some((p, len)) => {
            unsafe {
                *out_ptr = p;
                *out_len = len;
            }
            1
        }
        None => 0,
    }
}

/// Inspection: write the decimal digits of any integer term (small or
/// bignum) into a caller-provided buffer, snprintf-style — returns the
/// full digit count (which may exceed `cap`; the caller retries with a
/// bigger buffer), or `usize::MAX` if `t` is not an integer. Allocates
/// NOTHING on the process heap, so it is safe to call while walking an
/// unrooted term during JSON encode.
#[no_mangle]
pub extern "C" fn mana_rt_native_int_decimal(t: u64, out: *mut u8, cap: usize) -> usize {
    match int_term_digits(t, 10) {
        Some(s) => {
            let b = s.as_bytes();
            let n = b.len().min(cap);
            unsafe {
                std::ptr::copy_nonoverlapping(b.as_ptr(), out, n);
            }
            b.len()
        }
        None => usize::MAX,
    }
}
