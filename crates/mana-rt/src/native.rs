//! Public ABI for native code. The native/ crate of a hex package calls
//! these symbols, through the mana-native wrapper, to build and inspect
//! terms. They are the ONLY symbols that it calls. The rest of the runtime
//! is private.
//!
//! Terms are tagged u64 values. The first argument is the ProcCtx. This is
//! the codegen contract. Term construction that allocates can start a GC.
//! The caller (the Env of mana-native) roots live terms across allocations.

use super::*;

/// Bump-allocates `words` on the process nursery. This can start a GC.
/// Returns a raw heap pointer. The caller fills it with a header and term
/// words. The caller must read live child terms from its root frame AFTER
/// this call, because a GC can move them.
#[no_mangle]
pub extern "C" fn mana_rt_native_alloc(ctx: *mut ProcCtx, words: u64) -> *mut u64 {
    let ctx = unsafe { &mut *ctx };
    alloc_nursery(ctx, words as usize)
}

/// Builds a binary term from raw bytes. The function copies the bytes. The
/// source is not a term, so the caller does not need to root it.
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

/// Builds an integer term (small or bignum, normalized).
#[no_mangle]
pub extern "C" fn mana_rt_native_make_int(ctx: *mut ProcCtx, v: i64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    make_int_mag(ctx, v < 0, &[v.unsigned_abs()])
}

/// Builds an unsigned integer term (small or bignum). This is for JSON
/// numbers that exceed the i64 range.
#[no_mangle]
pub extern "C" fn mana_rt_native_make_uint(ctx: *mut ProcCtx, v: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    make_int_mag(ctx, false, &[v])
}

/// Builds a boxed float term.
#[no_mangle]
pub extern "C" fn mana_rt_native_make_float(ctx: *mut ProcCtx, v: f64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    box_float(ctx, v)
}

/// Interns an atom from raw bytes. Atoms are eternal, so there is no ctx and
/// no GC.
#[no_mangle]
pub extern "C" fn mana_rt_native_make_atom(ptr: *const u8, len: usize) -> u64 {
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    atom_intern(bytes)
}

/// Raises `badarg` from native code. It sets the exception cells and returns
/// the sentinel. The caller returns that sentinel to unwind.
#[no_mangle]
pub extern "C" fn mana_rt_native_raise_badarg(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &mut *ctx };
    raise_badarg(ctx)
}

/// Inspection. If `t` is a binary or a sub-binary view, writes its current
/// data pointer and length, then returns 1. Otherwise returns 0. It handles
/// the GC-recomputed data pointer of the view, so mana-native does not
/// duplicate that logic.
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

/// Inspection. Writes the decimal digits of an integer term (small or
/// bignum) into a caller-provided buffer, snprintf-style. Returns the full
/// digit count. The count can exceed `cap`. In that case the caller retries
/// with a bigger buffer. Returns `usize::MAX` if `t` is not an integer. It
/// allocates NOTHING on the process heap. So it is safe to call while the
/// caller walks an unrooted term during JSON encode.
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
