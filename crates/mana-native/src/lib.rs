//! # mana-native
//!
//! This crate is the stable term ABI for the `native/<pkg>/` Rust crate of
//! a hex package. The crate builds and inspects mana terms. It is the
//! closed-world analog of the `rustler` crate. A native function has this
//! signature:
//!
//! ```ignore
//! #[no_mangle]
//! pub extern "C" fn my_pkg_native_hello_1(ctx: *mut ProcCtx, arg0: u64) -> u64 { ... }
//! ```
//!
//! Terms are tagged 64-bit words (`u64`). `ProcCtx` is opaque here. Only
//! its first words matter, and only to the runtime. Read arguments with the
//! [`Term`] inspection API. Build results with an [`Env`]. The `Env` roots
//! every term that it creates across allocations. The mana GC moves
//! objects. This differs from the `ErlNifEnv` of a BEAM NIF. You must not
//! hold a raw term across an allocation without a root. `Env` does the
//! rooting for you.

#![allow(clippy::missing_safety_doc)]

/// The opaque process context handle. Only the runtime interprets its
/// fields. The ABI treats it as a pointer. Its word 2 is the head of the GC
/// root chain. [`Env`] changes this word.
#[repr(C)]
pub struct ProcCtx {
    _private: [u64; 0],
}

// The term tags, kinds, and the exception sentinel come from the shared
// `mana-abi` crate, the same source that the compiler and the runtime use.
pub use mana_abi::*;

extern "C" {
    fn mana_rt_native_alloc(ctx: *mut ProcCtx, words: u64) -> *mut u64;
    fn mana_rt_native_make_binary(ctx: *mut ProcCtx, ptr: *const u8, len: usize) -> u64;
    fn mana_rt_native_make_int(ctx: *mut ProcCtx, v: i64) -> u64;
    fn mana_rt_native_make_uint(ctx: *mut ProcCtx, v: u64) -> u64;
    fn mana_rt_native_make_float(ctx: *mut ProcCtx, v: f64) -> u64;
    fn mana_rt_native_make_atom(ptr: *const u8, len: usize) -> u64;
    fn mana_rt_native_raise_badarg(ctx: *mut ProcCtx) -> u64;
    fn mana_rt_native_bin_parts(t: u64, out_ptr: *mut *const u8, out_len: *mut usize) -> u8;
    fn mana_rt_native_int_decimal(t: u64, out: *mut u8, cap: usize) -> usize;
    fn mana_rt_map_from_list(ctx: *mut ProcCtx, list: u64) -> u64;
}

/// Raise `badarg`. Return the result of this call to unwind out of the
/// native fn.
#[inline]
pub fn raise_badarg(ctx: *mut ProcCtx) -> u64 {
    unsafe { mana_rt_native_raise_badarg(ctx) }
}

// Inspection. These reads never allocate. They are safe on an unrooted
// argument as long as no allocation happens between the reads.

/// A borrowed view of a term for inspection. It is `Copy` and holds only
/// the word.
#[derive(Clone, Copy)]
pub struct Term(pub u64);

impl Term {
    #[inline]
    pub fn is_small(self) -> bool {
        self.0 & TAG_MASK == TAG_SMALL
    }
    #[inline]
    pub fn as_small(self) -> i64 {
        (self.0 as i64) >> 3
    }
    #[inline]
    pub fn is_atom(self) -> bool {
        self.0 & TAG_MASK == TAG_ATOM
    }
    #[inline]
    pub fn is_nil(self) -> bool {
        self.0 == NIL
    }
    #[inline]
    pub fn is_cons(self) -> bool {
        self.0 & TAG_MASK == TAG_CONS
    }
    #[inline]
    pub fn is_boxed(self) -> bool {
        self.0 & TAG_MASK == TAG_BOXED && self.0 != 0
    }
    /// The kind byte of a boxed object, or `None` if the term is not boxed.
    #[inline]
    pub fn boxed_kind(self) -> Option<u64> {
        if self.is_boxed() {
            Some(unsafe { *(self.0 as *const u64) } & 0xff)
        } else {
            None
        }
    }
    pub fn is_float(self) -> bool {
        self.boxed_kind() == Some(KIND_FLOAT)
    }
    pub fn is_bignum(self) -> bool {
        self.boxed_kind() == Some(KIND_BIGNUM)
    }
    pub fn is_integer(self) -> bool {
        self.is_small() || self.is_bignum()
    }
    pub fn is_map(self) -> bool {
        self.boxed_kind() == Some(KIND_MAP)
    }
    pub fn is_tuple(self) -> bool {
        self.boxed_kind() == Some(KIND_TUPLE)
    }

    /// The atom name bytes. They are interned and static. Precondition:
    /// `is_atom()`.
    #[inline]
    pub fn atom_name(self) -> &'static [u8] {
        unsafe {
            let p = (self.0 & !TAG_MASK) as *const u64;
            let len = *p as usize;
            std::slice::from_raw_parts(p.add(1) as *const u8, len)
        }
    }

    /// The float value. Precondition: `is_float()`.
    #[inline]
    pub fn as_float(self) -> f64 {
        unsafe { f64::from_bits(*((self.0 as *const u64).add(1))) }
    }

    /// The bytes of a binary or sub-binary. The runtime recomputes the data
    /// pointer of a view after GC. Returns `None` if the term is not a
    /// binary. The slice borrows the process heap. Copy the bytes out before
    /// any allocation.
    #[inline]
    pub fn binary_bytes(self) -> Option<&'static [u8]> {
        let mut ptr: *const u8 = std::ptr::null();
        let mut len: usize = 0;
        if unsafe { mana_rt_native_bin_parts(self.0, &mut ptr, &mut len) } == 1 {
            Some(unsafe { std::slice::from_raw_parts(ptr, len) })
        } else {
            None
        }
    }

    /// Write the decimal digits of an integer term into `buf`. Returns the
    /// digit count, or `None` if the term is not an integer. The count can
    /// exceed `buf.len()`. In that case, retry with a bigger buffer. This
    /// call allocates nothing.
    #[inline]
    pub fn int_decimal(self, buf: &mut [u8]) -> Option<usize> {
        let n = unsafe { mana_rt_native_int_decimal(self.0, buf.as_mut_ptr(), buf.len()) };
        if n == usize::MAX {
            None
        } else {
            Some(n)
        }
    }

    // Containers. These are raw reads with no allocation.

    /// The tuple arity. Precondition: `is_tuple()`.
    #[inline]
    pub fn tuple_arity(self) -> usize {
        (unsafe { *(self.0 as *const u64) } >> 8) as usize
    }
    /// The 0-based tuple element. Precondition: `is_tuple()` and `i < arity`.
    #[inline]
    pub fn tuple_elem(self, i: usize) -> Term {
        Term(unsafe { *((self.0 as *const u64).add(1 + i)) })
    }
    /// The cons head. Precondition: `is_cons()`.
    #[inline]
    pub fn cons_head(self) -> Term {
        Term(unsafe { *((self.0 & !TAG_MASK) as *const u64) })
    }
    /// The cons tail. Precondition: `is_cons()`.
    #[inline]
    pub fn cons_tail(self) -> Term {
        Term(unsafe { *((self.0 & !TAG_MASK) as *const u64).add(1) })
    }
    /// The map size. Precondition: `is_map()`.
    #[inline]
    pub fn map_size(self) -> usize {
        (unsafe { *(self.0 as *const u64) } >> 8) as usize
    }
    /// The 0-based map key. The keys are stored in sorted order.
    /// Precondition: `is_map()`.
    #[inline]
    pub fn map_key(self, i: usize) -> Term {
        Term(unsafe { *((self.0 as *const u64).add(1 + i)) })
    }
    /// The 0-based map value. The values are parallel to the keys.
    /// Precondition: `is_map()`.
    #[inline]
    pub fn map_val(self, i: usize) -> Term {
        let n = self.map_size();
        Term(unsafe { *((self.0 as *const u64).add(1 + n + i)) })
    }
}

// Construction with rooting. This is the analog of ErlNifEnv.

/// A handle to a term that is rooted in an [`Env`]. The handle stays valid
/// until the `Env` is dropped. The `Env` tracks its value across GC moves.
#[derive(Clone, Copy)]
pub struct H(usize);

/// A rooting scope for term construction. The scope pushes every term that
/// it creates onto the GC root chain of the process. Then intermediate
/// results survive the allocations of later builds. On drop, the scope
/// restores the previous root head.
pub struct Env {
    ctx: *mut ProcCtx,
    // Layout: [prev_root_head, slot_count, slot0, slot1, ...]
    roots: Vec<u64>,
}

impl Env {
    /// # Safety
    /// `ctx` must be the live process context that the runtime passed to the
    /// native fn.
    pub unsafe fn new(ctx: *mut ProcCtx) -> Env {
        let prev = *(ctx as *const u64).add(2); // roots_head is word 2.
        let mut e = Env {
            ctx,
            roots: vec![prev, 0],
        };
        e.install();
        e
    }

    #[inline]
    fn install(&mut self) {
        let n = (self.roots.len() - 2) as u64;
        self.roots[1] = n;
        unsafe {
            *(self.ctx as *mut u64).add(2) = self.roots.as_ptr() as u64;
        }
    }

    #[inline]
    fn track(&mut self, t: u64) -> H {
        self.roots.push(t);
        self.install(); // The Vec can reallocate. Point the runtime at the new buffer.
        H(self.roots.len() - 1)
    }

    /// The current value of a handle. The read comes from its root slot, so
    /// it is always the location after GC.
    #[inline]
    pub fn get(&self, h: H) -> u64 {
        self.roots[h.0]
    }

    /// A tracked handle for `nil` (the immediate empty list).
    pub fn nil(&mut self) -> H {
        self.track(NIL)
    }
    pub fn int(&mut self, v: i64) -> H {
        let t = unsafe { mana_rt_native_make_int(self.ctx, v) };
        self.track(t)
    }
    pub fn uint(&mut self, v: u64) -> H {
        let t = unsafe { mana_rt_native_make_uint(self.ctx, v) };
        self.track(t)
    }
    pub fn float(&mut self, v: f64) -> H {
        let t = unsafe { mana_rt_native_make_float(self.ctx, v) };
        self.track(t)
    }
    pub fn binary(&mut self, bytes: &[u8]) -> H {
        let t = unsafe { mana_rt_native_make_binary(self.ctx, bytes.as_ptr(), bytes.len()) };
        self.track(t)
    }
    pub fn atom(&mut self, name: &[u8]) -> H {
        let t = unsafe { mana_rt_native_make_atom(name.as_ptr(), name.len()) };
        self.track(t)
    }

    /// Prepend `head` to `tail`.
    pub fn cons(&mut self, head: H, tail: H) -> H {
        let p = unsafe { mana_rt_native_alloc(self.ctx, 2) };
        // Read the children AFTER the alloc. The GC can move them. Their
        // root slots were updated in place.
        let (h, tl) = (self.get(head), self.get(tail));
        unsafe {
            *p = h;
            *p.add(1) = tl;
        }
        self.track(p as u64 | TAG_CONS)
    }

    /// A proper list of the given elements.
    pub fn list(&mut self, elems: &[H]) -> H {
        let mut acc = self.nil();
        for &e in elems.iter().rev() {
            acc = self.cons(e, acc);
        }
        acc
    }

    /// A tuple of the given elements.
    pub fn tuple(&mut self, elems: &[H]) -> H {
        let n = elems.len();
        let p = unsafe { mana_rt_native_alloc(self.ctx, 1 + n as u64) };
        unsafe {
            *p = ((n as u64) << 8) | KIND_TUPLE;
            for (i, &e) in elems.iter().enumerate() {
                *p.add(1 + i) = self.get(e); // A fresh read. No alloc happens between.
            }
        }
        self.track(p as u64) // TAG_BOXED == 0
    }

    /// A map from key/value handle pairs. The runtime sorts the keys and
    /// removes duplicates. The semantics are those of `maps:from_list`: the
    /// last value wins.
    pub fn map(&mut self, pairs: &[(H, H)]) -> H {
        let tuples: Vec<H> = pairs.iter().map(|&(k, v)| self.tuple(&[k, v])).collect();
        let list = self.list(&tuples);
        let m = unsafe { mana_rt_map_from_list(self.ctx, self.get(list)) };
        self.track(m)
    }
}

impl Drop for Env {
    fn drop(&mut self) {
        unsafe {
            *(self.ctx as *mut u64).add(2) = self.roots[0];
        }
    }
}
