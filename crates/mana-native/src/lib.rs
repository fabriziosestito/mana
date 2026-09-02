//! # mana-native
//!
//! The stable term ABI a hex package's `native/<pkg>/` Rust crate depends
//! on to build and inspect mana terms — the closed-world analog of the
//! `rustler` crate. A native function has the signature
//!
//! ```ignore
//! #[no_mangle]
//! pub extern "C" fn my_pkg_native_hello_1(ctx: *mut ProcCtx, arg0: u64) -> u64 { ... }
//! ```
//!
//! Terms are tagged 64-bit words (`u64`). `ProcCtx` is opaque here (only
//! its first words matter, and only to the runtime). Read arguments with
//! the [`Term`] inspection API; build results with an [`Env`], which roots
//! every term it creates across allocations (mana's GC moves objects, so —
//! unlike a BEAM NIF's `ErlNifEnv` — you must not hold a raw term across an
//! allocation without rooting it; `Env` does that for you).

#![allow(clippy::missing_safety_doc)]

/// Opaque process context handle. Only the runtime interprets its fields;
/// the ABI treats it as a pointer. Its word 2 is the GC root-chain head,
/// which [`Env`] manipulates.
#[repr(C)]
pub struct ProcCtx {
    _private: [u64; 0],
}

// -- tag / kind constants (mirror crates/mana-rt/src/lib.rs) --
pub const TAG_MASK: u64 = 0b111;
pub const TAG_BOXED: u64 = 0b000;
pub const TAG_SMALL: u64 = 0b001;
pub const TAG_ATOM: u64 = 0b010;
pub const NIL: u64 = 0b011;
pub const TAG_CONS: u64 = 0b100;

pub const KIND_TUPLE: u64 = 0;
pub const KIND_FLOAT: u64 = 1;
pub const KIND_BIGNUM: u64 = 3;
pub const KIND_MAP: u64 = 4;
pub const KIND_BIN: u64 = 5;
pub const KIND_SUBBIN: u64 = 13;

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

/// The sentinel a native fn returns to unwind (raise) — matches codegen.
pub const EXC_SENTINEL: u64 = 0b101;

/// Raise `badarg`; return the result of this to unwind out of the native fn.
#[inline]
pub fn raise_badarg(ctx: *mut ProcCtx) -> u64 {
    unsafe { mana_rt_native_raise_badarg(ctx) }
}

// ---------------------------------------------------------------------------
// Inspection (read-only, never allocates — safe on an unrooted argument as
// long as no allocation happens between reads).

/// A borrowed view of a term for inspection. Cheap (`Copy`), just the word.
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
    /// Boxed-object kind byte, or `None` if not boxed.
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

    /// Atom name bytes (interned, static). Precondition: `is_atom()`.
    #[inline]
    pub fn atom_name(self) -> &'static [u8] {
        unsafe {
            let p = (self.0 & !TAG_MASK) as *const u64;
            let len = *p as usize;
            std::slice::from_raw_parts(p.add(1) as *const u8, len)
        }
    }

    /// Float value. Precondition: `is_float()`.
    #[inline]
    pub fn as_float(self) -> f64 {
        unsafe { f64::from_bits(*((self.0 as *const u64).add(1))) }
    }

    /// Binary/sub-binary bytes (view data pointer is GC-recomputed by the
    /// runtime). Returns `None` if not a binary. The slice borrows the
    /// process heap — copy out before any allocation.
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

    /// Decimal digits of an integer term into `buf`; returns the digit
    /// count (may exceed `buf.len()` — retry with a bigger buffer), or
    /// `None` if not an integer. Allocates nothing.
    #[inline]
    pub fn int_decimal(self, buf: &mut [u8]) -> Option<usize> {
        let n = unsafe { mana_rt_native_int_decimal(self.0, buf.as_mut_ptr(), buf.len()) };
        if n == usize::MAX {
            None
        } else {
            Some(n)
        }
    }

    // -- containers (raw reads; no allocation) --

    /// Tuple arity. Precondition: `is_tuple()`.
    #[inline]
    pub fn tuple_arity(self) -> usize {
        (unsafe { *(self.0 as *const u64) } >> 8) as usize
    }
    /// 0-based tuple element. Precondition: `is_tuple()` and `i < arity`.
    #[inline]
    pub fn tuple_elem(self, i: usize) -> Term {
        Term(unsafe { *((self.0 as *const u64).add(1 + i)) })
    }
    /// Cons head. Precondition: `is_cons()`.
    #[inline]
    pub fn cons_head(self) -> Term {
        Term(unsafe { *((self.0 & !TAG_MASK) as *const u64) })
    }
    /// Cons tail. Precondition: `is_cons()`.
    #[inline]
    pub fn cons_tail(self) -> Term {
        Term(unsafe { *((self.0 & !TAG_MASK) as *const u64).add(1) })
    }
    /// Map size. Precondition: `is_map()`.
    #[inline]
    pub fn map_size(self) -> usize {
        (unsafe { *(self.0 as *const u64) } >> 8) as usize
    }
    /// 0-based map key (keys are stored sorted). Precondition: `is_map()`.
    #[inline]
    pub fn map_key(self, i: usize) -> Term {
        Term(unsafe { *((self.0 as *const u64).add(1 + i)) })
    }
    /// 0-based map value (parallel to keys). Precondition: `is_map()`.
    #[inline]
    pub fn map_val(self, i: usize) -> Term {
        let n = self.map_size();
        Term(unsafe { *((self.0 as *const u64).add(1 + n + i)) })
    }
}

// ---------------------------------------------------------------------------
// Construction with rooting (the ErlNifEnv analog).

/// A handle to a term rooted in an [`Env`]. Stays valid (its value tracked
/// across GC moves) until the `Env` is dropped.
#[derive(Clone, Copy)]
pub struct H(usize);

/// A rooting scope for building terms. Every term created through it is
/// pushed onto the process GC root chain, so intermediate results survive
/// the allocations of later builds. Restores the previous root head on drop.
pub struct Env {
    ctx: *mut ProcCtx,
    // [prev_root_head, slot_count, slot0, slot1, ...]
    roots: Vec<u64>,
}

impl Env {
    /// # Safety
    /// `ctx` must be the live process context passed to the native fn.
    pub unsafe fn new(ctx: *mut ProcCtx) -> Env {
        let prev = *(ctx as *const u64).add(2); // roots_head (word 2)
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
        self.install(); // re-point in case the Vec reallocated
        H(self.roots.len() - 1)
    }

    /// Current value of a handle (re-read from its root slot — always the
    /// post-GC location).
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
        // read children AFTER the alloc (GC may have moved them; their
        // root slots were updated in place)
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
                *p.add(1 + i) = self.get(e); // fresh read, no alloc between
            }
        }
        self.track(p as u64) // TAG_BOXED == 0
    }

    /// A map from key/value handle pairs. Keys are sorted and de-duplicated
    /// by the runtime (`maps:from_list` semantics: last value wins).
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
