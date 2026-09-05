//! Term representation and the shared runtime tables. This module holds the
//! tag and kind constants, the heap and stack size constants, the raw memory
//! primitives, the atom table, and the term helpers for order and numbers.
//! The tag and kind bit patterns are the ABI contract with the compiler.
//! They must match mana-codegen bit for bit.

use super::*;

pub const TAG_MASK: u64 = 0b111;

pub const TAG_BOXED: u64 = 0b000;

pub const TAG_SMALL: u64 = 0b001;

pub const TAG_ATOM: u64 = 0b010;

pub const NIL: u64 = 0b011;

pub const TAG_CONS: u64 = 0b100;

/// Identifier class. Bit 3 selects the kind: a pid is `id<<4|0110`, a ref
/// is `id<<4|1110`. Both are immediates. Raw-word equality compares them,
/// and the GC does not touch them.
pub const TAG_PID: u64 = 0b110;

pub const PID_TAG4: u64 = 0b0110;

pub const REF_TAG4: u64 = 0b1110;

pub const TAG_FORWARD: u64 = 0b111;

/// This value must match the exception sentinel of mana-codegen (tag 0b101).
pub(crate) const EXC_SENTINEL: u64 = 0b101;

pub const KIND_TUPLE: u64 = 0;

pub const KIND_FLOAT: u64 = 1;

/// Fun object: `[header | code_ptr | captured terms...]`.
/// Header layout: bits 0-7 hold the kind, bits 8-15 hold the arity, and
/// bits 16 and up hold the number of captures.
pub const KIND_FUN: u64 = 2;

/// Flatmap: `[header(size<<8|4) | k1..kn | v1..vn]`. The keys are sorted in
/// canonical term order. Exactness breaks ties: 1 sorts before 1.0.
pub const KIND_MAP: u64 = 4;

pub const KIND_BIN: u64 = 5;

/// Real bignum: `[header(limbs<<9 | sign<<8 | 3) | limbs (LE u64)...]`.
/// The value is normalized: it never fits the 61-bit small range, and it
/// has no leading zero limbs. A set sign bit means negative. The runtime
/// allocates bignums in the SHARED OLD SPACE with alloc_shared. That
/// allocation is a pure bump and never a GC point, so arithmetic keeps its
/// no-frame fast paths. A bignum has no term fields. The GC copies the
/// limbs verbatim.
pub const KIND_BIGNUM: u64 = 3;

/// Sub-binary view: `[header(len<<8|13) | parent_term | byte_offset]`. It
/// is a zero-copy slice of a ROOT KIND_BIN, never of another view. A slice
/// of a view folds the offsets.
///
/// The header convention is the same as KIND_BIN, so the inline length
/// preflight works for both. Kinds 5 (0b0101) and 13 (0b1101) differ only
/// in bit 3, so `(kind | 8) == 13` accepts either. Kind 7 is FORBIDDEN for
/// heap objects: header low bits 0b111 collide with the TAG_FORWARD marker
/// of the GC.
///
/// The parent is a TERM and moves under GC. Every access recomputes the
/// data pointer. The pointer is never cached.
pub const KIND_SUBBIN: u64 = 13;

pub(crate) const NURSERY_WORDS: usize = 16 * 1024; // 128 KiB

/// MANA_NURSERY_WORDS overrides the initial nursery size AND pins it.
/// Adaptive growth is then disabled. This is a GC-stress knob that finds
/// rooting bugs: a tiny nursery makes every allocation path meet constant
/// minor collections.
pub(crate) fn nursery_words_override() -> Option<usize> {
    std::env::var("MANA_NURSERY_WORDS").ok()?.parse().ok()
}

pub(crate) fn initial_nursery_words() -> usize {
    nursery_words_override().unwrap_or(NURSERY_WORDS)
}

pub(crate) const OLD_CHUNK_WORDS: usize = 64 * 1024;

pub(crate) const OLD_LIMIT_INIT: usize = 4 * OLD_CHUNK_WORDS;

/// This is a reservation only. Anonymous pages commit lazily on the first
/// touch.
pub(crate) const STACK_BYTES: usize = 256 * 1024 * 1024; // TODO(stacks): make the stack growable

/// This is a reservation only. Anonymous pages commit lazily on the first
/// touch.
pub(crate) const ROOT_STACK_BYTES: usize = 512 * 1024 * 1024;

pub(crate) const REDUCTIONS_PER_SLICE: i64 = 4000;

/// Uniform compiled ABI: every call passes `ctx + ABI_REGS` term words.
/// Arguments past ABI_REGS-1 travel through `ProcCtx::argv_spill` (see
/// codegen NREG).
pub(crate) const ABI_REGS: usize = 5;

pub(crate) const ARGV_SPILL_WORDS: usize = 64;

// Memory primitives

pub(crate) struct Chunk {
    pub(crate) start: *mut u64,
    pub(crate) top: *mut u64,
    pub(crate) end: *mut u64,
    pub(crate) words: usize,
}

unsafe impl Send for Chunk {}

pub(crate) fn alloc_space(words: usize) -> *mut u64 {
    let layout = std::alloc::Layout::from_size_align(words * 8, 8).expect("bad heap size");
    let p = unsafe { std::alloc::alloc(layout) } as *mut u64;
    if p.is_null() {
        eprintln!("mana: out of memory");
        std::process::exit(70);
    }
    p
}

pub(crate) unsafe fn free_space(p: *mut u64, words: usize) {
    let layout = std::alloc::Layout::from_size_align(words * 8, 8).unwrap();
    unsafe { std::alloc::dealloc(p as *mut u8, layout) };
}

pub(crate) fn payload_words(header: u64) -> usize {
    match header & 0xff {
        KIND_TUPLE => (header >> 8) as usize,
        KIND_FLOAT => 1,
        KIND_FUN => 1 + (header >> 16) as usize,
        KIND_MAP => 2 * (header >> 8) as usize,
        KIND_BIN => ((header >> 8) as usize + 7) / 8,
        KIND_SUBBIN => 2, // parent term and byte offset. The length lives in the header.
        KIND_BIGNUM => (header >> 9) as usize,
        _ => 0,
    }
}

pub(crate) fn make_pid(id: usize) -> u64 {
    ((id as u64) << 4) | PID_TAG4
}

pub(crate) fn pid_id(t: u64) -> Option<usize> {
    (t & 0xF == PID_TAG4).then_some((t >> 4) as usize)
}

/// Well-known atom terms that the generated main registers at start. The
/// runtime reads them here instead of a table lookup on every use.
#[derive(Default)]
pub(crate) struct KnownAtoms {
    pub(crate) normal: u64,
    pub(crate) killed: u64,
    pub(crate) kill: u64,
    pub(crate) exit_up: u64,   // 'EXIT'
    pub(crate) down_up: u64,   // 'DOWN'
    pub(crate) process: u64,
    pub(crate) noproc: u64,
    pub(crate) true_a: u64,
    pub(crate) false_a: u64,
    pub(crate) badarg: u64,
    pub(crate) error_a: u64,
    pub(crate) badmap: u64,
    pub(crate) badkey: u64,
    pub(crate) undef: u64,
    pub(crate) ok: u64,
    pub(crate) module: u64,
    pub(crate) nofile: u64,
    pub(crate) value: u64,
    pub(crate) undefined: u64,
    pub(crate) badarith: u64,
}

pub(crate) static KNOWN: std::sync::OnceLock<KnownAtoms> = std::sync::OnceLock::new();

pub(crate) fn known() -> &'static KnownAtoms {
    KNOWN.get().expect("atom table not registered")
}

/// The generated main calls this function before mana_rt_run.
#[no_mangle]
pub extern "C" fn mana_rt_register_atoms(
    normal: u64,
    killed: u64,
    kill: u64,
    exit_up: u64,
    down_up: u64,
    process: u64,
    noproc: u64,
    true_a: u64,
    false_a: u64,
    badarg: u64,
    error_a: u64,
    badmap: u64,
    badkey: u64,
    undef: u64,
    ok: u64,
    module: u64,
    nofile: u64,
    value: u64,
    undefined: u64,
    badarith: u64,
) {
    let _ = KNOWN.set(KnownAtoms {
        normal,
        killed,
        kill,
        exit_up,
        down_up,
        process,
        noproc,
        true_a,
        false_a,
        badarg,
        error_a,
        badmap,
        badkey,
        undef,
        ok,
        module,
        nofile,
        value,
        undefined,
        badarith,
    });
}

pub(crate) fn make_ref_term() -> u64 {
    ((REF_COUNTER.fetch_add(1, Ordering::Relaxed) as u64) << 4) | REF_TAG4
}

pub(crate) fn in_my_nursery(ctx: &ProcCtx, addr: u64) -> bool {
    let start = ctx.nursery_start as u64;
    addr >= start && addr < start + (ctx.nursery_words as u64) * 8
}

pub(crate) fn atom_exists(name: &[u8]) -> bool {
    atom_table_lock().read().unwrap().contains_key(name)
}

// Term order, equality, list and tuple helpers

pub(crate) fn atom_bytes(t: u64) -> &'static [u8] {
    unsafe {
        let p = (t & !TAG_MASK) as *const u64;
        let len = *p as usize;
        std::slice::from_raw_parts(p.add(1) as *const u8, len)
    }
}

/// Erlang type rank: number < atom < ref < fun < pid < tuple < map < nil
/// < list < bitstring.
pub(crate) fn type_rank(t: u64) -> u8 {
    match t & TAG_MASK {
        TAG_SMALL => 0,
        TAG_ATOM => 1,
        _ if t == NIL => 7,
        TAG_CONS => 8,
        TAG_PID => {
            if t & 0xF == PID_TAG4 {
                4
            } else {
                2 // ref
            }
        }
        TAG_BOXED => {
            let header = unsafe { *(t as *const u64) };
            match header & 0xff {
                KIND_FLOAT => 0,
                KIND_FUN => 3,
                KIND_MAP => 6,
                KIND_BIN | KIND_SUBBIN => 9,
                KIND_BIGNUM => 0, // numbers
                _ => 5, // tuple
            }
        }
        _ => 10,
    }
}

pub(crate) fn num_val(t: u64) -> f64 {
    if t & TAG_MASK == TAG_SMALL {
        return ((t as i64) >> 3) as f64;
    }
    if let Some((neg, mag)) = bignum_parts(t) {
        let v = bigint::mag_to_f64(mag);
        return if neg { -v } else { v };
    }
    f64::from_bits(unsafe { *(t as *const u64).add(1) })
}

/// Raise-site notifier (MANA_DEBUG_RAISE). It names the function that
/// raised and prints the reason term. This is the debugging stand-in for
/// stacktraces.
#[no_mangle]
pub extern "C" fn mana_rt_note_raise(msg: *const u8, len: u64, reason: u64) {
    if std::env::var_os("MANA_DEBUG_RAISE").is_some() {
        let m = unsafe { std::slice::from_raw_parts(msg, len as usize) };
        let mut r = String::new();
        write_term(reason, &mut r);
        eprintln!("mana: raise in {}: {}", String::from_utf8_lossy(m), r);
    }
}

/// Inline badarg raise notifier (MANA_DEBUG_BADARG).
#[no_mangle]
pub extern "C" fn mana_rt_note_badarg(msg: *const u8, len: u64) {
    if std::env::var_os("MANA_DEBUG_BADARG").is_some() {
        let m = unsafe { std::slice::from_raw_parts(msg, len as usize) };
        eprintln!("mana: badarg raised in {}", String::from_utf8_lossy(m));
    }
}

/// The program called a stubbed function for an unsupported construct.
#[no_mangle]
pub extern "C" fn mana_rt_unsupported(msg: *const u8, len: u64) -> ! {
    let m = unsafe { std::slice::from_raw_parts(msg, len as usize) };
    eprintln!(
        "mana: reached an unsupported construct: {}",
        String::from_utf8_lossy(m)
    );
    std::process::exit(1)
}

/// Sets exc and returns the sentinel. This is the raising-BIF convention:
/// codegen treats these helpers exactly like may-raise calls.
pub(crate) fn raise_badarg(ctx: &mut ProcCtx) -> u64 {
    if std::env::var_os("MANA_DEBUG_BADARG").is_some() {
        eprintln!(
            "mana: badarg raised at:\n{}",
            std::backtrace::Backtrace::force_capture()
        );
    }
    ctx.exc_class = atom_error();
    ctx.exc_reason = known().badarg;
    EXC_SENTINEL
}

pub(crate) fn atom_error() -> u64 {
    known().error_a
}

/// Allocates in the nursery of this scheduler. If the nursery is full, it
/// takes the slow path.
pub(crate) fn alloc_nursery(ctx: &mut ProcCtx, words: usize) -> *mut u64 {
    unsafe {
        if ctx.heap_top.add(words) <= ctx.heap_end {
            let p = ctx.heap_top;
            ctx.heap_top = ctx.heap_top.add(words);
            p
        } else {
            mana_rt_alloc_slow(ctx, words as u64)
        }
    }
}

/// Well-known atoms by name. The generated main registers them with the
/// rest.
pub(crate) fn atom_by_name(name: &str) -> u64 {
    let k = known();
    match name {
        "badmap" => k.badmap,
        "badkey" => k.badkey,
        "value" => k.value,
        other => panic!("atom_by_name: '{}' is not registered", other),
    }
}

// Closed-world atom table. Codegen plants one pointer per atom static in
// the `mana_atoms` ELF section. The linker deduplicates them (linkonce_odr)
// and provides the __start/__stop bounds. Every program registers the
// well-known atoms, so the section is never empty.
extern "C" {
    static __start_mana_atoms: u64;
    static __stop_mana_atoms: u64;
}

pub(crate) type AtomTable = std::sync::RwLock<rustc_hash::FxHashMap<&'static [u8], u64>>;

pub(crate) fn atom_table_lock() -> &'static AtomTable {
    static TABLE: std::sync::OnceLock<AtomTable> = std::sync::OnceLock::new();
    TABLE.get_or_init(|| {
        let mut map = rustc_hash::FxHashMap::default();
        unsafe {
            let start = &raw const __start_mana_atoms;
            let stop = &raw const __stop_mana_atoms;
            let n = (stop as usize - start as usize) / 8;
            for i in 0..n {
                // Each entry is a raw pointer to an atom struct.
                let p = *start.add(i);
                if p != 0 {
                    let atom = p | TAG_ATOM;
                    map.insert(atom_bytes(atom), atom);
                }
            }
        }
        std::sync::RwLock::new(map)
    })
}

/// Looks up an existing atom by its name bytes.
pub(crate) fn atom_lookup(bytes: &[u8]) -> Option<u64> {
    atom_table_lock().read().unwrap().get(bytes).copied()
}

/// Gets an atom, or mints it. A minted atom is an eternal {len, bytes}
/// struct in the SAME table, so pointer identity (raw =:=) holds for the
/// whole program. This gives BEAM parity for list_to_atom/binary_to_atom.
/// The table can grow at runtime but never shrinks. BEAM does the same.
pub(crate) fn atom_intern(bytes: &[u8]) -> u64 {
    if let Some(a) = atom_lookup(bytes) {
        return a;
    }
    let mut map = atom_table_lock().write().unwrap();
    if let Some(&a) = map.get(bytes) {
        return a;
    }
    let words = 1 + (bytes.len() + 7) / 8;
    let p = alloc_space(words);
    unsafe {
        *p = bytes.len() as u64;
        if bytes.len() % 8 != 0 {
            *p.add(words - 1) = 0;
        }
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), p.add(1) as *mut u8, bytes.len());
    }
    let atom = (p as u64) | TAG_ATOM;
    let key: &'static [u8] = Box::leak(bytes.to_vec().into_boxed_slice());
    map.insert(key, atom);
    atom
}

/// Finds any atom compiled into the program, by name. The closed-world
/// table is complete. A miss means that the runtime tried to mint a new
/// atom.
pub(crate) fn find_atom(name: &str) -> Option<u64> {
    atom_lookup(name.as_bytes())
}

/// BEAM treats the exit reasons normal, shutdown, and {shutdown, _} as
/// orderly termination. It logs nothing for them.
pub(crate) fn exit_reason_is_quiet(r: u64) -> bool {
    if r == known().normal {
        return true;
    }
    if r & TAG_MASK == TAG_ATOM {
        return atom_bytes(r) == b"shutdown";
    }
    if r & TAG_MASK == TAG_BOXED && r != 0 {
        let header = unsafe { *(r as *const u64) };
        if header & 0xff == KIND_TUPLE && (header >> 8) == 2 {
            let first = unsafe { *(r as *const u64).add(1) };
            return first & TAG_MASK == TAG_ATOM && atom_bytes(first) == b"shutdown";
        }
    }
    false
}

pub(crate) fn interned_atom_count() -> u64 {
    atom_table_lock().read().map(|m| m.len() as u64).unwrap_or(0)
}
