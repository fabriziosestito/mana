//! The ABI contract between the mana compiler and the mana runtime.
//!
//! Every constant that both sides must agree on lives here, once: term
//! tags, boxed-object kinds, the `ProcCtx` word offsets, the register count
//! of the uniform calling convention, the exception sentinel, and the
//! opcode tables of the runtime entry points that take an operation code.
//! `mana-rt`, `mana-codegen`, and `mana-native` re-export this crate.
//!
//! A change here changes the emitted code AND the runtime in one commit.
//! The object cache keys on the compiler binary, so a change invalidates
//! every cached object.
//!
//! This crate has no dependencies and no `std` use, so a native package can
//! depend on it without cost.

#![no_std]

// Term tags: the low 3 bits of every 64-bit word.

pub const TAG_MASK: u64 = 0b111;
/// Boxed pointer. The header word holds the kind (low 8 bits) and the size.
pub const TAG_BOXED: u64 = 0b000;
/// Small integer. The value is `word >> 3`.
pub const TAG_SMALL: u64 = 0b001;
/// Atom: a pointer to a static `{ len: u64, bytes }`.
pub const TAG_ATOM: u64 = 0b010;
/// Nil. The whole word is 3.
pub const NIL: u64 = 0b011;
/// Cons cell: a pointer to `[head, tail]`.
pub const TAG_CONS: u64 = 0b100;
/// The exception sentinel. Never a valid term. A function that raises
/// returns this word after it stores the class and the reason in the ctx.
pub const EXC_SENTINEL: u64 = 0b101;
/// Identifier class. Bit 3 selects: pid `id<<4|0110`, ref `id<<4|1110`.
pub const TAG_PID: u64 = 0b110;
pub const PID_TAG4: u64 = 0b0110;
pub const REF_TAG4: u64 = 0b1110;
/// The GC forwarding marker. Never a valid heap header kind.
pub const TAG_FORWARD: u64 = 0b111;

// Boxed-object kinds: the low 8 bits of a header word. Kind 7 is forbidden
// because it collides with `TAG_FORWARD`.

pub const KIND_TUPLE: u64 = 0;
pub const KIND_FLOAT: u64 = 1;
/// `[header | code_ptr | captures...]`. Header bits 8-15 hold the arity,
/// bits 16 and up the capture count.
pub const KIND_FUN: u64 = 2;
/// `[header(limbs<<9 | sign<<8 | 3) | limbs...]`, normalized.
pub const KIND_BIGNUM: u64 = 3;
/// Flatmap: `[header(n<<8 | 4) | k1..kn | v1..vn]`, keys in term order.
pub const KIND_MAP: u64 = 4;
/// Byte binary: `[header(bytes<<8 | 5) | data words]`.
pub const KIND_BIN: u64 = 5;
/// Sub-binary view: `[header(len<<8 | 13) | parent | offset]`. Kinds 5 and
/// 13 differ only in bit 3, so `(kind | 8) == 13` tests for both.
pub const KIND_SUBBIN: u64 = 13;

// `ProcCtx` word offsets. Compiled code reads and writes these words.

/// Nursery bump pointer.
pub const CTX_HEAP_TOP: u64 = 0;
/// Nursery end.
pub const CTX_HEAP_END: u64 = 1;
/// Head of the root-frame chain.
pub const CTX_ROOTS: u64 = 2;
/// Class of the pending exception.
pub const CTX_EXC_CLASS: u64 = 3;
/// Reason of the pending exception.
pub const CTX_EXC_REASON: u64 = 4;
/// Reduction counter.
pub const CTX_REDUCTIONS: u64 = 5;
/// Per-scheduler argument spill for calls with more than `NREG` arguments.
pub const CTX_ARGV_SPILL: u64 = 6;

/// Register arguments of the uniform `tailcc` prototype: `f(ctx, x0..x4)`.
/// With the ctx this fills the six x86-64 SysV integer registers. A compiled
/// function never has a stack parameter.
pub const NREG: usize = 5;
/// Words in the argument spill area behind `CTX_ARGV_SPILL`.
pub const ARGV_SPILL_WORDS: usize = 64;

// Opcode tables. The compiler passes these to runtime entry points that
// take an operation code.

/// `mana_rt_arith(ctx, op, a, b)`.
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

/// `mana_rt_f2i(ctx, mode, x)` and the mode argument of
/// `mana_rt_float_prec(ctx, x, prec, mode)`.
pub const F2I_TRUNC: u64 = 0;
pub const F2I_ROUND: u64 = 1;
pub const F2I_FLOOR: u64 = 2;
pub const F2I_CEIL: u64 = 3;

/// `mana_rt_math(ctx, op, a, b)`.
pub const M_SQRT: u64 = 0;
pub const M_POW: u64 = 1;
pub const M_LOG: u64 = 2;
pub const M_LOG2: u64 = 3;
pub const M_LOG10: u64 = 4;
pub const M_EXP: u64 = 5;
pub const M_SIN: u64 = 6;
pub const M_COS: u64 = 7;
pub const M_TAN: u64 = 8;
pub const M_ASIN: u64 = 9;
pub const M_ACOS: u64 = 10;
pub const M_ATAN: u64 = 11;
pub const M_ATAN2: u64 = 12;
pub const M_FMOD: u64 = 13;
pub const M_PI: u64 = 14;
pub const M_FLOOR: u64 = 15;
pub const M_CEIL: u64 = 16;

/// `mana_rt_crypto(ctx, op, ...)`.
pub const C_RAND: u64 = 0;
pub const C_HASH: u64 = 1;
pub const C_MAC: u64 = 2;
pub const C_EXOR: u64 = 3;
pub const C_PBKDF2: u64 = 4;
pub const C_HASH_EQUALS: u64 = 5;

/// `mana_rt_file(ctx, op, ...)`.
pub const F_READ_FILE: u64 = 0;
pub const F_WRITE_FILE: u64 = 1;
pub const F_WRITE_FILE3: u64 = 2;
pub const F_OPEN: u64 = 3;
pub const F_CLOSE: u64 = 4;
pub const F_READ: u64 = 5;
pub const F_WRITE: u64 = 6;
pub const F_POSITION: u64 = 7;
pub const F_DELETE: u64 = 8;
pub const F_RENAME: u64 = 9;
pub const F_MAKE_DIR: u64 = 10;
pub const F_DEL_DIR: u64 = 11;
pub const F_LIST_DIR: u64 = 12;
pub const F_FILE_INFO: u64 = 13;
pub const F_FILE_INFO2: u64 = 14;
pub const F_COPY: u64 = 15;
pub const F_GET_CWD: u64 = 16;

/// `mana_rt_tcp(ctx, op, ...)`.
pub const T_CONNECT: u64 = 0;
pub const T_LISTEN: u64 = 1;
pub const T_ACCEPT: u64 = 2;
pub const T_RECV: u64 = 3;
pub const T_SEND: u64 = 4;
pub const T_CLOSE: u64 = 5;
pub const T_SHUTDOWN: u64 = 6;
pub const T_SETOPTS: u64 = 7;
pub const T_PEERNAME: u64 = 8;
pub const T_SOCKNAME: u64 = 9;
pub const T_PORT: u64 = 10;
pub const T_CONTROLLING: u64 = 11;
pub const T_GETSTAT: u64 = 12;
pub const T_GETOPTS: u64 = 13;

/// Words in one export-table entry: `{module, function, arity, c_code,
/// fun_code}`.
pub const EXPORT_WORDS: usize = 5;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn forward_tag_is_not_a_kind_and_sentinel_is_not_a_term_tag() {
        for k in [
            KIND_TUPLE,
            KIND_FLOAT,
            KIND_FUN,
            KIND_BIGNUM,
            KIND_MAP,
            KIND_BIN,
            KIND_SUBBIN,
        ] {
            assert_ne!(k & TAG_MASK, TAG_FORWARD);
        }
        assert_ne!(EXC_SENTINEL, TAG_BOXED);
        assert!((KIND_BIN | 8) == KIND_SUBBIN);
    }
}
