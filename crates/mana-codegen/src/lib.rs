//! LLVM codegen for the sequential Core Erlang subset.
//!
//! Term representation matches mana-rt (see its crate docs): i64 words,
//! 3-bit tags — 001 small int, 010 atom ptr, 011 nil, 100 cons ptr,
//! 000 boxed ptr (kinds: 0 tuple, 1 float, 2 fun). Tag 111 is the GC
//! forwarding marker, never visible here.
//!
//! # Process-context ABI
//!
//! Every compiled function takes `ctx: ptr` (mana-rt's `ProcCtx`) as its
//! first argument. Codegen touches ctx only at word offset 2 (`roots_head`)
//! for the root-frame chain; allocation goes through `mana_rt_alloc(ctx, n)`
//! which may run a moving collection.
//!
//! # GC roots — effect analysis + frames + spills
//!
//! A term held in an SSA register is invalid after any *GC point* (a call
//! into compiled code that may allocate, or an allocation). Three layers
//! keep this sound without paying where it doesn't matter:
//!
//! 1. Whole-program **may-GC analysis** (fixpoint over the call graph):
//!    functions whose bodies can't reach an allocation get **no frame and
//!    no spills** — pure register code (fib stays fast).
//! 2. Framed functions alloca a root frame `[prev, len, slots...]`, link it
//!    into `ctx.roots_head` on entry and unlink before every return
//!    (including before tail calls). Slots are NIL-initialized; all named
//!    variables live in slots; reads load, binds store.
//! 3. Intermediates are spilled **structurally**: a sibling value is rooted
//!    only if a later sibling's evaluation contains a GC point; children of
//!    an allocation (tuple/cons/closure) are always rooted because the
//!    allocation itself is a GC point. Call arguments consumed by a callee
//!    need no rooting across that call (the callee roots its own params).
//!    TODO(liveness): per-variable liveness to shrink frames further.
//!
//! A program is one or more Core Erlang modules compiled to one object file
//! per module. Atoms are `linkonce_odr` globals (linker-deduplicated,
//! static, never collected). Closures are lambda-lifted in closure-passing
//! style: lifted signature `(ctx, args..., closure)`.
//!
//! Tail calls are guaranteed: uniform `tailcc` prototype + `musttail` (see NREG).

use std::cell::{Cell, RefCell};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::{Path, PathBuf};

use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module as LlvmModule};
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine,
};
use inkwell::types::{BasicMetadataTypeEnum, FunctionType, IntType, PointerType};
use inkwell::values::LLVMTailCallKind;
use inkwell::values::{
    BasicMetadataValueEnum, BasicValue, CallSiteValue, FunctionValue, GlobalValue,
    InstructionValue, IntValue, PointerValue, ValueKind,
};
use inkwell::AddressSpace;
use inkwell::IntPredicate;
use inkwell::OptimizationLevel;

use mana_syntax::{ApplyTarget, Clause, Expr, Fun, FunName, Literal, MapAssoc, Module, Pattern};

mod summary;
pub use summary::{summarize, ModuleSummary, SUMMARY_FORMAT};

mod cg;
mod driver;
mod effects;
mod reach;

pub use driver::{compile_program, CompileStats, ObjCache};
pub use reach::{set_native_manifest, NativeFn, NativeManifest, BIF_MODULES};

pub(crate) use cg::*;
pub(crate) use effects::*;
pub(crate) use reach::*;

/// One compilation input: its summary always present (from the summary
/// cache or freshly computed); the AST only if this run parsed it. Codegen
/// re-reads and re-parses on an object-cache miss when `ast` is None (the
/// re-read verifies `source_hash` — modify-during-compile is a hard error).
pub struct ModuleUnit {
    pub path: PathBuf,
    pub source_hash: [u8; 32],
    pub summary: ModuleSummary,
    pub ast: Option<Module>,
}

pub(crate) const TAG_SMALL: u64 = 0b001;

pub(crate) const TAG_ATOM: u64 = 0b010;

pub(crate) const NIL: u64 = 0b011;

pub(crate) const TAG_CONS: u64 = 0b100;

pub(crate) const TAG_MASK: u64 = 0b111;

pub(crate) const KIND_TUPLE: u64 = 0;

pub(crate) const KIND_FLOAT: u64 = 1;

pub(crate) const KIND_FUN: u64 = 2;

pub(crate) const KIND_MAP: u64 = 4;

pub(crate) const KIND_BIN: u64 = 5;

pub(crate) const KIND_SUBBIN: u64 = 13;

/// ctx word offsets (ProcCtx contract).
pub(crate) const CTX_ROOTS: u64 = 2;

pub(crate) const CTX_EXC_CLASS: u64 = 3;

pub(crate) const CTX_EXC_REASON: u64 = 4;

pub(crate) const CTX_REDUCTIONS: u64 = 5;

/// word 6: pointer to the per-scheduler argument spill area (uniform ABI)
pub(crate) const CTX_ARGV_SPILL: u64 = 6;

/// Uniform compiled-function signature: `ctx` + NREG term words, and NREG
/// is chosen so that EVERY parameter is register-passed on x86-64 SysV (6
/// integer registers: ctx + 5). Every compiled function has exactly this
/// LLVM prototype, so a `musttail` never needs stack argument space at
/// all — which sidesteps both tailcc pitfalls we hit: (1) callee-cleanup
/// popping more than a C entry reserved when the chain grows, and (2) the
/// x86 backend emitting a bare `jmp` without storing a constant stack
/// argument (`c5(a,b,c,d,e) -> a6(a,b,c,d,e,[])` compiled to `jmp a6`).
/// Arity > NREG passes args NREG-1.. through the ctx spill area, written
/// by the caller right before the call and read by the callee prologue
/// before anything else runs.
pub(crate) const NREG: usize = 5;

/// Reserved non-term word (tag 0b101): "an exception is unwinding".
pub(crate) const EXC_SENTINEL: u64 = 0b101;

pub(crate) type CgResult<T> = Result<T, String>;

pub(crate) type GcSet = HashSet<(String, FunName)>;

/// Disjoint memory classes for TBAA (never alias each other).
#[derive(Clone, Copy)]
pub(crate) enum MemKind {
    Ctx,
    Frame,
    Heap,
}

/// Where a variable's current value lives.
#[derive(Clone, Copy)]
pub(crate) enum Binding<'ctx> {
    /// Frame slot index (framed functions — survives GC).
    Slot(u64),
    /// SSA value (frameless functions — no GC can occur).
    Reg(IntValue<'ctx>),
}

#[derive(Clone, Default)]
pub(crate) struct Scope<'ctx> {
    pub(crate) vars: HashMap<String, Binding<'ctx>>,
    /// letrec-bound funs: lifted function + frame slot of the shared closure.
    pub(crate) funs: HashMap<FunName, (FunctionValue<'ctx>, u64)>,
}

/// A lambda-lifted function whose body still needs compiling.
pub(crate) struct Lift {
    pub(crate) f_index: usize,
    pub(crate) params: Vec<String>,
    pub(crate) captures: Vec<String>,
    pub(crate) sibs: Vec<(FunName, usize)>,
    pub(crate) body: Expr,
}

pub(crate) struct Cg<'ctx, 'p> {
    pub(crate) ctx: &'ctx Context,
    pub(crate) module: LlvmModule<'ctx>,
    pub(crate) builder: Builder<'ctx>,
    pub(crate) i64t: IntType<'ctx>,
    pub(crate) ptrt: PointerType<'ctx>,
    pub(crate) fns: RefCell<HashMap<FunName, FunctionValue<'ctx>>>,
    pub(crate) atoms: RefCell<HashMap<String, GlobalValue<'ctx>>>,
    pub(crate) lifted: RefCell<Vec<FunctionValue<'ctx>>>,
    pub(crate) pending: RefCell<Vec<Lift>>,
    pub(crate) lift_counter: Cell<u32>,
    pub(crate) module_name: String,
    pub(crate) gc_set: &'p GcSet,
    pub(crate) raise_set: &'p GcSet,
    // TBAA: ctx words / frame slots / heap objects never alias
    pub(crate) tbaa_kind: u32,
    pub(crate) tbaa_ctx: inkwell::values::MetadataValue<'ctx>,
    pub(crate) tbaa_frame: inkwell::values::MetadataValue<'ctx>,
    pub(crate) tbaa_heap: inkwell::values::MetadataValue<'ctx>,
    // per-function state
    pub(crate) cur_ctx: Cell<Option<PointerValue<'ctx>>>,
    pub(crate) cur_frame: Cell<Option<PointerValue<'ctx>>>,
    /// raise-path compilation: allocations go to the eternal allocator
    pub(crate) eternal_alloc: Cell<bool>,
    /// unique-name counter for static byte arrays (wide segment constants)
    pub(crate) static_bytes_count: Cell<usize>,
    /// exported functions compiled in this module → mana_exports entries
    pub(crate) exports: RefCell<Vec<(FunName, FunctionValue<'ctx>)>>,
    /// modules the program references but that are not compiled: calls to
    /// them poison the calling function (stub) instead of failing the build
    pub(crate) missing_modules: RefCell<HashSet<String>>,
    /// (module, behaviour) pairs for the mana_behaviours section
    pub(crate) behaviours: RefCell<Vec<(String, String)>>,
    pub(crate) is_entry_module: Cell<bool>,
    /// innermost enclosing try handler blocks (current function)
    pub(crate) handlers: RefCell<Vec<BasicBlock<'ctx>>>,
    /// lazily created per-function "pop frame; return sentinel" block
    pub(crate) propagate_bb: Cell<Option<BasicBlock<'ctx>>>,
    pub(crate) var_slots: RefCell<HashMap<String, u64>>,
    pub(crate) next_slot: Cell<u64>,
    pub(crate) slot_cap: Cell<u64>,
    /// slot high-water mark: frame len + memset are patched down to this
    /// once the body is compiled (the prepass cap is an over-approximation)
    pub(crate) peak_slot: Cell<u64>,
    pub(crate) frame_memset: Cell<Option<InstructionValue<'ctx>>>,
    pub(crate) frame_len_store: Cell<Option<InstructionValue<'ctx>>>,
    /// leading slots holding params/captures — written before the first GC
    /// point, so the entry memset skips them
    pub(crate) frame_skip: Cell<u64>,
}

/// A child value of an allocation: rooted in a frame slot, or (raise-path /
/// frameless) held in SSA.
pub(crate) enum Rooted<'ctx> {
    Slot(u64),
    Val(IntValue<'ctx>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum DiscKey {
    /// immediate term word (small int, nil)
    Word(u64),
    /// first byte of a binary subject
    Byte0(u8),
}

pub(crate) enum CaseVals<'ctx> {
    Ssa(Vec<IntValue<'ctx>>),
    Slots(Vec<u64>),
}

/// A parsed bitstring segment spec `(size, unit, type, flags)`. Byte-aligned
/// subset only; sub-byte sizes are TODO(bitstring).
pub(crate) struct SegSpec {
    pub(crate) little: bool,
    pub(crate) signed: bool,
    pub(crate) kind: SegKind,
}

pub(crate) enum SegKind {
    Int { size: SegSize },
    Bin { size: SegSize },
    Utf8,
}

/// Size in BYTES: constant, 'all' (binary rest), or computed at runtime
/// (`expr * unit` bits; the byte-alignment check happens at runtime).
pub(crate) enum SegSize {
    Bytes(u64),
    /// constant bit count that is NOT a byte multiple (nibble reads in
    /// Code.Identifier.escape etc.) — patterns only, static prefix only
    Bits(u64),
    All,
    Dyn { size: Expr, unit: i64 },
}

impl SegKind {
    pub(crate) fn allocates(&self) -> bool {
        matches!(self, SegKind::Bin { .. })
    }
    pub(crate) fn dynamic(&self) -> bool {
        matches!(
            self,
            SegKind::Utf8
                | SegKind::Int { size: SegSize::Dyn { .. } }
                | SegKind::Bin { size: SegSize::Dyn { .. } | SegSize::All }
        )
    }
}

pub(crate) fn mangle(module: &str, f: &FunName) -> String {
    format!("mn_{}_{}_{}", sanitize(module), sanitize(&f.name), f.arity)
}

pub(crate) fn sanitize(s: &str) -> String {
    s.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() {
                c.to_string()
            } else {
                format!("_x{:02x}", c as u32)
            }
        })
        .collect()
}

pub(crate) fn be(e: inkwell::builder::BuilderError) -> String {
    format!("LLVM builder: {}", e)
}

pub(crate) fn call_result(call: CallSiteValue<'_>) -> CgResult<inkwell::values::BasicValueEnum<'_>> {
    match call.try_as_basic_value() {
        ValueKind::Basic(v) => Ok(v),
        ValueKind::Instruction(_) => Err("call to void function used as a value".into()),
    }
}

impl<'ctx, 'p> Cg<'ctx, 'p> {
    pub(crate) fn new(
        ctx: &'ctx Context,
        module_name: &str,
        gc_set: &'p GcSet,
        raise_set: &'p GcSet,
    ) -> Self {
        let module = ctx.create_module(module_name);
        // TBAA tree: three disjoint scalar classes under one root. Lets LLVM
        // keep heap_top/frame slots in registers across heap stores.
        let i64t = ctx.i64_type();
        let root = ctx.metadata_node(&[ctx.metadata_string("mana-tbaa").into()]);
        let mk_tag = |name: &str| {
            let ty = ctx.metadata_node(&[
                ctx.metadata_string(name).into(),
                root.into(),
                i64t.const_zero().into(),
            ]);
            ctx.metadata_node(&[ty.into(), ty.into(), i64t.const_zero().into()])
        };
        let tbaa_ctx = mk_tag("procctx");
        let tbaa_frame = mk_tag("gcframe");
        let tbaa_heap = mk_tag("heap");
        Cg {
            ctx,
            module,
            builder: ctx.create_builder(),
            i64t: ctx.i64_type(),
            ptrt: ctx.ptr_type(AddressSpace::default()),
            fns: Default::default(),
            atoms: Default::default(),
            lifted: Default::default(),
            pending: Default::default(),
            lift_counter: Cell::new(0),
            module_name: module_name.to_string(),
            gc_set,
            raise_set,
            tbaa_kind: ctx.get_kind_id("tbaa"),
            tbaa_ctx,
            tbaa_frame,
            tbaa_heap,
            cur_ctx: Cell::new(None),
            cur_frame: Cell::new(None),
            eternal_alloc: Cell::new(false),
            static_bytes_count: Cell::new(0),
            exports: RefCell::new(Vec::new()),
            missing_modules: RefCell::new(HashSet::new()),
            behaviours: RefCell::new(Vec::new()),
            is_entry_module: Cell::new(false),
            handlers: RefCell::new(Vec::new()),
            propagate_bb: Cell::new(None),
            var_slots: Default::default(),
            next_slot: Cell::new(0),
            slot_cap: Cell::new(0),
            peak_slot: Cell::new(0),
            frame_memset: Cell::new(None),
            frame_len_store: Cell::new(None),
            frame_skip: Cell::new(0),
        }
    }

    /// `(ctx, term × arity) -> term`
    /// Named compiled functions use LLVM's `tailcc`: with the C convention a
    /// callee taking >6 integer args gets stack-passed arguments, and a
    /// `tail` hint on such a call is NOT honored — the call stays a real
    /// call and a self-recursive server loop (gen_server:loop/7) grows the
    /// coroutine stack by one frame per iteration until it faults. `tailcc`
    /// guarantees `musttail` regardless of arity. Pointers that escape to
    /// the runtime (exports table, program entry) go through `ccc_wrapper`.
    pub(crate) const TAILCC: u32 = 18; // LLVMCallConv: tailcc
}
