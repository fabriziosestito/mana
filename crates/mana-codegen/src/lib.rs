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
//! TODO(lco): tailcc + musttail for guaranteed cross-function tail calls.

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
use inkwell::values::{
    BasicMetadataValueEnum, BasicValue, CallSiteValue, FunctionValue, GlobalValue, IntValue, PointerValue,
    ValueKind,
};
use inkwell::AddressSpace;
use inkwell::IntPredicate;
use inkwell::OptimizationLevel;

use mana_syntax::{ApplyTarget, Clause, Expr, Fun, FunName, Literal, MapAssoc, Module, Pattern};

const TAG_SMALL: u64 = 0b001;
const TAG_ATOM: u64 = 0b010;
const NIL: u64 = 0b011;
const TAG_CONS: u64 = 0b100;
const TAG_MASK: u64 = 0b111;
const KIND_TUPLE: u64 = 0;
const KIND_FLOAT: u64 = 1;
const KIND_FUN: u64 = 2;
const KIND_MAP: u64 = 4;

/// ctx word offsets (ProcCtx contract).
const CTX_ROOTS: u64 = 2;
const CTX_EXC_CLASS: u64 = 3;
const CTX_EXC_REASON: u64 = 4;
const CTX_REDUCTIONS: u64 = 5;
/// Reserved non-term word (tag 0b101): "an exception is unwinding".
const EXC_SENTINEL: u64 = 0b101;

type CgResult<T> = Result<T, String>;
type GcSet = HashSet<(String, FunName)>;

/// Disjoint memory classes for TBAA (never alias each other).
#[derive(Clone, Copy)]
enum MemKind {
    Ctx,
    Frame,
    Heap,
}

/// Where a variable's current value lives.
#[derive(Clone, Copy)]
enum Binding<'ctx> {
    /// Frame slot index (framed functions — survives GC).
    Slot(u64),
    /// SSA value (frameless functions — no GC can occur).
    Reg(IntValue<'ctx>),
}

#[derive(Clone, Default)]
struct Scope<'ctx> {
    vars: HashMap<String, Binding<'ctx>>,
    /// letrec-bound funs: lifted function + frame slot of the shared closure.
    funs: HashMap<FunName, (FunctionValue<'ctx>, u64)>,
}

/// A lambda-lifted function whose body still needs compiling.
struct Lift {
    f_index: usize,
    params: Vec<String>,
    captures: Vec<String>,
    sibs: Vec<(FunName, usize)>,
    body: Expr,
}

/// Compile a program to one object file per module in `out_dir`; returns
/// the object paths. Only functions reachable from `entry` are compiled
/// (closed world). A C `main` (init ctx, call entry) lands in the entry
/// module's object. `poisoned` maps unparseable module names to their
/// errors, surfaced if reachability needs them.
pub fn compile_program(
    mods: &[Module],
    entry_mod: &str,
    entry: &FunName,
    out_dir: &Path,
    dump_ir: bool,
    poisoned: &HashMap<String, String>,
) -> CgResult<Vec<PathBuf>> {
    if entry.arity != 0 {
        return Err(format!(
            "entry function {}/{} must have arity 0",
            entry.name, entry.arity
        ));
    }
    {
        let mut names = HashSet::new();
        for m in mods {
            if !names.insert(&m.name) {
                return Err(format!("module '{}' provided more than once", m.name));
            }
        }
    }
    let reachable = reachable_funs(mods, entry_mod, entry, poisoned)?;
    let gc_set = compute_may_gc(mods, &reachable);
    let raise_set = compute_may_raise(mods, &reachable);

    std::fs::create_dir_all(out_dir)
        .map_err(|e| format!("creating {}: {}", out_dir.display(), e))?;
    let mut objs = Vec::new();
    for m in mods {
        let include: HashSet<FunName> = reachable
            .iter()
            .filter(|(module, _)| module == &m.name)
            .map(|(_, f)| f.clone())
            .collect();
        if include.is_empty() {
            continue;
        }
        let context = Context::create();
        let cg = Cg::new(&context, &m.name, &gc_set, &raise_set);
        let entry_here = (m.name == entry_mod).then_some(entry);
        cg.compile(m, &include, entry_here)?;
        if dump_ir {
            eprintln!("{}", cg.module.print_to_string().to_string());
        }
        cg.module
            .verify()
            .map_err(|e| format!("LLVM verifier ({}): {}", m.name, e))?;
        let obj = out_dir.join(format!("{}.o", sanitize(&m.name)));
        cg.emit_object(&obj)?;
        objs.push(obj);
    }
    Ok(objs)
}

struct Cg<'ctx, 'p> {
    ctx: &'ctx Context,
    module: LlvmModule<'ctx>,
    builder: Builder<'ctx>,
    i64t: IntType<'ctx>,
    ptrt: PointerType<'ctx>,
    fns: RefCell<HashMap<FunName, FunctionValue<'ctx>>>,
    atoms: RefCell<HashMap<String, GlobalValue<'ctx>>>,
    lifted: RefCell<Vec<FunctionValue<'ctx>>>,
    pending: RefCell<Vec<Lift>>,
    lift_counter: Cell<u32>,
    module_name: String,
    gc_set: &'p GcSet,
    raise_set: &'p GcSet,
    // TBAA: ctx words / frame slots / heap objects never alias
    tbaa_kind: u32,
    tbaa_ctx: inkwell::values::MetadataValue<'ctx>,
    tbaa_frame: inkwell::values::MetadataValue<'ctx>,
    tbaa_heap: inkwell::values::MetadataValue<'ctx>,
    // per-function state
    cur_ctx: Cell<Option<PointerValue<'ctx>>>,
    cur_frame: Cell<Option<PointerValue<'ctx>>>,
    /// raise-path compilation: allocations go to the eternal allocator
    eternal_alloc: Cell<bool>,
    /// innermost enclosing try handler blocks (current function)
    handlers: RefCell<Vec<BasicBlock<'ctx>>>,
    /// lazily created per-function "pop frame; return sentinel" block
    propagate_bb: Cell<Option<BasicBlock<'ctx>>>,
    var_slots: RefCell<HashMap<String, u64>>,
    next_slot: Cell<u64>,
    slot_cap: Cell<u64>,
}

impl<'ctx, 'p> Cg<'ctx, 'p> {
    fn new(
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
            handlers: RefCell::new(Vec::new()),
            propagate_bb: Cell::new(None),
            var_slots: Default::default(),
            next_slot: Cell::new(0),
            slot_cap: Cell::new(0),
        }
    }

    /// `(ctx, term × arity) -> term`
    fn term_fn_type(&self, arity: usize) -> FunctionType<'ctx> {
        let mut params: Vec<BasicMetadataTypeEnum> =
            vec![BasicMetadataTypeEnum::PointerType(self.ptrt)];
        params.extend((0..arity).map(|_| BasicMetadataTypeEnum::IntType(self.i64t)));
        self.i64t.fn_type(&params, false)
    }

    fn ctx_val(&self) -> PointerValue<'ctx> {
        self.cur_ctx.get().expect("ctx param not set")
    }

    fn framed(&self) -> bool {
        self.cur_frame.get().is_some()
    }

    fn expr_gc(&self, e: &Expr) -> bool {
        let mut letrec = HashSet::new();
        expr_may_gc(e, &self.module_name, self.gc_set, &mut letrec)
    }

    // ---- runtime externs ----

    fn rt_fn(
        &self,
        name: &str,
        mk: impl FnOnce() -> FunctionType<'ctx>,
    ) -> FunctionValue<'ctx> {
        self.module
            .get_function(name)
            .unwrap_or_else(|| self.module.add_function(name, mk(), None))
    }

    fn rt_init(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_init", || self.ptrt.fn_type(&[], false))
    }

    fn rt_display(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_display", || {
            self.ctx
                .void_type()
                .fn_type(&[BasicMetadataTypeEnum::IntType(self.i64t)], false)
        })
    }

    fn rt_alloc_slow(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_alloc_slow", || {
            self.ptrt.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    fn rt_alloc_eternal(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_alloc_eternal", || {
            self.ptrt.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    fn rt_p_i64(&self, name: &str) -> FunctionValue<'ctx> {
        self.rt_fn(name, || {
            self.i64t
                .fn_type(&[BasicMetadataTypeEnum::PointerType(self.ptrt)], false)
        })
    }

    fn rt_p_void(&self, name: &str) -> FunctionValue<'ctx> {
        self.rt_fn(name, || {
            self.ctx
                .void_type()
                .fn_type(&[BasicMetadataTypeEnum::PointerType(self.ptrt)], false)
        })
    }

    fn rt_register_atoms(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_register_atoms", || {
            let params: Vec<BasicMetadataTypeEnum> =
                (0..13).map(|_| BasicMetadataTypeEnum::IntType(self.i64t)).collect();
            self.ctx.void_type().fn_type(&params, false)
        })
    }

    /// (ctx, term) -> term runtime BIF helper.
    fn rt_pt_i64(&self, name: &str) -> FunctionValue<'ctx> {
        self.rt_fn(name, || {
            self.i64t.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    fn rt_run(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_run", || {
            self.i64t.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                ],
                false,
            )
        })
    }

    fn rt_spawn(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_spawn", || {
            self.i64t.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    fn rt_send(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_send", || {
            self.ctx.void_type().fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    fn rt_recv_wait(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_recv_wait", || {
            self.i64t.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    fn rt_uncaught(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_uncaught", || {
            self.ctx
                .void_type()
                .fn_type(&[BasicMetadataTypeEnum::PointerType(self.ptrt)], false)
        })
    }

    // ---- constants ----

    fn small_int(&self, n: i64) -> IntValue<'ctx> {
        // TODO(bignum): values outside the small range wrap silently.
        self.i64t.const_int(((n as u64) << 3) | TAG_SMALL, false)
    }

    fn nil(&self) -> IntValue<'ctx> {
        self.i64t.const_int(NIL, false)
    }

    fn atom_term(&self, name: &str) -> CgResult<IntValue<'ctx>> {
        let global = {
            let mut atoms = self.atoms.borrow_mut();
            if let Some(g) = atoms.get(name) {
                *g
            } else {
                let bytes = name.as_bytes();
                let data = self.ctx.const_string(bytes, false);
                let len = self.i64t.const_int(bytes.len() as u64, false);
                let init = self.ctx.const_struct(&[len.into(), data.into()], false);
                let g = self.module.add_global(
                    init.get_type(),
                    None,
                    &format!("mana_atom.{}", sanitize(name)),
                );
                g.set_initializer(&init);
                g.set_constant(true);
                g.set_alignment(8);
                // Same atom name → same symbol in every object; the linker
                // keeps exactly one, giving program-wide identity.
                g.set_linkage(Linkage::LinkOnceODR);
                atoms.insert(name.to_string(), g);
                g
            }
        };
        let as_int = self
            .builder
            .build_ptr_to_int(global.as_pointer_value(), self.i64t, "atom.addr")
            .map_err(be)?;
        self.builder
            .build_or(as_int, self.i64t.const_int(TAG_ATOM, false), "atom")
            .map_err(be)
    }

    // ---- frames & slots ----

    /// Set up the root frame for the function whose entry block the builder
    /// is positioned in. `body` decides framedness; `var_names` are all
    /// names that may be bound (params, captures, body binds).
    fn setup_frame(
        &self,
        body: &Expr,
        var_names: &[String],
        letrec_sibs: &[FunName],
    ) -> CgResult<()> {
        self.var_slots.borrow_mut().clear();
        let mut letrec: HashSet<FunName> = letrec_sibs.iter().cloned().collect();
        if !expr_may_gc(body, &self.module_name, self.gc_set, &mut letrec) {
            self.cur_frame.set(None);
            return Ok(());
        }

        let mut vars: BTreeSet<String> = var_names.iter().cloned().collect();
        let mut nodes = 0usize;
        frame_prepass(body, &mut vars, &mut nodes);
        let nvars = vars.len() as u64;
        let cap = nvars + nodes as u64 + 8;

        {
            let mut slots = self.var_slots.borrow_mut();
            for (i, v) in vars.iter().enumerate() {
                slots.insert(v.clone(), i as u64);
            }
        }
        self.next_slot.set(nvars);
        self.slot_cap.set(cap);

        let frame_ty = self.i64t.array_type((cap + 2) as u32);
        let frame = self
            .builder
            .build_alloca(frame_ty, "gc.frame")
            .map_err(be)?;
        let ctx = self.ctx_val();
        let prev = self.mem_load(ctx, CTX_ROOTS, MemKind::Ctx)?;
        self.mem_store(frame, 0, prev, MemKind::Frame)?;
        self.mem_store(frame, 1, self.i64t.const_int(cap, false), MemKind::Frame)?;
        // zero-init all slots with one memset — 0 marks an empty slot the
        // collector skips (cheaper than storing NIL per slot)
        let slots = unsafe {
            self.builder
                .build_in_bounds_gep(
                    self.i64t,
                    frame,
                    &[self.i64t.const_int(2, false)],
                    "slots",
                )
                .map_err(be)?
        };
        self.builder
            .build_memset(
                slots,
                8,
                self.ctx.i8_type().const_zero(),
                self.i64t.const_int(cap * 8, false),
            )
            .map_err(be)?;
        let frame_int = self
            .builder
            .build_ptr_to_int(frame, self.i64t, "frame.addr")
            .map_err(be)?;
        self.mem_store(ctx, CTX_ROOTS, frame_int, MemKind::Ctx)?;
        self.cur_frame.set(Some(frame));
        Ok(())
    }

    /// Unlink the frame (before any return or tail call).
    fn pop_frame(&self) -> CgResult<()> {
        if let Some(frame) = self.cur_frame.get() {
            let prev = self.mem_load(frame, 0, MemKind::Frame)?;
            self.mem_store(self.ctx_val(), CTX_ROOTS, prev, MemKind::Ctx)?;
        }
        Ok(())
    }

    fn emit_ret(&self, v: IntValue<'ctx>) -> CgResult<()> {
        self.pop_frame()?;
        self.builder.build_return(Some(&v)).map_err(be)?;
        Ok(())
    }

    fn sentinel(&self) -> IntValue<'ctx> {
        self.i64t.const_int(EXC_SENTINEL, false)
    }

    /// Where an unwinding exception goes: the innermost try handler, or the
    /// per-function propagate block (unlink frame, return the sentinel).
    fn unwind_target(&self, f: FunctionValue<'ctx>) -> CgResult<BasicBlock<'ctx>> {
        if let Some(h) = self.handlers.borrow().last() {
            return Ok(*h);
        }
        if let Some(bb) = self.propagate_bb.get() {
            return Ok(bb);
        }
        let saved = self.builder.get_insert_block();
        let bb = self.ctx.append_basic_block(f, "unwind");
        self.builder.position_at_end(bb);
        self.pop_frame()?;
        self.builder.build_return(Some(&self.sentinel())).map_err(be)?;
        if let Some(s) = saved {
            self.builder.position_at_end(s);
        }
        self.propagate_bb.set(Some(bb));
        Ok(bb)
    }

    /// Store class/reason into the ctx and jump to the unwind target.
    /// Leaves the builder in a fresh dead block.
    fn emit_raise(
        &self,
        f: FunctionValue<'ctx>,
        class: IntValue<'ctx>,
        reason: IntValue<'ctx>,
    ) -> CgResult<()> {
        let ctx = self.ctx_val();
        self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
        self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
        let target = self.unwind_target(f)?;
        self.builder.build_unconditional_branch(target).map_err(be)?;
        let dead = self.ctx.append_basic_block(f, "dead");
        self.builder.position_at_end(dead);
        Ok(())
    }

    /// After a call to a may-raise function: branch to the unwind target if
    /// the sentinel came back.
    fn check_exc(
        &self,
        f: FunctionValue<'ctx>,
        ret: IntValue<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let is_exc = self
            .builder
            .build_int_compare(IntPredicate::EQ, ret, self.sentinel(), "is.exc")
            .map_err(be)?;
        let target = self.unwind_target(f)?;
        let cont = self.ctx.append_basic_block(f, "call.ok");
        self.builder
            .build_conditional_branch(is_exc, target, cont)
            .map_err(be)?;
        self.builder.position_at_end(cont);
        Ok(ret)
    }

    /// Build an eternal (non-moving) 2-tuple for an exception reason.
    fn eternal_pair(
        &self,
        tag: &str,
        v: IntValue<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let call = self
            .builder
            .build_call(
                self.rt_alloc_eternal(),
                &[
                    self.ctx_val().into(),
                    self.i64t.const_int(3, false).into(),
                    self.i64t.const_zero().into(),
                ],
                "exc.reason",
            )
            .map_err(be)?;
        let p = call_result(call)?.into_pointer_value();
        self.store_word(p, 0, self.i64t.const_int((2 << 8) | KIND_TUPLE, false))?;
        let tag_atom = self.atom_term(tag)?;
        self.store_word(p, 1, tag_atom)?;
        self.store_word(p, 2, v)?;
        self.builder.build_ptr_to_int(p, self.i64t, "reason").map_err(be)
    }

    fn slot_ptr(&self, idx: u64) -> CgResult<PointerValue<'ctx>> {
        let frame = self.cur_frame.get().expect("slot in frameless function");
        unsafe {
            self.builder
                .build_in_bounds_gep(
                    self.i64t,
                    frame,
                    &[self.i64t.const_int(2 + idx, false)],
                    "slot",
                )
                .map_err(be)
        }
    }

    fn alloc_temp(&self) -> u64 {
        let n = self.next_slot.get();
        assert!(n < self.slot_cap.get(), "frame slot capacity exceeded");
        self.next_slot.set(n + 1);
        n
    }

    fn spill(&self, v: IntValue<'ctx>) -> CgResult<u64> {
        let idx = self.alloc_temp();
        let p = self.slot_ptr(idx)?;
        let inst = self.builder.build_store(p, v).map_err(be)?;
        let _ = inst.set_metadata(self.tbaa_frame, self.tbaa_kind);
        Ok(idx)
    }

    fn reload(&self, idx: u64) -> CgResult<IntValue<'ctx>> {
        let p = self.slot_ptr(idx)?;
        let v = self.builder.build_load(self.i64t, p, "reload").map_err(be)?;
        if let Some(inst) = v.as_instruction_value() {
            let _ = inst.set_metadata(self.tbaa_frame, self.tbaa_kind);
        }
        Ok(v.into_int_value())
    }

    fn bind_var(&self, scope: &mut Scope<'ctx>, name: &str, v: IntValue<'ctx>) -> CgResult<()> {
        if self.framed() {
            let idx = *self
                .var_slots
                .borrow()
                .get(name)
                .unwrap_or_else(|| panic!("no slot preassigned for variable {}", name));
            let p = self.slot_ptr(idx)?;
            let inst = self.builder.build_store(p, v).map_err(be)?;
            let _ = inst.set_metadata(self.tbaa_frame, self.tbaa_kind);
            scope.vars.insert(name.to_string(), Binding::Slot(idx));
        } else {
            scope.vars.insert(name.to_string(), Binding::Reg(v));
        }
        Ok(())
    }

    fn read_var(&self, scope: &Scope<'ctx>, name: &str) -> CgResult<IntValue<'ctx>> {
        match scope.vars.get(name) {
            Some(Binding::Reg(v)) => Ok(*v),
            Some(Binding::Slot(idx)) => self.reload(*idx),
            None => Err(format!("unbound variable {}", name)),
        }
    }

    // ---- module compilation ----

    fn compile(
        &self,
        ast: &Module,
        include: &HashSet<FunName>,
        entry: Option<&FunName>,
    ) -> CgResult<()> {
        for (fname, fun) in &ast.definitions {
            if !include.contains(fname) {
                continue;
            }
            let f = self.module.add_function(
                &mangle(&self.module_name, fname),
                self.term_fn_type(fun.params.len()),
                None,
            );
            self.fns.borrow_mut().insert(fname.clone(), f);
        }

        for (fname, fun) in &ast.definitions {
            if !include.contains(fname) {
                continue;
            }
            self.compile_fn(fname, fun)?;
            self.drain_lifts()?;
        }

        match entry {
            Some(e) => self.emit_main(e),
            None => Ok(()),
        }
    }

    fn compile_fn(&self, fname: &FunName, fun: &Fun) -> CgResult<()> {
        let f = self.fns.borrow()[fname];
        let entry = self.ctx.append_basic_block(f, "entry");
        self.builder.position_at_end(entry);
        self.cur_ctx
            .set(Some(f.get_nth_param(0).unwrap().into_pointer_value()));
        self.handlers.borrow_mut().clear();
        self.propagate_bb.set(None);
        self.setup_frame(&fun.body, &fun.params, &[])?;
        let mut scope = Scope::default();
        for (i, p) in fun.params.iter().enumerate() {
            let v = f.get_nth_param(1 + i as u32).unwrap().into_int_value();
            v.set_name(p);
            self.bind_var(&mut scope, p, v)?;
        }
        self.emit_reduction_check(f)?;
        self.compile_tail(f, &fun.body, &mut scope)
    }

    /// Preemption point: decrement the reduction budget, yield to the
    /// scheduler on exhaustion. Only in framed functions AFTER params are
    /// rooted — yield points are GC points, and everything live is already
    /// in frame slots here, so preemption costs no extra spills.
    fn emit_reduction_check(&self, f: FunctionValue<'ctx>) -> CgResult<()> {
        if !self.framed() {
            return Ok(());
        }
        let ctx = self.ctx_val();
        let red = self.mem_load(ctx, CTX_REDUCTIONS, MemKind::Ctx)?;
        let dec = self
            .builder
            .build_int_sub(red, self.i64t.const_int(1, false), "red.dec")
            .map_err(be)?;
        self.mem_store(ctx, CTX_REDUCTIONS, dec, MemKind::Ctx)?;
        let out = self
            .builder
            .build_int_compare(
                IntPredicate::SLT,
                dec,
                self.i64t.const_zero(),
                "red.out",
            )
            .map_err(be)?;
        let yield_bb = self.ctx.append_basic_block(f, "yield");
        let cont = self.ctx.append_basic_block(f, "red.cont");
        self.builder
            .build_conditional_branch(out, yield_bb, cont)
            .map_err(be)?;
        self.builder.position_at_end(yield_bb);
        self.builder
            .build_call(self.rt_p_void("mana_rt_yield"), &[ctx.into()], "")
            .map_err(be)?;
        self.builder.build_unconditional_branch(cont).map_err(be)?;
        self.builder.position_at_end(cont);
        Ok(())
    }

    /// Compile bodies of lambda-lifted funs queued during compilation.
    fn drain_lifts(&self) -> CgResult<()> {
        loop {
            // NB: pop in its own statement — a `while let` scrutinee would
            // hold the RefMut across the body, and bodies push new lifts.
            let next = self.pending.borrow_mut().pop();
            let Some(l) = next else { break };
            let f = self.lifted.borrow()[l.f_index];
            let entry = self.ctx.append_basic_block(f, "entry");
            self.builder.position_at_end(entry);
            self.cur_ctx
                .set(Some(f.get_nth_param(0).unwrap().into_pointer_value()));
            self.handlers.borrow_mut().clear();
            self.propagate_bb.set(None);

            let closure_slot_name = "closure$".to_string();
            let mut var_names: Vec<String> = l.params.clone();
            var_names.extend(l.captures.iter().cloned());
            if !l.sibs.is_empty() {
                var_names.push(closure_slot_name.clone());
            }
            let sib_names: Vec<FunName> = l.sibs.iter().map(|(n, _)| n.clone()).collect();
            self.setup_frame(&l.body, &var_names, &sib_names)?;

            let mut scope = Scope::default();
            for (i, p) in l.params.iter().enumerate() {
                let v = f.get_nth_param(1 + i as u32).unwrap().into_int_value();
                v.set_name(p);
                self.bind_var(&mut scope, p, v)?;
            }
            let closure = f
                .get_nth_param(1 + l.params.len() as u32)
                .unwrap()
                .into_int_value();
            closure.set_name("closure");
            if !l.captures.is_empty() {
                // loads happen before any GC point (entry, no allocs yet)
                let p = self
                    .builder
                    .build_int_to_ptr(closure, self.ptrt, "env.ptr")
                    .map_err(be)?;
                for (i, cap) in l.captures.iter().enumerate() {
                    let v = self.load_word(p, 2 + i as u64)?;
                    v.set_name(cap);
                    self.bind_var(&mut scope, cap, v)?;
                }
            }
            if !l.sibs.is_empty() && self.framed() {
                // the closure term itself must be rooted for sibling calls;
                // a member that never calls siblings can be frameless, in
                // which case no sibling binding is ever consulted.
                self.bind_var(&mut scope, &closure_slot_name, closure)?;
                let Binding::Slot(cl_slot) = scope.vars[&closure_slot_name] else {
                    unreachable!("framed bind produced a register");
                };
                for (fname, idx) in &l.sibs {
                    let sib = self.lifted.borrow()[*idx];
                    scope.funs.insert(fname.clone(), (sib, cl_slot));
                }
            }
            self.emit_reduction_check(f)?;
            self.compile_tail(f, &l.body, &mut scope)?;
        }
        Ok(())
    }

    fn emit_main(&self, entry: &FunName) -> CgResult<()> {
        let i32t = self.ctx.i32_type();
        let main = self
            .module
            .add_function("main", i32t.fn_type(&[], false), None);
        let bb = self.ctx.append_basic_block(main, "entry");
        self.builder.position_at_end(bb);
        let init = self
            .builder
            .build_call(self.rt_init(), &[], "ctx")
            .map_err(be)?;
        let ctx = call_result(init)?.into_pointer_value();
        // the runtime builds exit/monitor messages: hand it the well-known
        // atom terms (atoms are compiler statics)
        let names = [
            "normal", "killed", "kill", "EXIT", "DOWN", "process", "noproc", "true", "false",
            "badarg", "error", "badmap", "badkey",
        ];
        let mut atom_args: Vec<BasicMetadataValueEnum> = Vec::new();
        for n in names {
            atom_args.push(self.atom_term(n)?.into());
        }
        self.builder
            .build_call(self.rt_register_atoms(), &atom_args, "")
            .map_err(be)?;

        let target = self.fns.borrow()[entry];
        let entry_ptr = target.as_global_value().as_pointer_value();
        let call = self
            .builder
            .build_call(self.rt_run(), &[ctx.into(), entry_ptr.into()], "ret")
            .map_err(be)?;
        let ret = call_result(call)?.into_int_value();
        let is_exc = self
            .builder
            .build_int_compare(IntPredicate::EQ, ret, self.sentinel(), "is.exc")
            .map_err(be)?;
        let bad = self.ctx.append_basic_block(main, "uncaught");
        let ok = self.ctx.append_basic_block(main, "ok");
        self.builder
            .build_conditional_branch(is_exc, bad, ok)
            .map_err(be)?;
        self.builder.position_at_end(bad);
        self.builder
            .build_call(self.rt_uncaught(), &[ctx.into()], "")
            .map_err(be)?;
        self.builder.build_unreachable().map_err(be)?;
        self.builder.position_at_end(ok);
        self.builder
            .build_return(Some(&i32t.const_zero()))
            .map_err(be)?;
        Ok(())
    }

    // ---- expression compilation ----

    fn compile_tail(
        &self,
        f: FunctionValue<'ctx>,
        e: &Expr,
        scope: &mut Scope<'ctx>,
    ) -> CgResult<()> {
        match e {
            Expr::Let { vars, arg, body } => {
                self.bind_let(f, vars, arg, scope)?;
                self.compile_tail(f, body, scope)
            }
            Expr::LetRec { defs, body } => {
                let mut inner = self.bind_letrec(f, defs, scope)?;
                self.compile_tail(f, body, &mut inner)
            }
            Expr::Do(first, then) => {
                self.compile_value(f, first, scope)?;
                self.compile_tail(f, then, scope)
            }
            Expr::Case { arg, clauses } => {
                let vals = self.compile_case_arg(f, arg, clauses, scope)?;
                self.compile_case(f, &vals, clauses, scope, None)
            }
            Expr::Try {
                arg,
                vars,
                body,
                evars,
                handler,
            } => {
                if vars.len() != 1 {
                    return Err("multi-value try is not supported".into());
                }
                let hbb = self.ctx.append_basic_block(f, "catch");
                self.handlers.borrow_mut().push(hbb);
                let v = self.compile_value(f, arg, scope);
                self.handlers.borrow_mut().pop();
                let v = v?;
                self.bind_var(scope, &vars[0], v)?;
                self.compile_tail(f, body, scope)?;

                self.builder.position_at_end(hbb);
                let ctx = self.ctx_val();
                let class = self.mem_load(ctx, CTX_EXC_CLASS, MemKind::Ctx)?;
                let reason = self.mem_load(ctx, CTX_EXC_REASON, MemKind::Ctx)?;
                let mut hscope = scope.clone();
                self.bind_try_evars(&mut hscope, evars, class, reason)?;
                self.compile_tail(f, handler, &mut hscope)
            }
            Expr::Apply { target, args } => {
                // the sentinel propagates through the returned value —
                // tail calls need no exception check
                let (call, _) = self.compile_apply(f, target, args, scope, true)?;
                call.set_tail_call(true);
                let v = call_result(call)?;
                self.builder.build_return(Some(&v)).map_err(be)?;
                Ok(())
            }
            Expr::Call { module, name, args } if module != "erlang" => {
                let callee = self.remote_fn(module, name, args.len());
                let argv = self.eval_args(f, args, scope)?;
                self.pop_frame()?;
                let call = self.builder.build_call(callee, &argv, "tail").map_err(be)?;
                call.set_tail_call(true);
                let v = call_result(call)?;
                self.builder.build_return(Some(&v)).map_err(be)?;
                Ok(())
            }
            Expr::PrimOp { name, args } if is_raise(name) => {
                self.compile_raise(f, name, args, scope)?;
                self.builder.build_unreachable().map_err(be)?;
                Ok(())
            }
            _ => {
                let v = self.compile_value(f, e, scope)?;
                self.emit_ret(v)
            }
        }
    }

    fn compile_value(
        &self,
        f: FunctionValue<'ctx>,
        e: &Expr,
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        match e {
            Expr::Var(v) => self.read_var(scope, v),
            Expr::Lit(l) => self.compile_literal(l),
            Expr::Tuple(items) => {
                let refs: Vec<&Expr> = items.iter().collect();
                let slots = self.eval_all_rooted(f, &refs, scope)?;
                let p = self.alloc_words(1 + slots.len() as u64)?;
                let header = self
                    .i64t
                    .const_int(((slots.len() as u64) << 8) | KIND_TUPLE, false);
                self.store_word(p, 0, header)?;
                for (i, s) in slots.iter().enumerate() {
                    let v = self.rooted_get(s)?;
                    self.store_word(p, 1 + i as u64, v)?;
                }
                self.builder
                    .build_ptr_to_int(p, self.i64t, "tuple")
                    .map_err(be)
            }
            Expr::Cons(h, t) => {
                let slots = self.eval_all_rooted(f, &[h.as_ref(), t.as_ref()], scope)?;
                let p = self.alloc_words_kind(2, true)?;
                for (i, s) in slots.iter().enumerate() {
                    let v = self.rooted_get(s)?;
                    self.store_word(p, i as u64, v)?;
                }
                let as_int = self
                    .builder
                    .build_ptr_to_int(p, self.i64t, "cons.addr")
                    .map_err(be)?;
                self.builder
                    .build_or(as_int, self.i64t.const_int(TAG_CONS, false), "cons")
                    .map_err(be)
            }
            Expr::Fun(fun) => {
                let free: Vec<String> = {
                    let mut bound: HashSet<String> = fun.params.iter().cloned().collect();
                    let mut out = BTreeSet::new();
                    free_vars(&fun.body, &mut bound, &mut out);
                    out.into_iter().collect()
                };
                let lifted = self.declare_lift("fun", fun.params.len());
                self.pending.borrow_mut().push(Lift {
                    f_index: lifted,
                    params: fun.params.clone(),
                    captures: free.clone(),
                    sibs: Vec::new(),
                    body: fun.body.clone(),
                });
                let fv = self.lifted.borrow()[lifted];
                self.make_closure(fv, fun.params.len(), &free, scope)
            }
            Expr::FunRef { module, fun } => {
                if module.is_none() && scope.funs.contains_key(fun) {
                    return Err(format!(
                        "letrec-bound fun {}/{} used as a value (unsupported)",
                        fun.name, fun.arity
                    ));
                }
                let shim = self.fun_shim(module.as_deref(), fun)?;
                self.make_closure(shim, fun.arity, &[], scope)
            }
            Expr::Let { vars, arg, body } => {
                self.bind_let(f, vars, arg, scope)?;
                self.compile_value(f, body, scope)
            }
            Expr::LetRec { defs, body } => {
                let mut inner = self.bind_letrec(f, defs, scope)?;
                self.compile_value(f, body, &mut inner)
            }
            Expr::Do(first, then) => {
                self.compile_value(f, first, scope)?;
                self.compile_value(f, then, scope)
            }
            Expr::Try {
                arg,
                vars,
                body,
                evars,
                handler,
            } => {
                if vars.len() != 1 {
                    return Err("multi-value try is not supported".into());
                }
                let hbb = self.ctx.append_basic_block(f, "catch");
                let merge = self.ctx.append_basic_block(f, "try.merge");

                self.handlers.borrow_mut().push(hbb);
                let v = self.compile_value(f, arg, scope);
                self.handlers.borrow_mut().pop();
                let v = v?;
                self.bind_var(scope, &vars[0], v)?;
                let bv = self.compile_value(f, body, scope)?;
                let body_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(merge).map_err(be)?;

                self.builder.position_at_end(hbb);
                let ctx = self.ctx_val();
                let class = self.mem_load(ctx, CTX_EXC_CLASS, MemKind::Ctx)?;
                let reason = self.mem_load(ctx, CTX_EXC_REASON, MemKind::Ctx)?;
                let mut hscope = scope.clone();
                self.bind_try_evars(&mut hscope, evars, class, reason)?;
                let hv = self.compile_value(f, handler, &mut hscope)?;
                let handler_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(merge).map_err(be)?;

                self.builder.position_at_end(merge);
                let phi = self.builder.build_phi(self.i64t, "try.val").map_err(be)?;
                phi.add_incoming(&[(&bv, body_end), (&hv, handler_end)]);
                Ok(phi.as_basic_value().into_int_value())
            }
            Expr::Apply { target, args } => {
                let (call, may_raise) = self.compile_apply(f, target, args, scope, false)?;
                let v = call_result(call)?.into_int_value();
                if may_raise {
                    self.check_exc(f, v)
                } else {
                    Ok(v)
                }
            }
            Expr::Call { module, name, args } => {
                if is_bif_module(module) {
                    self.compile_bif(f, module, name, args, scope)
                } else {
                    let callee = self.remote_fn(module, name, args.len());
                    let may_raise = self.raise_set.contains(&(
                        module.clone(),
                        FunName {
                            name: name.clone(),
                            arity: args.len(),
                        },
                    ));
                    let argv = self.eval_args(f, args, scope)?;
                    let call = self.builder.build_call(callee, &argv, "call").map_err(be)?;
                    let v = call_result(call)?.into_int_value();
                    if may_raise {
                        self.check_exc(f, v)
                    } else {
                        Ok(v)
                    }
                }
            }
            Expr::PrimOp { name, args } if is_raise(name) => {
                self.compile_raise(f, name, args, scope)?;
                Ok(self.i64t.get_undef())
            }
            Expr::PrimOp { name, args } if name == "remove_message" && args.is_empty() => {
                self.builder
                    .build_call(
                        self.rt_p_void("mana_rt_recv_remove"),
                        &[self.ctx_val().into()],
                        "",
                    )
                    .map_err(be)?;
                Ok(self.nil())
            }
            Expr::PrimOp { name, args } if name == "recv_next" && args.is_empty() => {
                self.builder
                    .build_call(
                        self.rt_p_void("mana_rt_recv_next"),
                        &[self.ctx_val().into()],
                        "",
                    )
                    .map_err(be)?;
                Ok(self.nil())
            }
            Expr::PrimOp { name, args } if name == "recv_wait_timeout" && args.len() == 1 => {
                let t = self.compile_value(f, &args[0], scope)?;
                let call = self
                    .builder
                    .build_call(
                        self.rt_recv_wait(),
                        &[self.ctx_val().into(), t.into()],
                        "recv.wait",
                    )
                    .map_err(be)?;
                let timed_out = call_result(call)?.into_int_value();
                let c = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        timed_out,
                        self.i64t.const_int(1, false),
                        "timedout",
                    )
                    .map_err(be)?;
                let tr = self.atom_term("true")?;
                let fa = self.atom_term("false")?;
                Ok(self
                    .builder
                    .build_select(c, tr, fa, "waited")
                    .map_err(be)?
                    .into_int_value())
            }
            Expr::PrimOp { name, .. } => Err(format!("unsupported primop {}", name)),
            Expr::Case { arg, clauses } => {
                let vals = self.compile_case_arg(f, arg, clauses, scope)?;
                let merge = self.ctx.append_basic_block(f, "case.merge");
                let mut incoming: Vec<(IntValue<'ctx>, BasicBlock<'ctx>)> = Vec::new();
                self.compile_case(f, &vals, clauses, scope, Some((merge, &mut incoming)))?;
                self.builder.position_at_end(merge);
                let phi = self.builder.build_phi(self.i64t, "case.val").map_err(be)?;
                for (v, bb) in &incoming {
                    phi.add_incoming(&[(v, *bb)]);
                }
                Ok(phi.as_basic_value().into_int_value())
            }
            Expr::Values(_) => Err("multi-value expression outside let/case".into()),
            Expr::Binary(_) => Err("bitstring construction is not supported yet".into()),
            Expr::Map { pairs, update } => {
                match update {
                    None => {
                        // build unsorted, then normalize (pre-publication
                        // mutation: the term hasn't escaped yet)
                        let n = pairs.len();
                        let mut children: Vec<&Expr> = Vec::with_capacity(2 * n);
                        for (k, _, v) in pairs {
                            children.push(k);
                            children.push(v);
                        }
                        let slots = self.eval_all_rooted(f, &children, scope)?;
                        let p = self.alloc_words(1 + 2 * n as u64)?;
                        let header =
                            self.i64t.const_int(((n as u64) << 8) | KIND_MAP, false);
                        self.store_word(p, 0, header)?;
                        for i in 0..n {
                            let k = self.rooted_get(&slots[2 * i])?;
                            self.store_word(p, 1 + i as u64, k)?;
                            let v = self.rooted_get(&slots[2 * i + 1])?;
                            self.store_word(p, 1 + (n + i) as u64, v)?;
                        }
                        let raw = self
                            .builder
                            .build_ptr_to_int(p, self.i64t, "map.raw")
                            .map_err(be)?;
                        let call = self
                            .builder
                            .build_call(
                                self.rt_fn("mana_rt_map_norm", || {
                                    self.i64t.fn_type(
                                        &[BasicMetadataTypeEnum::IntType(self.i64t)],
                                        false,
                                    )
                                }),
                                &[raw.into()],
                                "map",
                            )
                            .map_err(be)?;
                        Ok(call_result(call)?.into_int_value())
                    }
                    Some(base) => {
                        // `=>` = insert-or-replace (erlc rewrites maps:put/3
                        // into these), `:=` = exact (badkey on miss)
                        let mut acc = self.compile_value(f, base, scope)?;
                        for (k, assoc, v) in pairs {
                            let acc_slot =
                                if self.framed() { Some(self.spill(acc)?) } else { None };
                            let kv = self.eval_siblings(f, &[k, v], scope)?;
                            let acc2 = match acc_slot {
                                Some(s) => self.reload(s)?,
                                None => acc,
                            };
                            let helper = match assoc {
                                MapAssoc::Assoc => "mana_rt_map_put",
                                MapAssoc::Exact => "mana_rt_map_update_exact",
                            };
                            let callee = self.rt_fn(helper, || {
                                self.i64t.fn_type(
                                    &[
                                        BasicMetadataTypeEnum::PointerType(self.ptrt),
                                        BasicMetadataTypeEnum::IntType(self.i64t),
                                        BasicMetadataTypeEnum::IntType(self.i64t),
                                        BasicMetadataTypeEnum::IntType(self.i64t),
                                    ],
                                    false,
                                )
                            });
                            let call = self
                                .builder
                                .build_call(
                                    callee,
                                    &[
                                        self.ctx_val().into(),
                                        kv[0].into(),
                                        kv[1].into(),
                                        acc2.into(),
                                    ],
                                    "mup",
                                )
                                .map_err(be)?;
                            let r = call_result(call)?.into_int_value();
                            acc = self.check_exc(f, r)?;
                        }
                        Ok(acc)
                    }
                }
            }
        }
    }

    /// Evaluate sibling expressions left→right; a value is spilled only if
    /// a *later* sibling's evaluation contains a GC point. Returns fresh
    /// values valid at the point of return.
    fn eval_siblings(
        &self,
        f: FunctionValue<'ctx>,
        exprs: &[&Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<Vec<IntValue<'ctx>>> {
        // gc_after[i]: any expr j > i contains a GC point
        let mut gc_after = vec![false; exprs.len()];
        let mut acc = false;
        for i in (0..exprs.len()).rev() {
            gc_after[i] = acc;
            acc = acc || self.expr_gc(&exprs[i]);
        }
        enum Held<'ctx> {
            Val(IntValue<'ctx>),
            Slot(u64),
        }
        let mut held = Vec::with_capacity(exprs.len());
        for (i, e) in exprs.iter().enumerate() {
            if gc_after[i] && self.framed() {
                if let Expr::Var(name) = e {
                    if let Some(Binding::Slot(idx)) = scope.vars.get(name.as_str()) {
                        held.push(Held::Slot(*idx));
                        continue;
                    }
                }
                if matches!(
                    e,
                    Expr::Lit(Literal::Int(_) | Literal::Atom(_) | Literal::Nil)
                ) {
                    held.push(Held::Val(self.compile_value(f, e, scope)?));
                    continue;
                }
                let v = self.compile_value(f, e, scope)?;
                held.push(Held::Slot(self.spill(v)?));
            } else {
                let v = self.compile_value(f, e, scope)?;
                held.push(Held::Val(v));
            }
        }        held.into_iter()
            .map(|h| match h {
                Held::Val(v) => Ok(v),
                Held::Slot(s) => self.reload(s),
            })
            .collect()
    }

    /// Evaluate and root every expression (used when the consumer itself is
    /// an allocation). In frameless functions this can only be reached in
    /// eternal-alloc (raise) mode, where allocation never collects — values
    /// stay in SSA.
    fn eval_all_rooted(
        &self,
        f: FunctionValue<'ctx>,
        exprs: &[&Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<Vec<Rooted<'ctx>>> {
        exprs
            .iter()
            .map(|e| {
                // a variable already in a frame slot IS a root — reuse it;
                // immediates (ints/atoms/nil) never move — keep in SSA
                if let Expr::Var(name) = e {
                    if let Some(Binding::Slot(idx)) = scope.vars.get(name.as_str()) {
                        return Ok(Rooted::Slot(*idx));
                    }
                }
                if matches!(
                    e,
                    Expr::Lit(Literal::Int(_) | Literal::Atom(_) | Literal::Nil)
                ) {
                    return Ok(Rooted::Val(self.compile_value(f, e, scope)?));
                }
                let v = self.compile_value(f, e, scope)?;
                if self.framed() {
                    Ok(Rooted::Slot(self.spill(v)?))
                } else {
                    // frameless: the effect analysis proved no GC point
                    // exists anywhere in this function (raise-path allocs
                    // use the eternal allocator), so SSA is safe
                    Ok(Rooted::Val(v))
                }
            })
            .collect()
    }

    fn rooted_get(&self, r: &Rooted<'ctx>) -> CgResult<IntValue<'ctx>> {
        match r {
            Rooted::Slot(idx) => self.reload(*idx),
            Rooted::Val(v) => Ok(*v),
        }
    }

    /// Arguments for a call: ctx first, then sibling-rule values.
    fn eval_args(
        &self,
        f: FunctionValue<'ctx>,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<Vec<BasicMetadataValueEnum<'ctx>>> {
        let vals = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        let mut argv: Vec<BasicMetadataValueEnum> = vec![self.ctx_val().into()];
        argv.extend(vals.iter().map(|v| BasicMetadataValueEnum::from(*v)));
        Ok(argv)
    }

    /// Compile any `apply`; `tail` pops the frame just before the call.
    /// Returns the call site and whether the callee may raise (tail calls
    /// propagate the sentinel for free via the return value; non-tail
    /// callers must `check_exc`).
    fn compile_apply(
        &self,
        f: FunctionValue<'ctx>,
        target: &ApplyTarget,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
        tail: bool,
    ) -> CgResult<(CallSiteValue<'ctx>, bool)> {
        match target {
            ApplyTarget::LocalFun(fname) => {
                if let Some((lf, cl_slot)) = scope.funs.get(fname).copied() {
                    let mut argv = self.eval_args(f, args, scope)?;
                    let closure = self.reload(cl_slot)?;
                    argv.push(closure.into());
                    if tail {
                        self.pop_frame()?;
                    }
                    let call = self.builder.build_call(lf, &argv, "call").map_err(be)?;
                    Ok((call, true)) // letrec bodies: conservatively may raise
                } else {
                    let callee = self.local_fn(fname)?;
                    let may_raise = self
                        .raise_set
                        .contains(&(self.module_name.clone(), fname.clone()));
                    let argv = self.eval_args(f, args, scope)?;
                    if tail {
                        self.pop_frame()?;
                    }
                    let call = self.builder.build_call(callee, &argv, "call").map_err(be)?;
                    Ok((call, may_raise))
                }
            }
            ApplyTarget::Var(v) => {
                let argv = self.eval_args(f, args, scope)?;
                let fun_val = self.read_var(scope, v)?;
                let call = self.compile_apply_value(f, fun_val, &argv, args.len(), tail)?;
                Ok((call, true))
            }
        }
    }

    /// Apply a fun value: check tag/kind/arity, indirect-call
    /// `(ctx, args..., closure)`.
    fn compile_apply_value(
        &self,
        f: FunctionValue<'ctx>,
        fun_val: IntValue<'ctx>,
        argv: &[BasicMetadataValueEnum<'ctx>],
        nargs: usize,
        tail: bool,
    ) -> CgResult<CallSiteValue<'ctx>> {
        let bad = self.ctx.append_basic_block(f, "badfun");
        let check_hdr = self.ctx.append_basic_block(f, "fun.hdr");
        let good = self.ctx.append_basic_block(f, "fun.call");

        let tag = self.tag_of(fun_val)?;
        let is_boxed = self
            .builder
            .build_int_compare(IntPredicate::EQ, tag, self.i64t.const_zero(), "is.boxed")
            .map_err(be)?;
        self.builder
            .build_conditional_branch(is_boxed, check_hdr, bad)
            .map_err(be)?;

        self.builder.position_at_end(check_hdr);
        let p = self
            .builder
            .build_int_to_ptr(fun_val, self.ptrt, "fun.ptr")
            .map_err(be)?;
        let header = self.load_word(p, 0)?;
        let masked = self
            .builder
            .build_and(header, self.i64t.const_int(0xffff, false), "hdr.ka")
            .map_err(be)?;
        let want = self.i64t.const_int(((nargs as u64) << 8) | KIND_FUN, false);
        let hdr_ok = self
            .builder
            .build_int_compare(IntPredicate::EQ, masked, want, "hdr.ok")
            .map_err(be)?;
        self.builder
            .build_conditional_branch(hdr_ok, good, bad)
            .map_err(be)?;

        self.builder.position_at_end(bad);
        {
            let reason = self.eternal_pair("badfun", fun_val)?;
            let class = self.atom_term("error")?;
            let ctx = self.ctx_val();
            self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
            self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
            let target = self.unwind_target(f)?;
            self.builder.build_unconditional_branch(target).map_err(be)?;
        }

        self.builder.position_at_end(good);
        let code = self.load_word(p, 1)?;
        let code_ptr = self
            .builder
            .build_int_to_ptr(code, self.ptrt, "code.ptr")
            .map_err(be)?;
        let mut full_args = argv.to_vec();
        full_args.push(fun_val.into());
        if tail {
            self.pop_frame()?;
        }
        self.builder
            .build_indirect_call(self.term_fn_type(nargs + 1), code_ptr, &full_args, "apply")
            .map_err(be)
    }

    /// `[header | code | captures...]`, boxed (tag 000). Allocates first,
    /// then reads captures from their variable bindings — safe because the
    /// allocation is the only GC point involved.
    fn make_closure(
        &self,
        code: FunctionValue<'ctx>,
        arity: usize,
        capture_names: &[String],
        scope: &Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let p = self.alloc_words(2 + capture_names.len() as u64)?;
        let header = self.i64t.const_int(
            ((capture_names.len() as u64) << 16) | ((arity as u64) << 8) | KIND_FUN,
            false,
        );
        self.store_word(p, 0, header)?;
        let code_int = self
            .builder
            .build_ptr_to_int(
                code.as_global_value().as_pointer_value(),
                self.i64t,
                "code.addr",
            )
            .map_err(be)?;
        self.store_word(p, 1, code_int)?;
        for (i, name) in capture_names.iter().enumerate() {
            let v = self.read_var(scope, name).map_err(|e| {
                format!("{} (captured by fun)", e)
            })?;
            self.store_word(p, 2 + i as u64, v)?;
        }
        self.builder
            .build_ptr_to_int(p, self.i64t, "fun")
            .map_err(be)
    }

    fn declare_lift(&self, hint: &str, arity: usize) -> usize {
        let n = self.lift_counter.get();
        self.lift_counter.set(n + 1);
        let name = format!(
            "mn_{}.l{}.{}",
            sanitize(&self.module_name),
            n,
            sanitize(hint)
        );
        let f = self
            .module
            .add_function(&name, self.term_fn_type(arity + 1), None);
        f.set_linkage(Linkage::Internal);
        let mut lifted = self.lifted.borrow_mut();
        lifted.push(f);
        lifted.len() - 1
    }

    /// Lift a letrec group: one shared capture environment, direct calls
    /// among members. Returns the scope extended with the group's funs.
    fn bind_letrec(
        &self,
        _f: FunctionValue<'ctx>,
        defs: &[(FunName, Fun)],
        scope: &Scope<'ctx>,
    ) -> CgResult<Scope<'ctx>> {
        let mut free: BTreeSet<String> = BTreeSet::new();
        for (_, fun) in defs {
            let mut bound: HashSet<String> = fun.params.iter().cloned().collect();
            free_vars(&fun.body, &mut bound, &mut free);
        }
        let free: Vec<String> = free.into_iter().collect();

        let indices: Vec<usize> = defs
            .iter()
            .map(|(fname, fun)| {
                self.declare_lift(
                    &format!("{}_{}", fname.name, fname.arity),
                    fun.params.len(),
                )
            })
            .collect();
        let sibs: Vec<(FunName, usize)> = defs
            .iter()
            .map(|(fname, _)| fname.clone())
            .zip(indices.iter().copied())
            .collect();

        // One closure object shared by the whole group for direct calls;
        // its code pointer (first member) is never used via apply.
        let first = self.lifted.borrow()[indices[0]];
        let closure = self.make_closure(first, defs[0].1.params.len(), &free, scope)?;
        let cl_slot = self.spill(closure)?;

        for ((_, fun), idx) in defs.iter().zip(indices.iter()) {
            self.pending.borrow_mut().push(Lift {
                f_index: *idx,
                params: fun.params.clone(),
                captures: free.clone(),
                sibs: sibs.clone(),
                body: fun.body.clone(),
            });
        }

        let mut inner = scope.clone();
        for (fname, idx) in &sibs {
            let lf = self.lifted.borrow()[*idx];
            inner.funs.insert(fname.clone(), (lf, cl_slot));
        }
        Ok(inner)
    }

    /// A shim adapting a plain top-level function to the closure calling
    /// convention. Frameless: it holds no live terms across the call.
    fn fun_shim(&self, module: Option<&str>, fname: &FunName) -> CgResult<FunctionValue<'ctx>> {
        let target_mod = module.unwrap_or(&self.module_name);
        let sym = format!("{}.shim", mangle(target_mod, fname));
        if let Some(existing) = self.module.get_function(&sym) {
            return Ok(existing);
        }
        let shim = self
            .module
            .add_function(&sym, self.term_fn_type(fname.arity + 1), None);
        shim.set_linkage(Linkage::LinkOnceODR);

        let target = if module.is_none() || module == Some(self.module_name.as_str()) {
            self.local_fn(fname)?
        } else {
            self.remote_fn(target_mod, &fname.name, fname.arity)
        };

        let saved = self.builder.get_insert_block();
        let bb = self.ctx.append_basic_block(shim, "entry");
        self.builder.position_at_end(bb);
        let argv: Vec<BasicMetadataValueEnum> = (0..=fname.arity)
            .map(|i| shim.get_nth_param(i as u32).unwrap().into())
            .collect(); // ctx + args, dropping the trailing closure param
        let call = self.builder.build_call(target, &argv, "fwd").map_err(be)?;
        call.set_tail_call(true);
        let v = call_result(call)?;
        self.builder.build_return(Some(&v)).map_err(be)?;
        if let Some(bb) = saved {
            self.builder.position_at_end(bb);
        }
        Ok(shim)
    }

    /// Bind try-catch variables: `<Class, Reason, Stk>` (3), `<Class,
    /// Reason>` (2) or `<Reason>` (1). The stacktrace slot carries the class
    /// atom so `primop raise(Stk, Reason)` re-raises with the right class
    /// (TODO(stacktraces)).
    fn bind_try_evars(
        &self,
        scope: &mut Scope<'ctx>,
        evars: &[String],
        class: IntValue<'ctx>,
        reason: IntValue<'ctx>,
    ) -> CgResult<()> {
        match evars.len() {
            1 => self.bind_var(scope, &evars[0], reason),
            2 => {
                self.bind_var(scope, &evars[0], class)?;
                self.bind_var(scope, &evars[1], reason)
            }
            3 => {
                self.bind_var(scope, &evars[0], class)?;
                self.bind_var(scope, &evars[1], reason)?;
                self.bind_var(scope, &evars[2], class)
            }
            n => Err(format!("try with {} catch variables is not supported", n)),
        }
    }

    /// (term, term) -> i64 runtime helper.
    fn rt_tt_i64(&self, name: &str) -> FunctionValue<'ctx> {
        self.rt_fn(name, || {
            self.i64t.fn_type(
                &[
                    BasicMetadataTypeEnum::IntType(self.i64t),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    fn bool_term(&self, cond: IntValue<'ctx>) -> CgResult<IntValue<'ctx>> {
        let t = self.atom_term("true")?;
        let fa = self.atom_term("false")?;
        Ok(self
            .builder
            .build_select(cond, t, fa, "bool")
            .map_err(be)?
            .into_int_value())
    }

    /// Branch to a fresh block that raises `error:badarg` unless `ok`.
    fn guard_badarg(
        &self,
        f: FunctionValue<'ctx>,
        ok: IntValue<'ctx>,
    ) -> CgResult<()> {
        let bad = self.ctx.append_basic_block(f, "badarg");
        let cont = self.ctx.append_basic_block(f, "ok");
        self.builder
            .build_conditional_branch(ok, cont, bad)
            .map_err(be)?;
        self.builder.position_at_end(bad);
        let class = self.atom_term("error")?;
        let reason = self.atom_term("badarg")?;
        let ctx = self.ctx_val();
        self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
        self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
        let target = self.unwind_target(f)?;
        self.builder.build_unconditional_branch(target).map_err(be)?;
        self.builder.position_at_end(cont);
        Ok(())
    }

    /// `boxed(v) && header.kind == kind` as an i1, via control flow.
    fn kind_test(
        &self,
        f: FunctionValue<'ctx>,
        v: IntValue<'ctx>,
        test: impl FnOnce(&Self, IntValue<'ctx>) -> CgResult<IntValue<'ctx>>,
    ) -> CgResult<IntValue<'ctx>> {
        let entry = self.builder.get_insert_block().unwrap();
        let boxed_bb = self.ctx.append_basic_block(f, "kt.boxed");
        let merge = self.ctx.append_basic_block(f, "kt.merge");
        let tag = self.tag_of(v)?;
        let is_boxed = self
            .builder
            .build_int_compare(IntPredicate::EQ, tag, self.i64t.const_zero(), "kt.tag")
            .map_err(be)?;
        let nonzero = self
            .builder
            .build_int_compare(IntPredicate::NE, v, self.i64t.const_zero(), "kt.nz")
            .map_err(be)?;
        let okptr = self.builder.build_and(is_boxed, nonzero, "kt.ptr").map_err(be)?;
        self.builder
            .build_conditional_branch(okptr, boxed_bb, merge)
            .map_err(be)?;
        self.builder.position_at_end(boxed_bb);
        let p = self
            .builder
            .build_int_to_ptr(v, self.ptrt, "kt.p")
            .map_err(be)?;
        let header = self.load_word(p, 0)?;
        let inner = test(self, header)?;
        let boxed_end = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(merge).map_err(be)?;
        self.builder.position_at_end(merge);
        let phi = self
            .builder
            .build_phi(self.ctx.bool_type(), "kt.res")
            .map_err(be)?;
        let ff = self.ctx.bool_type().const_zero();
        phi.add_incoming(&[(&ff, entry), (&inner, boxed_end)]);
        Ok(phi.as_basic_value().into_int_value())
    }

    fn compile_literal(&self, l: &Literal) -> CgResult<IntValue<'ctx>> {
        match l {
            Literal::Int(n) => Ok(self.small_int(*n)),
            Literal::Atom(a) => self.atom_term(a),
            Literal::Nil => Ok(self.nil()),
            Literal::Float(x) => {
                let p = self.alloc_words(2)?;
                let header = self.i64t.const_int((1 << 8) | KIND_FLOAT, false);
                self.store_word(p, 0, header)?;
                let bits = self.i64t.const_int(x.to_bits(), false);
                self.store_word(p, 1, bits)?;
                self.builder
                    .build_ptr_to_int(p, self.i64t, "float")
                    .map_err(be)
            }
        }
    }

    fn bind_let(
        &self,
        f: FunctionValue<'ctx>,
        vars: &[String],
        arg: &Expr,
        scope: &mut Scope<'ctx>,
    ) -> CgResult<()> {
        match (vars.len(), arg) {
            (1, _) => {
                let v = self.compile_value(f, arg, scope)?;
                self.bind_var(scope, &vars[0], v)
            }
            (2, Expr::PrimOp { name, args })
                if name == "recv_peek_message" && args.is_empty() =>
            {
                let call = self
                    .builder
                    .build_call(
                        self.rt_p_i64("mana_rt_recv_ready"),
                        &[self.ctx_val().into()],
                        "recv.ready",
                    )
                    .map_err(be)?;
                let ready = call_result(call)?.into_int_value();
                let c = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        ready,
                        self.i64t.const_int(1, false),
                        "has.msg",
                    )
                    .map_err(be)?;
                let tr = self.atom_term("true")?;
                let fa = self.atom_term("false")?;
                let flag = self
                    .builder
                    .build_select(c, tr, fa, "ready")
                    .map_err(be)?
                    .into_int_value();
                self.bind_var(scope, &vars[0], flag)?;
                let call = self
                    .builder
                    .build_call(
                        self.rt_p_i64("mana_rt_recv_peek"),
                        &[self.ctx_val().into()],
                        "recv.msg",
                    )
                    .map_err(be)?;
                let msg = call_result(call)?.into_int_value();
                self.bind_var(scope, &vars[1], msg)?;
                Ok(())
            }
            (_, Expr::Values(es)) if es.len() == vars.len() => {
                for (var, e) in vars.iter().zip(es) {
                    let v = self.compile_value(f, e, scope)?;
                    self.bind_var(scope, var, v)?;
                }
                Ok(())
            }
            _ => Err("multi-value let from a non-values expression is not supported".into()),
        }
    }

    /// Case scrutinees. If any guard contains a GC point, values must be
    /// re-loadable per clause (later clauses re-match after the guard ran),
    /// so everything goes to slots; otherwise plain sibling evaluation.
    fn compile_case_arg(
        &self,
        f: FunctionValue<'ctx>,
        arg: &Expr,
        clauses: &[Clause],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<CaseVals<'ctx>> {
        let exprs: Vec<&Expr> = match arg {
            Expr::Values(es) => es.iter().collect(),
            other => vec![other],
        };
        let any_guard_gc = clauses.iter().any(|c| self.expr_gc(&c.guard));
        if any_guard_gc && self.framed() {
            let slots = exprs
                .iter()
                .map(|e| {
                    let v = self.compile_value(f, e, scope)?;
                    self.spill(v)
                })
                .collect::<CgResult<Vec<_>>>()?;
            Ok(CaseVals::Slots(slots))
        } else {
            Ok(CaseVals::Ssa(self.eval_siblings(f, &exprs, scope)?))
        }
    }

    fn compile_case(
        &self,
        f: FunctionValue<'ctx>,
        vals: &CaseVals<'ctx>,
        clauses: &[Clause],
        scope: &Scope<'ctx>,
        mut merge: Option<(BasicBlock<'ctx>, &mut Vec<(IntValue<'ctx>, BasicBlock<'ctx>)>)>,
    ) -> CgResult<()> {
        let fail_bb = self.ctx.append_basic_block(f, "case.nomatch");
        let mut next = self.ctx.append_basic_block(f, "clause0");
        self.builder.build_unconditional_branch(next).map_err(be)?;

        for (i, clause) in clauses.iter().enumerate() {
            self.builder.position_at_end(next);
            next = if i + 1 < clauses.len() {
                self.ctx.append_basic_block(f, &format!("clause{}", i + 1))
            } else {
                fail_bb
            };
            let vs: Vec<IntValue<'ctx>> = match vals {
                CaseVals::Ssa(vs) => vs.clone(),
                CaseVals::Slots(slots) => slots
                    .iter()
                    .map(|s| self.reload(*s))
                    .collect::<CgResult<_>>()?,
            };
            if clause.patterns.len() != vs.len() {
                return Err(format!(
                    "clause has {} patterns but case argument has {} values",
                    clause.patterns.len(),
                    vs.len()
                ));
            }
            let mut cscope = scope.clone();
            for (v, p) in vs.iter().zip(&clause.patterns) {
                self.match_pattern(f, *v, p, &mut cscope, next)?;
            }
            if !is_true_atom(&clause.guard) {
                let g = self.compile_value(f, &clause.guard, &mut cscope)?;
                let t = self.atom_term("true")?;
                let ok = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, g, t, "guard.ok")
                    .map_err(be)?;
                let body_bb = self.ctx.append_basic_block(f, &format!("body{}", i));
                self.builder
                    .build_conditional_branch(ok, body_bb, next)
                    .map_err(be)?;
                self.builder.position_at_end(body_bb);
            }
            match merge {
                None => self.compile_tail(f, &clause.body, &mut cscope)?,
                Some((merge_bb, ref mut incoming)) => {
                    let v = self.compile_value(f, &clause.body, &mut cscope)?;
                    let cur = self.builder.get_insert_block().unwrap();
                    incoming.push((v, cur));
                    self.builder
                        .build_unconditional_branch(merge_bb)
                        .map_err(be)?;
                }
            }
        }

        self.builder.position_at_end(fail_bb);
        {
            let v0 = match vals {
                CaseVals::Ssa(vs) => vs.first().copied().unwrap_or_else(|| self.nil()),
                CaseVals::Slots(slots) => match slots.first() {
                    Some(s) => self.reload(*s)?,
                    None => self.nil(),
                },
            };
            let reason = self.eternal_pair("case_clause", v0)?;
            let class = self.atom_term("error")?;
            let ctx = self.ctx_val();
            self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
            self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
            let target = self.unwind_target(f)?;
            self.builder.build_unconditional_branch(target).map_err(be)?;
        }
        Ok(())
    }

    /// Emit tests for `pat` against `val`, branching to `fail` on mismatch.
    /// No allocation happens inside a pattern, so SSA subterm loads are safe.
    fn match_pattern(
        &self,
        f: FunctionValue<'ctx>,
        val: IntValue<'ctx>,
        pat: &Pattern,
        scope: &mut Scope<'ctx>,
        fail: BasicBlock<'ctx>,
    ) -> CgResult<()> {
        match pat {
            Pattern::Var(v) => self.bind_var(scope, v, val),
            Pattern::Alias(v, inner) => {
                self.bind_var(scope, v, val)?;
                self.match_pattern(f, val, inner, scope, fail)
            }
            Pattern::Lit(Literal::Float(_)) => Err("float patterns not supported yet".into()),
            Pattern::Binary(_) => Err("bitstring patterns are not supported yet".into()),
            Pattern::Map(pairs) => {
                // no allocation inside a pattern: keys must be literals or
                // vars; the lookup helper is non-allocating
                for (k, sub) in pairs {
                    let key = self.compile_value(f, k, scope)?;
                    let call = self
                        .builder
                        .build_call(
                            self.rt_tt_i64("mana_rt_map_pat_get"),
                            &[val.into(), key.into()],
                            "mpat",
                        )
                        .map_err(be)?;
                    let v = call_result(call)?.into_int_value();
                    let hit = self
                        .builder
                        .build_int_compare(IntPredicate::NE, v, self.sentinel(), "mpat.h")
                        .map_err(be)?;
                    self.branch_test(f, hit, fail)?;
                    self.match_pattern(f, v, sub, scope, fail)?;
                }
                Ok(())
            }
            Pattern::Lit(l) => {
                let expect = self.compile_literal(l)?;
                let eq = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, val, expect, "lit.eq")
                    .map_err(be)?;
                self.branch_test(f, eq, fail)
            }
            Pattern::Tuple(ps) => {
                let tag = self.tag_of(val)?;
                let is_boxed = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_zero(),
                        "is.boxed",
                    )
                    .map_err(be)?;
                self.branch_test(f, is_boxed, fail)?;
                let p = self
                    .builder
                    .build_int_to_ptr(val, self.ptrt, "tuple.ptr")
                    .map_err(be)?;
                let header = self.load_word(p, 0)?;
                let want = self
                    .i64t
                    .const_int(((ps.len() as u64) << 8) | KIND_TUPLE, false);
                let hdr_ok = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, header, want, "hdr.ok")
                    .map_err(be)?;
                self.branch_test(f, hdr_ok, fail)?;
                for (i, sub) in ps.iter().enumerate() {
                    let elem = self.load_word(p, 1 + i as u64)?;
                    self.match_pattern(f, elem, sub, scope, fail)?;
                }
                Ok(())
            }
            Pattern::Cons(h, t) => {
                let tag = self.tag_of(val)?;
                let is_cons = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_int(TAG_CONS, false),
                        "is.cons",
                    )
                    .map_err(be)?;
                self.branch_test(f, is_cons, fail)?;
                let addr = self
                    .builder
                    .build_and(val, self.i64t.const_int(!TAG_MASK, false), "cons.addr")
                    .map_err(be)?;
                let p = self
                    .builder
                    .build_int_to_ptr(addr, self.ptrt, "cons.ptr")
                    .map_err(be)?;
                let head = self.load_word(p, 0)?;
                self.match_pattern(f, head, h, scope, fail)?;
                let tail = self.load_word(p, 1)?;
                self.match_pattern(f, tail, t, scope, fail)
            }
        }
    }

    fn branch_test(
        &self,
        f: FunctionValue<'ctx>,
        cond: IntValue<'ctx>,
        fail: BasicBlock<'ctx>,
    ) -> CgResult<()> {
        let cont = self.ctx.append_basic_block(f, "m.cont");
        self.builder
            .build_conditional_branch(cond, cont, fail)
            .map_err(be)?;
        self.builder.position_at_end(cont);
        Ok(())
    }

    // ---- BIFs (none allocate today; TODO(bignum) changes that) ----

    fn compile_bif(
        &self,
        f: FunctionValue<'ctx>,
        module: &str,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        if module == "maps" {
            return self.compile_maps_bif(f, name, args, scope);
        }
        // raising BIFs: reason terms use the eternal allocator so raise
        // paths don't create GC points
        if matches!(
            (name, args.len()),
            ("error", 1) | ("error", 2) | ("exit", 1) | ("throw", 1)
        ) {
            self.compile_raise(f, name, args, scope)?;
            return Ok(self.i64t.get_undef());
        }

        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;

        match (name, argv.len()) {
            ("+", 2) | ("-", 2) | ("*", 2) | ("div", 2) | ("rem", 2) => {
                let a = self.untag_int(argv[0])?;
                let b = self.untag_int(argv[1])?;
                let r = match name {
                    "+" => self.builder.build_int_add(a, b, "add"),
                    "-" => self.builder.build_int_sub(a, b, "sub"),
                    "*" => self.builder.build_int_mul(a, b, "mul"),
                    "div" => self.builder.build_int_signed_div(a, b, "div"),
                    _ => self.builder.build_int_signed_rem(a, b, "rem"),
                }
                .map_err(be)?;
                self.retag_int(r)
            }
            ("-", 1) => {
                let a = self.untag_int(argv[0])?;
                let r = self
                    .builder
                    .build_int_sub(self.i64t.const_zero(), a, "neg")
                    .map_err(be)?;
                self.retag_int(r)
            }
            ("+", 1) => Ok(argv[0]),
            ("<", 2) | ("=<", 2) | (">", 2) | (">=", 2) | ("==", 2) | ("/=", 2)
            | ("=:=", 2) | ("=/=", 2) => {
                // fast path: both small ints (tagging is order-preserving);
                // slow path: full Erlang term order in the runtime
                let pred = match name {
                    "<" => IntPredicate::SLT,
                    "=<" => IntPredicate::SLE,
                    ">" => IntPredicate::SGT,
                    ">=" => IntPredicate::SGE,
                    "==" | "=:=" => IntPredicate::EQ,
                    _ => IntPredicate::NE,
                };
                let (a, b) = (argv[0], argv[1]);
                let one = self.i64t.const_int(1, false);
                let ta = self.tag_of(a)?;
                let tb = self.tag_of(b)?;
                let sa = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, ta, one, "sa")
                    .map_err(be)?;
                let sb = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, tb, one, "sb")
                    .map_err(be)?;
                let both = self.builder.build_and(sa, sb, "both.small").map_err(be)?;
                let fast = self.ctx.append_basic_block(f, "cmp.fast");
                let slow = self.ctx.append_basic_block(f, "cmp.slow");
                let merge = self.ctx.append_basic_block(f, "cmp.merge");
                self.builder
                    .build_conditional_branch(both, fast, slow)
                    .map_err(be)?;

                self.builder.position_at_end(fast);
                let cf = self
                    .builder
                    .build_int_compare(pred, a, b, "cmp.i")
                    .map_err(be)?;
                let vf = self.bool_term(cf)?;
                let fast_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(merge).map_err(be)?;

                self.builder.position_at_end(slow);
                let vs = match name {
                    "=:=" | "=/=" => {
                        let call = self
                            .builder
                            .build_call(
                                self.rt_tt_i64("mana_rt_eq_exact"),
                                &[a.into(), b.into()],
                                "eqx",
                            )
                            .map_err(be)?;
                        let r = call_result(call)?.into_int_value();
                        let want = if name == "=:=" { 1 } else { 0 };
                        let c = self
                            .builder
                            .build_int_compare(
                                IntPredicate::EQ,
                                r,
                                self.i64t.const_int(want, false),
                                "eqx.c",
                            )
                            .map_err(be)?;
                        self.bool_term(c)?
                    }
                    _ => {
                        let call = self
                            .builder
                            .build_call(
                                self.rt_tt_i64("mana_rt_compare"),
                                &[a.into(), b.into()],
                                "ord",
                            )
                            .map_err(be)?;
                        let r = call_result(call)?.into_int_value();
                        let c = self
                            .builder
                            .build_int_compare(pred, r, self.i64t.const_zero(), "ord.c")
                            .map_err(be)?;
                        self.bool_term(c)?
                    }
                };
                let slow_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(merge).map_err(be)?;

                self.builder.position_at_end(merge);
                let phi = self.builder.build_phi(self.i64t, "cmp.v").map_err(be)?;
                phi.add_incoming(&[(&vf, fast_end), (&vs, slow_end)]);
                Ok(phi.as_basic_value().into_int_value())
            }
            ("self", 0) => {
                let call = self
                    .builder
                    .build_call(self.rt_p_i64("mana_rt_self"), &[self.ctx_val().into()], "self")
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("spawn", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_spawn(),
                        &[self.ctx_val().into(), argv[0].into()],
                        "spawn",
                    )
                    .map_err(be)?;
                let pid = call_result(call)?.into_int_value();
                // 0 = not an arity-0 fun
                let bad = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, pid, self.i64t.const_zero(), "spawn.bad")
                    .map_err(be)?;
                let bad_bb = self.ctx.append_basic_block(f, "spawn.badarg");
                let ok_bb = self.ctx.append_basic_block(f, "spawn.ok");
                self.builder
                    .build_conditional_branch(bad, bad_bb, ok_bb)
                    .map_err(be)?;
                self.builder.position_at_end(bad_bb);
                let class = self.atom_term("error")?;
                let reason = self.atom_term("badarg")?;
                let ctx = self.ctx_val();
                self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
                self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
                let target = self.unwind_target(f)?;
                self.builder.build_unconditional_branch(target).map_err(be)?;
                self.builder.position_at_end(ok_bb);
                Ok(pid)
            }
            ("make_ref", 0) => {
                let call = self
                    .builder
                    .build_call(self.rt_p_i64("mana_rt_make_ref"), &[self.ctx_val().into()], "r")
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("link", 1) => {
                self.builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_link"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "",
                    )
                    .map_err(be)?;
                self.atom_term("true")
            }
            ("unlink", 1) => {
                self.builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_unlink"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "",
                    )
                    .map_err(be)?;
                self.atom_term("true")
            }
            ("monitor", 2) => {
                // monitor(process, Pid) — first arg assumed 'process'
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_monitor"),
                        &[self.ctx_val().into(), argv[1].into()],
                        "mref",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("demonitor", 1) => {
                self.builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_demonitor"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "",
                    )
                    .map_err(be)?;
                self.atom_term("true")
            }
            ("spawn_link", 1) | ("spawn_monitor", 1) => {
                let fname = if name == "spawn_link" {
                    "mana_rt_spawn_link"
                } else {
                    "mana_rt_spawn_monitor"
                };
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64(fname),
                        &[self.ctx_val().into(), argv[0].into()],
                        "sp",
                    )
                    .map_err(be)?;
                let r = call_result(call)?.into_int_value();
                let bad = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, r, self.i64t.const_zero(), "sp.bad")
                    .map_err(be)?;
                let bad_bb = self.ctx.append_basic_block(f, "sp.badarg");
                let ok_bb = self.ctx.append_basic_block(f, "sp.ok");
                self.builder
                    .build_conditional_branch(bad, bad_bb, ok_bb)
                    .map_err(be)?;
                self.builder.position_at_end(bad_bb);
                let class = self.atom_term("error")?;
                let reason = self.atom_term("badarg")?;
                let ctx = self.ctx_val();
                self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
                self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
                let target = self.unwind_target(f)?;
                self.builder.build_unconditional_branch(target).map_err(be)?;
                self.builder.position_at_end(ok_bb);
                Ok(r)
            }
            ("process_flag", 2) => {
                // only trap_exit is supported; the flag name is ignored
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_trap_exit"),
                        &[self.ctx_val().into(), argv[1].into()],
                        "prev",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("exit", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_fn("mana_rt_exit2", || {
                            self.i64t.fn_type(
                                &[
                                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                ],
                                false,
                            )
                        }),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "",
                    )
                    .map_err(be)?;
                let _ = call;
                self.atom_term("true")
            }
            ("!", 2) | ("send", 2) => {
                self.builder
                    .build_call(
                        self.rt_send(),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "",
                    )
                    .map_err(be)?;
                Ok(argv[1])
            }
            ("and", 2) | ("or", 2) | ("xor", 2) => {
                let t = self.atom_term("true")?;
                let a = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, argv[0], t, "a")
                    .map_err(be)?;
                let b = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, argv[1], t, "b")
                    .map_err(be)?;
                let r = match name {
                    "and" => self.builder.build_and(a, b, "and"),
                    "or" => self.builder.build_or(a, b, "or"),
                    _ => self.builder.build_xor(a, b, "xor"),
                }
                .map_err(be)?;
                let fa = self.atom_term("false")?;
                Ok(self
                    .builder
                    .build_select(r, t, fa, "bool")
                    .map_err(be)?
                    .into_int_value())
            }
            ("not", 1) => {
                let t = self.atom_term("true")?;
                let fa = self.atom_term("false")?;
                let a = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, argv[0], t, "a")
                    .map_err(be)?;
                Ok(self
                    .builder
                    .build_select(a, fa, t, "not")
                    .map_err(be)?
                    .into_int_value())
            }
            ("is_integer", 1) | ("is_atom", 1) | ("is_pid", 1) | ("is_reference", 1) => {
                let want: u64 = match name {
                    "is_integer" => 1,
                    "is_atom" => 2,
                    "is_pid" => 0b0110,
                    _ => 0b1110,
                };
                let mask: u64 = if name == "is_pid" || name == "is_reference" {
                    0xF
                } else {
                    7
                };
                let m = self
                    .builder
                    .build_and(argv[0], self.i64t.const_int(mask, false), "tt")
                    .map_err(be)?;
                let c = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        m,
                        self.i64t.const_int(want, false),
                        "tt.c",
                    )
                    .map_err(be)?;
                self.bool_term(c)
            }
            ("is_list", 1) => {
                let tag = self.tag_of(argv[0])?;
                let cons = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_int(0b100, false),
                        "il.c",
                    )
                    .map_err(be)?;
                let nil = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, argv[0], self.nil(), "il.n")
                    .map_err(be)?;
                let c = self.builder.build_or(cons, nil, "il").map_err(be)?;
                self.bool_term(c)
            }
            ("is_boolean", 1) => {
                let t = self.atom_term("true")?;
                let fa = self.atom_term("false")?;
                let a = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, argv[0], t, "ib.t")
                    .map_err(be)?;
                let b = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, argv[0], fa, "ib.f")
                    .map_err(be)?;
                let c = self.builder.build_or(a, b, "ib").map_err(be)?;
                self.bool_term(c)
            }
            ("is_tuple", 1) | ("is_float", 1) | ("is_function", 1) => {
                let kind: u64 = match name {
                    "is_tuple" => KIND_TUPLE,
                    "is_float" => KIND_FLOAT,
                    _ => KIND_FUN,
                };
                let c = self.kind_test(f, argv[0], |s, header| {
                    let k = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xff, false), "k")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            k,
                            s.i64t.const_int(kind, false),
                            "k.c",
                        )
                        .map_err(be)
                })?;
                self.bool_term(c)
            }
            ("is_function", 2) => {
                let arity = argv[1];
                let c = self.kind_test(f, argv[0], |s, header| {
                    let ka = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xffff, false), "ka")
                        .map_err(be)?;
                    let want_lo = s
                        .builder
                        .build_right_shift(arity, s.i64t.const_int(3, false), true, "ar")
                        .map_err(be)?;
                    let want = s
                        .builder
                        .build_left_shift(want_lo, s.i64t.const_int(8, false), "ar8")
                        .map_err(be)?;
                    let want = s
                        .builder
                        .build_or(want, s.i64t.const_int(KIND_FUN, false), "want")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(IntPredicate::EQ, ka, want, "isf2")
                        .map_err(be)
                })?;
                self.bool_term(c)
            }
            ("is_number", 1) => {
                let tag = self.tag_of(argv[0])?;
                let small = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_int(1, false),
                        "n.s",
                    )
                    .map_err(be)?;
                let isf = self.kind_test(f, argv[0], |s, header| {
                    let k = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xff, false), "k")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            k,
                            s.i64t.const_int(KIND_FLOAT, false),
                            "k.f",
                        )
                        .map_err(be)
                })?;
                let c = self.builder.build_or(small, isf, "isnum").map_err(be)?;
                self.bool_term(c)
            }
            ("is_binary", 1) | ("is_bitstring", 1) | ("is_port", 1) => {
                // no such terms yet (S3)
                self.atom_term("false")
            }
            ("is_map", 1) => {
                let c = self.kind_test(f, argv[0], |s, header| {
                    let k = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xff, false), "k")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            k,
                            s.i64t.const_int(KIND_MAP, false),
                            "k.m",
                        )
                        .map_err(be)
                })?;
                self.bool_term(c)
            }
            ("map_size", 1) => self.map_size_of(f, argv[0]),
            ("map_get", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_map_get"),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "mg",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("is_map_key", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_map_is_key"),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "mk",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("element", 2) => {
                // element(I, Tuple), 1-based; badarg on any misuse
                let (i, t) = (argv[0], argv[1]);
                let ti = self.tag_of(i)?;
                let i_ok = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        ti,
                        self.i64t.const_int(1, false),
                        "el.i",
                    )
                    .map_err(be)?;
                let is_tup = self.kind_test(f, t, |s, header| {
                    let k = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xff, false), "k")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            k,
                            s.i64t.const_int(KIND_TUPLE, false),
                            "k.t",
                        )
                        .map_err(be)
                })?;
                let ok = self.builder.build_and(i_ok, is_tup, "el.ok").map_err(be)?;
                self.guard_badarg(f, ok)?;
                let p = self
                    .builder
                    .build_int_to_ptr(t, self.ptrt, "el.p")
                    .map_err(be)?;
                let header = self.load_word(p, 0)?;
                let arity = self
                    .builder
                    .build_right_shift(header, self.i64t.const_int(8, false), false, "el.n")
                    .map_err(be)?;
                let idx = self.untag_int(i)?;
                let ge1 = self
                    .builder
                    .build_int_compare(
                        IntPredicate::SGE,
                        idx,
                        self.i64t.const_int(1, false),
                        "el.ge",
                    )
                    .map_err(be)?;
                let le = self
                    .builder
                    .build_int_compare(IntPredicate::SLE, idx, arity, "el.le")
                    .map_err(be)?;
                let in_range = self.builder.build_and(ge1, le, "el.rng").map_err(be)?;
                self.guard_badarg(f, in_range)?;
                let slot = unsafe {
                    self.builder
                        .build_in_bounds_gep(self.i64t, p, &[idx], "el.slot")
                        .map_err(be)?
                };
                let v = self
                    .builder
                    .build_load(self.i64t, slot, "el.v")
                    .map_err(be)?;
                if let Some(inst) = v.as_instruction_value() {
                    let _ = inst.set_metadata(self.tbaa_heap, self.tbaa_kind);
                }
                Ok(v.into_int_value())
            }
            ("tuple_size", 1) => {
                let is_tup = self.kind_test(f, argv[0], |s, header| {
                    let k = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xff, false), "k")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            k,
                            s.i64t.const_int(KIND_TUPLE, false),
                            "k.t",
                        )
                        .map_err(be)
                })?;
                self.guard_badarg(f, is_tup)?;
                let p = self
                    .builder
                    .build_int_to_ptr(argv[0], self.ptrt, "ts.p")
                    .map_err(be)?;
                let header = self.load_word(p, 0)?;
                let n = self
                    .builder
                    .build_right_shift(header, self.i64t.const_int(8, false), false, "ts.n")
                    .map_err(be)?;
                self.retag_int(n)
            }
            ("hd", 1) | ("tl", 1) => {
                let tag = self.tag_of(argv[0])?;
                let is_cons = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_int(0b100, false),
                        "ht.c",
                    )
                    .map_err(be)?;
                self.guard_badarg(f, is_cons)?;
                let addr = self
                    .builder
                    .build_and(argv[0], self.i64t.const_int(!TAG_MASK, false), "ht.a")
                    .map_err(be)?;
                let p = self
                    .builder
                    .build_int_to_ptr(addr, self.ptrt, "ht.p")
                    .map_err(be)?;
                self.load_word(p, if name == "hd" { 0 } else { 1 })
            }
            ("abs", 1) => {
                let tag = self.tag_of(argv[0])?;
                let ok = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_int(1, false),
                        "abs.i",
                    )
                    .map_err(be)?;
                self.guard_badarg(f, ok)?;
                let v = self.untag_int(argv[0])?;
                let neg = self
                    .builder
                    .build_int_sub(self.i64t.const_zero(), v, "abs.n")
                    .map_err(be)?;
                let isneg = self
                    .builder
                    .build_int_compare(
                        IntPredicate::SLT,
                        v,
                        self.i64t.const_zero(),
                        "abs.c",
                    )
                    .map_err(be)?;
                let r = self
                    .builder
                    .build_select(isneg, neg, v, "abs")
                    .map_err(be)?
                    .into_int_value();
                self.retag_int(r)
            }
            ("min", 2) | ("max", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_tt_i64("mana_rt_compare"),
                        &[argv[0].into(), argv[1].into()],
                        "mm",
                    )
                    .map_err(be)?;
                let r = call_result(call)?.into_int_value();
                let pred = if name == "min" {
                    IntPredicate::SLE
                } else {
                    IntPredicate::SGE
                };
                let c = self
                    .builder
                    .build_int_compare(pred, r, self.i64t.const_zero(), "mm.c")
                    .map_err(be)?;
                Ok(self
                    .builder
                    .build_select(c, argv[0], argv[1], "mm.v")
                    .map_err(be)?
                    .into_int_value())
            }
            ("setelement", 3) | ("length", 1) | ("++", 2) | ("--", 2) => {
                let (fname, args_ll): (&str, Vec<BasicMetadataValueEnum>) = match name {
                    "setelement" => (
                        "mana_rt_setelement",
                        vec![
                            self.ctx_val().into(),
                            argv[0].into(),
                            argv[1].into(),
                            argv[2].into(),
                        ],
                    ),
                    "length" => (
                        "mana_rt_length",
                        vec![self.ctx_val().into(), argv[0].into()],
                    ),
                    "++" => (
                        "mana_rt_append",
                        vec![self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    ),
                    _ => (
                        "mana_rt_subtract",
                        vec![self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    ),
                };
                let nargs = args_ll.len();
                let callee = self.rt_fn(fname, || {
                    let mut params: Vec<BasicMetadataTypeEnum> =
                        vec![BasicMetadataTypeEnum::PointerType(self.ptrt)];
                    params.extend(
                        (1..nargs).map(|_| BasicMetadataTypeEnum::IntType(self.i64t)),
                    );
                    self.i64t.fn_type(&params, false)
                });
                let call = self.builder.build_call(callee, &args_ll, "rtb").map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("display", 1) => {
                self.builder
                    .build_call(self.rt_display(), &[argv[0].into()], "")
                    .map_err(be)?;
                self.atom_term("true")
            }
            _ => Err(format!("unsupported BIF erlang:{}/{}", name, argv.len())),
        }
    }

    /// Raise an exception: primop match_fail/raise or erlang:error|exit|throw.
    /// Reason terms are built with the eternal allocator (never moved, GC
    /// scans their fields). Leaves the builder in a dead block.
    /// (ctx, term, term) -> term runtime helper.
    fn rt_ptt_i64(&self, name: &str) -> FunctionValue<'ctx> {
        self.rt_fn(name, || {
            self.i64t.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    fn compile_maps_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        let ctxv: BasicMetadataValueEnum = self.ctx_val().into();
        match (name, argv.len()) {
            ("get", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_map_get"),
                        &[ctxv, argv[0].into(), argv[1].into()],
                        "mg",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("get", 3) => {
                // miss (or non-map) yields the default — TODO(badmap): a
                // non-map should raise
                let call = self
                    .builder
                    .build_call(
                        self.rt_tt_i64("mana_rt_map_pat_get"),
                        &[argv[1].into(), argv[0].into()],
                        "mg3",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                let miss = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, v, self.sentinel(), "mg3.m")
                    .map_err(be)?;
                Ok(self
                    .builder
                    .build_select(miss, argv[2], v, "mg3.v")
                    .map_err(be)?
                    .into_int_value())
            }
            ("find", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_tt_i64("mana_rt_map_pat_get"),
                        &[argv[1].into(), argv[0].into()],
                        "mf",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                let miss = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, v, self.sentinel(), "mf.m")
                    .map_err(be)?;
                let hit_bb = self.ctx.append_basic_block(f, "mf.hit");
                let miss_bb = self.ctx.append_basic_block(f, "mf.miss");
                let merge = self.ctx.append_basic_block(f, "mf.merge");
                self.builder
                    .build_conditional_branch(miss, miss_bb, hit_bb)
                    .map_err(be)?;
                self.builder.position_at_end(hit_bb);
                // {ok, V}: alloc, so root v in a temp slot first
                let vslot = if self.framed() { Some(self.spill(v)?) } else { None };
                let p = self.alloc_words(3)?;
                self.store_word(p, 0, self.i64t.const_int((2 << 8) | KIND_TUPLE, false))?;
                let ok_atom = self.atom_term("ok")?;
                self.store_word(p, 1, ok_atom)?;
                let v2 = match vslot {
                    Some(s) => self.reload(s)?,
                    None => v,
                };
                self.store_word(p, 2, v2)?;
                let tup = self
                    .builder
                    .build_ptr_to_int(p, self.i64t, "mf.t")
                    .map_err(be)?;
                let hit_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(merge).map_err(be)?;
                self.builder.position_at_end(miss_bb);
                let err_atom = self.atom_term("error")?;
                self.builder.build_unconditional_branch(merge).map_err(be)?;
                self.builder.position_at_end(merge);
                let phi = self.builder.build_phi(self.i64t, "mf.v").map_err(be)?;
                phi.add_incoming(&[(&tup, hit_end), (&err_atom, miss_bb)]);
                Ok(phi.as_basic_value().into_int_value())
            }
            ("put", 3) => {
                let callee = self.rt_fn("mana_rt_map_put", || {
                    self.i64t.fn_type(
                        &[
                            BasicMetadataTypeEnum::PointerType(self.ptrt),
                            BasicMetadataTypeEnum::IntType(self.i64t),
                            BasicMetadataTypeEnum::IntType(self.i64t),
                            BasicMetadataTypeEnum::IntType(self.i64t),
                        ],
                        false,
                    )
                });
                let call = self
                    .builder
                    .build_call(
                        callee,
                        &[ctxv, argv[0].into(), argv[1].into(), argv[2].into()],
                        "mp",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("is_key", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_map_is_key"),
                        &[ctxv, argv[0].into(), argv[1].into()],
                        "mk",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("remove", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_map_remove"),
                        &[ctxv, argv[0].into(), argv[1].into()],
                        "mr",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("merge", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_map_merge"),
                        &[ctxv, argv[0].into(), argv[1].into()],
                        "mm",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("from_list", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_map_from_list"),
                        &[ctxv, argv[0].into()],
                        "mfl",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("to_list", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_map_to_list"),
                        &[ctxv, argv[0].into()],
                        "mtl",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("size", 1) => self.map_size_of(f, argv[0]),
            _ => Err(format!("unsupported BIF maps:{}/{}", name, argv.len())),
        }
    }

    fn map_size_of(
        &self,
        f: FunctionValue<'ctx>,
        m: IntValue<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let is_map = self.kind_test(f, m, |s, header| {
            let k = s
                .builder
                .build_and(header, s.i64t.const_int(0xff, false), "k")
                .map_err(be)?;
            s.builder
                .build_int_compare(
                    IntPredicate::EQ,
                    k,
                    s.i64t.const_int(KIND_MAP, false),
                    "k.m",
                )
                .map_err(be)
        })?;
        self.guard_badarg(f, is_map)?;
        let p = self
            .builder
            .build_int_to_ptr(m, self.ptrt, "ms.p")
            .map_err(be)?;
        let header = self.load_word(p, 0)?;
        let n = self
            .builder
            .build_right_shift(header, self.i64t.const_int(8, false), false, "ms.n")
            .map_err(be)?;
        self.retag_int(n)
    }

    fn compile_raise(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<()> {
        let was = self.eternal_alloc.replace(true);
        let result: CgResult<(IntValue<'ctx>, IntValue<'ctx>)> = (|| {
            let (class, reason) = match name {
                // primop raise(Stk, Reason): re-raise. The "stacktrace" slot
                // carries the class atom (TODO(stacktraces)).
                "raise" if args.len() == 2 => {
                    let class = self.compile_value(f, &args[0], scope)?;
                    let reason = self.compile_value(f, &args[1], scope)?;
                    (class, reason)
                }
                "exit" => {
                    let reason = match args.first() {
                        Some(a) => self.compile_value(f, a, scope)?,
                        None => self.nil(),
                    };
                    (self.atom_term("exit")?, reason)
                }
                "throw" => {
                    let reason = match args.first() {
                        Some(a) => self.compile_value(f, a, scope)?,
                        None => self.nil(),
                    };
                    (self.atom_term("throw")?, reason)
                }
                // match_fail / error / anything else: class error.
                // BEAM reports function_clause as a bare atom (the args go
                // into the stacktrace, which we don't build yet).
                _ => {
                    let reason = match args.first() {
                        Some(Expr::Tuple(items))
                            if name == "match_fail"
                                && matches!(
                                    items.first(),
                                    Some(Expr::Lit(Literal::Atom(a))) if a == "function_clause"
                                ) =>
                        {
                            self.atom_term("function_clause")?
                        }
                        Some(a) => self.compile_value(f, a, scope)?,
                        None => self.nil(),
                    };
                    (self.atom_term("error")?, reason)
                }
            };
            Ok((class, reason))
        })();
        self.eternal_alloc.set(was);
        let (class, reason) = result?;
        self.emit_raise(f, class, reason)
    }

    // ---- helpers ----

    fn local_fn(&self, fname: &FunName) -> CgResult<FunctionValue<'ctx>> {
        self.fns
            .borrow()
            .get(fname)
            .copied()
            .ok_or_else(|| format!("undefined local function {}/{}", fname.name, fname.arity))
    }

    fn remote_fn(&self, module: &str, name: &str, arity: usize) -> FunctionValue<'ctx> {
        let sym = mangle(
            module,
            &FunName {
                name: name.to_string(),
                arity,
            },
        );
        self.module.get_function(&sym).unwrap_or_else(|| {
            self.module
                .add_function(&sym, self.term_fn_type(arity), None)
        })
    }

    fn tag_of(&self, val: IntValue<'ctx>) -> CgResult<IntValue<'ctx>> {
        self.builder
            .build_and(val, self.i64t.const_int(TAG_MASK, false), "tag")
            .map_err(be)
    }

    fn untag_int(&self, val: IntValue<'ctx>) -> CgResult<IntValue<'ctx>> {
        self.builder
            .build_right_shift(val, self.i64t.const_int(3, false), true, "untag")
            .map_err(be)
    }

    fn retag_int(&self, val: IntValue<'ctx>) -> CgResult<IntValue<'ctx>> {
        let shifted = self
            .builder
            .build_left_shift(val, self.i64t.const_int(3, false), "shl")
            .map_err(be)?;
        self.builder
            .build_or(shifted, self.i64t.const_int(TAG_SMALL, false), "retag")
            .map_err(be)
    }

    /// Inline nursery bump allocation: load top/end from ctx words 0/1,
    /// bump on the fast path, call `mana_rt_alloc_slow` (collect) on
    /// overflow. Remains a GC point via the slow path.
    fn alloc_words(&self, n: u64) -> CgResult<PointerValue<'ctx>> {
        self.alloc_words_kind(n, false)
    }

    fn alloc_words_kind(&self, n: u64, is_cons: bool) -> CgResult<PointerValue<'ctx>> {
        if self.eternal_alloc.get() {
            let call = self
                .builder
                .build_call(
                    self.rt_alloc_eternal(),
                    &[
                        self.ctx_val().into(),
                        self.i64t.const_int(n, false).into(),
                        self.i64t.const_int(is_cons as u64, false).into(),
                    ],
                    "alloc.eternal",
                )
                .map_err(be)?;
            return Ok(call_result(call)?.into_pointer_value());
        }
        let f = self
            .builder
            .get_insert_block()
            .unwrap()
            .get_parent()
            .unwrap();
        let ctx = self.ctx_val();
        let fast = self.ctx.append_basic_block(f, "alloc.fast");
        let slow = self.ctx.append_basic_block(f, "alloc.slow");
        let merge = self.ctx.append_basic_block(f, "alloc.done");

        let top = self.mem_load(ctx, 0, MemKind::Ctx)?;
        let new_top = self
            .builder
            .build_int_add(top, self.i64t.const_int(n * 8, false), "alloc.newtop")
            .map_err(be)?;
        let end = self.mem_load(ctx, 1, MemKind::Ctx)?;
        let fits = self
            .builder
            .build_int_compare(IntPredicate::ULE, new_top, end, "alloc.fits")
            .map_err(be)?;
        self.builder
            .build_conditional_branch(fits, fast, slow)
            .map_err(be)?;

        self.builder.position_at_end(fast);
        self.mem_store(ctx, 0, new_top, MemKind::Ctx)?;
        self.builder.build_unconditional_branch(merge).map_err(be)?;

        self.builder.position_at_end(slow);
        let call = self
            .builder
            .build_call(
                self.rt_alloc_slow(),
                &[ctx.into(), self.i64t.const_int(n, false).into()],
                "alloc.rt",
            )
            .map_err(be)?;
        let slow_ptr = call_result(call)?.into_pointer_value();
        let slow_addr = self
            .builder
            .build_ptr_to_int(slow_ptr, self.i64t, "alloc.slowaddr")
            .map_err(be)?;
        let slow_bb = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(merge).map_err(be)?;

        self.builder.position_at_end(merge);
        let phi = self.builder.build_phi(self.i64t, "alloc.addr").map_err(be)?;
        phi.add_incoming(&[(&top, fast), (&slow_addr, slow_bb)]);
        self.builder
            .build_int_to_ptr(phi.as_basic_value().into_int_value(), self.ptrt, "alloc")
            .map_err(be)
    }

    fn tbaa_tag(&self, kind: MemKind) -> inkwell::values::MetadataValue<'ctx> {
        match kind {
            MemKind::Ctx => self.tbaa_ctx,
            MemKind::Frame => self.tbaa_frame,
            MemKind::Heap => self.tbaa_heap,
        }
    }

    fn mem_store(
        &self,
        p: PointerValue<'ctx>,
        index: u64,
        v: IntValue<'ctx>,
        kind: MemKind,
    ) -> CgResult<()> {
        let slot = unsafe {
            self.builder
                .build_in_bounds_gep(
                    self.i64t,
                    p,
                    &[self.i64t.const_int(index, false)],
                    "slot",
                )
                .map_err(be)?
        };
        let inst = self.builder.build_store(slot, v).map_err(be)?;
        let _ = inst.set_metadata(self.tbaa_tag(kind), self.tbaa_kind);
        Ok(())
    }

    fn mem_load(
        &self,
        p: PointerValue<'ctx>,
        index: u64,
        kind: MemKind,
    ) -> CgResult<IntValue<'ctx>> {
        let slot = unsafe {
            self.builder
                .build_in_bounds_gep(
                    self.i64t,
                    p,
                    &[self.i64t.const_int(index, false)],
                    "slot",
                )
                .map_err(be)?
        };
        let v = self.builder.build_load(self.i64t, slot, "word").map_err(be)?;
        if let Some(inst) = v.as_instruction_value() {
            let _ = inst.set_metadata(self.tbaa_tag(kind), self.tbaa_kind);
        }
        Ok(v.into_int_value())
    }

    /// Heap-object word access (the overwhelmingly common case).
    fn store_word(
        &self,
        p: PointerValue<'ctx>,
        index: u64,
        v: IntValue<'ctx>,
    ) -> CgResult<()> {
        self.mem_store(p, index, v, MemKind::Heap)
    }

    fn load_word(&self, p: PointerValue<'ctx>, index: u64) -> CgResult<IntValue<'ctx>> {
        self.mem_load(p, index, MemKind::Heap)
    }

    // ---- output ----

    fn emit_object(&self, out: &Path) -> CgResult<()> {
        Target::initialize_native(&InitializationConfig::default())
            .map_err(|e| format!("target init: {}", e))?;
        let triple = TargetMachine::get_default_triple();
        let target = Target::from_triple(&triple).map_err(|e| e.to_string())?;
        let tm = target
            .create_target_machine(
                &triple,
                &TargetMachine::get_host_cpu_name().to_string(),
                &TargetMachine::get_host_cpu_features().to_string(),
                OptimizationLevel::Aggressive,
                RelocMode::PIC,
                CodeModel::Default,
            )
            .ok_or("failed to create target machine")?;
        self.module.set_triple(&triple);
        self.module
            .set_data_layout(&tm.get_target_data().get_data_layout());
        let opts = inkwell::passes::PassBuilderOptions::create();
        self.module
            .run_passes("default<O2>", &tm, opts)
            .map_err(|e| format!("optimization: {}", e))?;
        tm.write_to_file(&self.module, FileType::Object, out)
            .map_err(|e| format!("emit object: {}", e))
    }
}

/// A child value of an allocation: rooted in a frame slot, or (raise-path /
/// frameless) held in SSA.
enum Rooted<'ctx> {
    Slot(u64),
    Val(IntValue<'ctx>),
}

enum CaseVals<'ctx> {
    Ssa(Vec<IntValue<'ctx>>),
    Slots(Vec<u64>),
}

/// Modules implemented natively (never compiled from beams).
fn is_bif_module(m: &str) -> bool {
    matches!(m, "erlang" | "maps")
}

fn is_raise(primop: &str) -> bool {
    matches!(primop, "match_fail" | "raise" | "error" | "exit" | "throw")
}

// ---- GC-effect analysis ----

/// Fixpoint: which reachable functions may trigger a collection.
fn compute_may_gc(mods: &[Module], reachable: &HashSet<(String, FunName)>) -> GcSet {
    let defs: HashMap<(&str, &FunName), &Fun> = mods
        .iter()
        .flat_map(|m| m.definitions.iter().map(move |(f, b)| ((m.name.as_str(), f), b)))
        .collect();
    let mut set: GcSet = GcSet::new();
    loop {
        let mut changed = false;
        for (m, f) in reachable {
            if set.contains(&(m.clone(), f.clone())) {
                continue;
            }
            let Some(fun) = defs.get(&(m.as_str(), f)) else {
                continue;
            };
            let mut letrec = HashSet::new();
            if expr_may_gc(&fun.body, m, &set, &mut letrec) {
                set.insert((m.clone(), f.clone()));
                changed = true;
            }
        }
        if !changed {
            return set;
        }
    }
}

/// Fixpoint: which reachable functions may raise an exception.
fn compute_may_raise(mods: &[Module], reachable: &HashSet<(String, FunName)>) -> GcSet {
    let defs: HashMap<(&str, &FunName), &Fun> = mods
        .iter()
        .flat_map(|m| m.definitions.iter().map(move |(f, b)| ((m.name.as_str(), f), b)))
        .collect();
    let mut set: GcSet = GcSet::new();
    loop {
        let mut changed = false;
        for (m, f) in reachable {
            if set.contains(&(m.clone(), f.clone())) {
                continue;
            }
            let Some(fun) = defs.get(&(m.as_str(), f)) else {
                continue;
            };
            let mut letrec = HashSet::new();
            if expr_may_raise(&fun.body, m, &set, &mut letrec) {
                set.insert((m.clone(), f.clone()));
                changed = true;
            }
        }
        if !changed {
            return set;
        }
    }
}

fn clause_irrefutable(c: &Clause) -> bool {
    is_true_atom(&c.guard) && c.patterns.iter().all(|p| matches!(p, Pattern::Var(_)))
}

/// Can evaluating `e` raise? Sources: raising primops/BIFs, fun-value
/// applies (badfun), refutable cases (case_clause/function_clause), and
/// calls to may-raise functions. Raises inside a `try` argument are caught.
fn expr_may_raise(
    e: &Expr,
    cur_mod: &str,
    raise_set: &GcSet,
    letrec_bound: &mut HashSet<FunName>,
) -> bool {
    match e {
        Expr::Var(_) | Expr::Lit(_) | Expr::FunRef { .. } | Expr::Fun(_) => false,
        Expr::Tuple(items) | Expr::Values(items) => items
            .iter()
            .any(|i| expr_may_raise(i, cur_mod, raise_set, letrec_bound)),
        Expr::Cons(h, t) => {
            expr_may_raise(h, cur_mod, raise_set, letrec_bound)
                || expr_may_raise(t, cur_mod, raise_set, letrec_bound)
        }
        Expr::Let { arg, body, .. } => {
            expr_may_raise(arg, cur_mod, raise_set, letrec_bound)
                || expr_may_raise(body, cur_mod, raise_set, letrec_bound)
        }
        Expr::Do(a, b) => {
            expr_may_raise(a, cur_mod, raise_set, letrec_bound)
                || expr_may_raise(b, cur_mod, raise_set, letrec_bound)
        }
        Expr::LetRec { defs, body } => {
            let added: Vec<FunName> = defs
                .iter()
                .map(|(f, _)| f.clone())
                .filter(|f| letrec_bound.insert(f.clone()))
                .collect();
            let r = expr_may_raise(body, cur_mod, raise_set, letrec_bound);
            for f in added {
                letrec_bound.remove(&f);
            }
            r
        }
        Expr::Apply { target, args } => {
            let target_raises = match target {
                ApplyTarget::Var(_) => true, // badfun/badarity
                ApplyTarget::LocalFun(f) => {
                    letrec_bound.contains(f)
                        || raise_set.contains(&(cur_mod.to_string(), f.clone()))
                }
            };
            target_raises
                || args
                    .iter()
                    .any(|a| expr_may_raise(a, cur_mod, raise_set, letrec_bound))
        }
        Expr::Call { module, name, args } => {
            if module == "maps" {
                return matches!(
                    name.as_str(),
                    "get" | "put" | "is_key" | "remove" | "merge" | "from_list"
                        | "to_list" | "size"
                ) || args
                    .iter()
                    .any(|a| expr_may_raise(a, cur_mod, raise_set, letrec_bound));
            }
            let callee = if module == "erlang" {
                matches!(
                    (name.as_str(), args.len()),
                    ("error", 1)
                        | ("error", 2)
                        | ("exit", 1)
                        | ("throw", 1)
                        | ("spawn", 1)
                        | ("spawn_link", 1)
                        | ("spawn_monitor", 1)
                        | ("element", 2)
                        | ("setelement", 3)
                        | ("tuple_size", 1)
                        | ("hd", 1)
                        | ("tl", 1)
                        | ("length", 1)
                        | ("++", 2)
                        | ("--", 2)
                        | ("abs", 1)
                        | ("map_size", 1)
                        | ("map_get", 2)
                        | ("is_map_key", 2)
                )
            } else {
                raise_set.contains(&(
                    module.clone(),
                    FunName {
                        name: name.clone(),
                        arity: args.len(),
                    },
                ))
            };
            callee
                || args
                    .iter()
                    .any(|a| expr_may_raise(a, cur_mod, raise_set, letrec_bound))
        }
        Expr::PrimOp { name, .. } if is_raise(name) => true,
        Expr::PrimOp { args, .. } => args
            .iter()
            .any(|a| expr_may_raise(a, cur_mod, raise_set, letrec_bound)),
        Expr::Case { arg, clauses } => {
            let refutable = clauses.last().map_or(true, |c| !clause_irrefutable(c));
            refutable
                || expr_may_raise(arg, cur_mod, raise_set, letrec_bound)
                || clauses.iter().any(|c| {
                    expr_may_raise(&c.guard, cur_mod, raise_set, letrec_bound)
                        || expr_may_raise(&c.body, cur_mod, raise_set, letrec_bound)
                })
        }
        // raises inside the protected argument are caught by this try
        Expr::Try { body, handler, .. } => {
            expr_may_raise(body, cur_mod, raise_set, letrec_bound)
                || expr_may_raise(handler, cur_mod, raise_set, letrec_bound)
        }
        Expr::Binary(_) => false, // rejected at codegen
        // updates raise badmap/badkey; construction only via children
        Expr::Map { pairs, update } => {
            update.is_some()
                || pairs.iter().any(|(k, _, v)| {
                    expr_may_raise(k, cur_mod, raise_set, letrec_bound)
                        || expr_may_raise(v, cur_mod, raise_set, letrec_bound)
                })
        }
    }
}

/// Does evaluating `e` contain a GC point? Allocation sites are GC points;
/// calls consult the (possibly still-growing) fixpoint set; letrec-bound
/// applies and fun-value applies are conservatively GC points.
fn expr_may_gc(
    e: &Expr,
    cur_mod: &str,
    gc_set: &GcSet,
    letrec_bound: &mut HashSet<FunName>,
) -> bool {
    match e {
        Expr::Var(_) => false,
        Expr::Lit(Literal::Float(_)) => true, // boxed
        Expr::Lit(_) => false,
        // allocation sites
        Expr::Tuple(_) | Expr::Cons(..) | Expr::Fun(_) | Expr::FunRef { .. }
        | Expr::LetRec { .. } | Expr::Binary(_) | Expr::Map { .. } => true,
        Expr::Apply { target, args } => {
            let target_gc = match target {
                ApplyTarget::Var(_) => true,
                ApplyTarget::LocalFun(f) => {
                    letrec_bound.contains(f)
                        || gc_set.contains(&(cur_mod.to_string(), f.clone()))
                }
            };
            target_gc
                || args
                    .iter()
                    .any(|a| expr_may_gc(a, cur_mod, gc_set, letrec_bound))
        }
        Expr::Call { module, name, args } => {
            if module == "erlang"
                && matches!(
                    (name.as_str(), args.len()),
                    ("error", 1) | ("error", 2) | ("exit", 1) | ("throw", 1)
                )
            {
                return args
                    .iter()
                    .any(|a| raise_arg_may_gc(a, cur_mod, gc_set, letrec_bound));
            }
            // allocating erlang BIFs are GC points
            if module == "erlang"
                && matches!(
                    (name.as_str(), args.len()),
                    ("setelement", 3) | ("++", 2) | ("--", 2)
                )
            {
                return true;
            }
            if module == "maps"
                && matches!(
                    name.as_str(),
                    "put" | "remove" | "merge" | "from_list" | "to_list" | "find"
                )
            {
                return true;
            }
            let callee_gc = module != "erlang"
                && gc_set.contains(&(
                    module.clone(),
                    FunName {
                        name: name.clone(),
                        arity: args.len(),
                    },
                ));
            callee_gc
                || args
                    .iter()
                    .any(|a| expr_may_gc(a, cur_mod, gc_set, letrec_bound))
        }
        Expr::PrimOp { name, args } if is_raise(name) => args
            .iter()
            .any(|a| raise_arg_may_gc(a, cur_mod, gc_set, letrec_bound)),
        // recv_wait_timeout suspends the process — other processes run and
        // may collect the shared heap, so it is a GC point
        Expr::PrimOp { name, .. } if name == "recv_wait_timeout" => true,
        Expr::PrimOp { args, .. } => args
            .iter()
            .any(|a| expr_may_gc(a, cur_mod, gc_set, letrec_bound)),
        Expr::Let { arg, body, .. } => {
            expr_may_gc(arg, cur_mod, gc_set, letrec_bound)
                || expr_may_gc(body, cur_mod, gc_set, letrec_bound)
        }
        Expr::Do(a, b) => {
            expr_may_gc(a, cur_mod, gc_set, letrec_bound)
                || expr_may_gc(b, cur_mod, gc_set, letrec_bound)
        }
        Expr::Try {
            arg, body, handler, ..
        } => {
            expr_may_gc(arg, cur_mod, gc_set, letrec_bound)
                || expr_may_gc(body, cur_mod, gc_set, letrec_bound)
                || expr_may_gc(handler, cur_mod, gc_set, letrec_bound)
        }
        Expr::Case { arg, clauses } => {
            expr_may_gc(arg, cur_mod, gc_set, letrec_bound)
                || clauses.iter().any(|c| {
                    expr_may_gc(&c.guard, cur_mod, gc_set, letrec_bound)
                        || expr_may_gc(&c.body, cur_mod, gc_set, letrec_bound)
                })
        }
        Expr::Values(items) => items
            .iter()
            .any(|i| expr_may_gc(i, cur_mod, gc_set, letrec_bound)),
    }
}

/// GC-point analysis for raise arguments: the reason term is built with the
/// eternal allocator (no GC), so allocation nodes don't count — only calls
/// into compiled code do.
fn raise_arg_may_gc(
    e: &Expr,
    cur_mod: &str,
    gc_set: &GcSet,
    letrec_bound: &mut HashSet<FunName>,
) -> bool {
    match e {
        Expr::Var(_) | Expr::Lit(_) | Expr::FunRef { .. } | Expr::Fun(_) => false,
        Expr::Tuple(items) | Expr::Values(items) => items
            .iter()
            .any(|i| raise_arg_may_gc(i, cur_mod, gc_set, letrec_bound)),
        Expr::Cons(h, t) => {
            raise_arg_may_gc(h, cur_mod, gc_set, letrec_bound)
                || raise_arg_may_gc(t, cur_mod, gc_set, letrec_bound)
        }
        // anything with control flow or calls: fall back to the full analysis
        other => expr_may_gc(other, cur_mod, gc_set, letrec_bound),
    }
}

/// Count bound variable names and *spill sites* for frame sizing. Spills
/// only happen for children of allocations (eval_all_rooted), call/BIF
/// arguments (eval_siblings), case scrutinees, and letrec closures — the
/// sum over those sites bounds any execution path. Does not descend into
/// Fun/LetRec definition bodies (they get their own frames when lifted).
fn frame_prepass(e: &Expr, vars: &mut BTreeSet<String>, nodes: &mut usize) {
    match e {
        Expr::Var(_) | Expr::Lit(_) | Expr::FunRef { .. } | Expr::Fun(_) => {}
        Expr::Tuple(items) | Expr::Values(items) => {
            *nodes += items.len();
            items.iter().for_each(|i| frame_prepass(i, vars, nodes))
        }
        Expr::Cons(h, t) => {
            *nodes += 2;
            frame_prepass(h, vars, nodes);
            frame_prepass(t, vars, nodes);
        }
        Expr::Let { vars: vs, arg, body } => {
            vars.extend(vs.iter().cloned());
            frame_prepass(arg, vars, nodes);
            frame_prepass(body, vars, nodes);
        }
        Expr::LetRec { body, .. } => {
            *nodes += 1; // shared closure slot
            frame_prepass(body, vars, nodes);
        }
        Expr::Apply { args, .. } => {
            *nodes += args.len();
            args.iter().for_each(|a| frame_prepass(a, vars, nodes))
        }
        Expr::Call { args, .. } | Expr::PrimOp { args, .. } => {
            *nodes += args.len();
            args.iter().for_each(|a| frame_prepass(a, vars, nodes))
        }
        Expr::Case { arg, clauses } => {
            *nodes += match arg.as_ref() {
                Expr::Values(es) => es.len(),
                _ => 1,
            };
            frame_prepass(arg, vars, nodes);
            for c in clauses {
                let mut pvars = Vec::new();
                c.patterns.iter().for_each(|p| pattern_vars(p, &mut pvars));
                vars.extend(pvars);
                frame_prepass(&c.guard, vars, nodes);
                frame_prepass(&c.body, vars, nodes);
            }
        }
        Expr::Try {
            arg,
            vars: vs,
            body,
            evars,
            handler,
        } => {
            vars.extend(vs.iter().cloned());
            vars.extend(evars.iter().cloned());
            frame_prepass(arg, vars, nodes);
            frame_prepass(body, vars, nodes);
            frame_prepass(handler, vars, nodes);
        }
        Expr::Binary(segs) => {
            for s in segs {
                frame_prepass(&s.value, vars, nodes);
                s.spec.iter().for_each(|x| frame_prepass(x, vars, nodes));
            }
        }
        Expr::Map { pairs, update } => {
            for (k, _, v) in pairs {
                frame_prepass(k, vars, nodes);
                frame_prepass(v, vars, nodes);
            }
            if let Some(u) = update {
                frame_prepass(u, vars, nodes);
            }
        }
        Expr::Do(a, b) => {
            frame_prepass(a, vars, nodes);
            frame_prepass(b, vars, nodes);
        }
    }
}

// ---- free variable analysis ----

fn free_vars(e: &Expr, bound: &mut HashSet<String>, out: &mut BTreeSet<String>) {
    match e {
        Expr::Var(v) => {
            if !bound.contains(v) {
                out.insert(v.clone());
            }
        }
        Expr::Lit(_) | Expr::FunRef { .. } => {}
        Expr::Tuple(items) | Expr::Values(items) => {
            items.iter().for_each(|i| free_vars(i, bound, out))
        }
        Expr::Cons(h, t) => {
            free_vars(h, bound, out);
            free_vars(t, bound, out);
        }
        Expr::Fun(f) => {
            let added: Vec<&String> = f
                .params
                .iter()
                .filter(|p| bound.insert((*p).clone()))
                .collect();
            free_vars(&f.body, bound, out);
            for p in added {
                bound.remove(p);
            }
        }
        Expr::Let { vars, arg, body } => {
            free_vars(arg, bound, out);
            let added: Vec<&String> =
                vars.iter().filter(|v| bound.insert((*v).clone())).collect();
            free_vars(body, bound, out);
            for v in added {
                bound.remove(v);
            }
        }
        Expr::LetRec { defs, body } => {
            for (_, f) in defs {
                let added: Vec<&String> = f
                    .params
                    .iter()
                    .filter(|p| bound.insert((*p).clone()))
                    .collect();
                free_vars(&f.body, bound, out);
                for p in added {
                    bound.remove(p);
                }
            }
            free_vars(body, bound, out);
        }
        Expr::Apply { target, args } => {
            if let ApplyTarget::Var(v) = target {
                if !bound.contains(v) {
                    out.insert(v.clone());
                }
            }
            args.iter().for_each(|a| free_vars(a, bound, out));
        }
        Expr::Call { args, .. } | Expr::PrimOp { args, .. } => {
            args.iter().for_each(|a| free_vars(a, bound, out))
        }
        Expr::Case { arg, clauses } => {
            free_vars(arg, bound, out);
            for c in clauses {
                let mut pvars = Vec::new();
                c.patterns.iter().for_each(|p| pattern_vars(p, &mut pvars));
                let added: Vec<String> = pvars
                    .into_iter()
                    .filter(|v| bound.insert(v.clone()))
                    .collect();
                free_vars(&c.guard, bound, out);
                free_vars(&c.body, bound, out);
                for v in added {
                    bound.remove(&v);
                }
            }
        }
        Expr::Binary(segs) => {
            for s in segs {
                free_vars(&s.value, bound, out);
                s.spec.iter().for_each(|x| free_vars(x, bound, out));
            }
        }
        Expr::Map { pairs, update } => {
            for (k, _, v) in pairs {
                free_vars(k, bound, out);
                free_vars(v, bound, out);
            }
            if let Some(u) = update {
                free_vars(u, bound, out);
            }
        }
        Expr::Try {
            arg,
            vars,
            body,
            evars,
            handler,
        } => {
            free_vars(arg, bound, out);
            let added: Vec<&String> =
                vars.iter().filter(|v| bound.insert((*v).clone())).collect();
            free_vars(body, bound, out);
            for v in added {
                bound.remove(v);
            }
            let added: Vec<&String> = evars
                .iter()
                .filter(|v| bound.insert((*v).clone()))
                .collect();
            free_vars(handler, bound, out);
            for v in added {
                bound.remove(v);
            }
        }
        Expr::Do(a, b) => {
            free_vars(a, bound, out);
            free_vars(b, bound, out);
        }
    }
}

fn pattern_vars(p: &Pattern, out: &mut Vec<String>) {
    match p {
        Pattern::Var(v) => out.push(v.clone()),
        Pattern::Lit(_) => {}
        Pattern::Alias(v, inner) => {
            out.push(v.clone());
            pattern_vars(inner, out);
        }
        Pattern::Tuple(ps) => ps.iter().for_each(|p| pattern_vars(p, out)),
        Pattern::Cons(h, t) => {
            pattern_vars(h, out);
            pattern_vars(t, out);
        }
        Pattern::Binary(segs) => segs.iter().for_each(|s| pattern_vars(&s.value, out)),
        Pattern::Map(pairs) => pairs.iter().for_each(|(_, p)| pattern_vars(p, out)),
    }
}

// ---- reachability ----

enum Edge {
    Local(FunName),
    Remote(String, FunName),
}

fn reachable_funs(
    mods: &[Module],
    entry_mod: &str,
    entry: &FunName,
    poisoned: &HashMap<String, String>,
) -> CgResult<HashSet<(String, FunName)>> {
    let defs: HashMap<(&str, &FunName), &Fun> = mods
        .iter()
        .flat_map(|m| m.definitions.iter().map(move |(f, b)| ((m.name.as_str(), f), b)))
        .collect();
    let have_module: HashSet<&str> = mods.iter().map(|m| m.name.as_str()).collect();

    if !defs.contains_key(&(entry_mod, entry)) {
        if !have_module.contains(entry_mod) {
            return Err(format!(
                "entry module '{}' is not among the compiled modules ({})",
                entry_mod,
                have_module.iter().copied().collect::<Vec<_>>().join(", ")
            ));
        }
        let known: Vec<String> = mods
            .iter()
            .find(|m| m.name == entry_mod)
            .map(|m| {
                m.definitions
                    .iter()
                    .map(|(f, _)| format!("{}/{}", f.name, f.arity))
                    .collect()
            })
            .unwrap_or_default();
        return Err(format!(
            "entry function {}/{} is not defined in module '{}' (defined: {})",
            entry.name,
            entry.arity,
            entry_mod,
            known.join(", ")
        ));
    }

    let mut seen: HashSet<(String, FunName)> = HashSet::new();
    let mut work = vec![(entry_mod.to_string(), entry.clone())];
    while let Some((module, fname)) = work.pop() {
        if !seen.insert((module.clone(), fname.clone())) {
            continue;
        }
        let fun = defs[&(module.as_str(), &fname)];
        let mut edges = Vec::new();
        let mut letrec_bound = HashSet::new();
        collect_edges(&fun.body, &mut edges, &mut letrec_bound);
        for edge in edges {
            let (tmod, tfun) = match edge {
                Edge::Local(f) => (module.clone(), f),
                Edge::Remote(m, _) if is_bif_module(&m) => continue, // BIF
                Edge::Remote(m, f) => (m, f),
            };
            if defs.contains_key(&(tmod.as_str(), &tfun)) {
                work.push((tmod, tfun));
            } else if have_module.contains(tmod.as_str()) {
                return Err(format!(
                    "function {}:{}/{} (required by {}:{}/{}) is not defined",
                    tmod, tfun.name, tfun.arity, module, fname.name, fname.arity
                ));
            } else if let Some(parse_err) = poisoned.get(&tmod) {
                return Err(format!(
                    "module '{}' (required by {}:{}/{}) failed to parse: {}",
                    tmod, module, fname.name, fname.arity, parse_err
                ));
            } else {
                return Err(format!(
                    "module '{}' (required by {}:{}/{}) is not among the compiled \
                     modules — the Erlang/Elixir standard library is not yet supported",
                    tmod, module, fname.name, fname.arity
                ));
            }
        }
    }
    Ok(seen)
}

fn collect_edges(e: &Expr, out: &mut Vec<Edge>, letrec_bound: &mut HashSet<FunName>) {
    match e {
        Expr::Var(_) | Expr::Lit(_) => {}
        Expr::FunRef { module, fun } => match module {
            Some(m) => out.push(Edge::Remote(m.clone(), fun.clone())),
            None => {
                if !letrec_bound.contains(fun) {
                    out.push(Edge::Local(fun.clone()));
                }
            }
        },
        Expr::Tuple(items) | Expr::Values(items) => items
            .iter()
            .for_each(|i| collect_edges(i, out, letrec_bound)),
        Expr::Cons(h, t) => {
            collect_edges(h, out, letrec_bound);
            collect_edges(t, out, letrec_bound);
        }
        Expr::Fun(f) => collect_edges(&f.body, out, letrec_bound),
        Expr::Let { arg, body, .. } => {
            collect_edges(arg, out, letrec_bound);
            collect_edges(body, out, letrec_bound);
        }
        Expr::LetRec { defs, body } => {
            let added: Vec<FunName> = defs
                .iter()
                .map(|(f, _)| f.clone())
                .filter(|f| letrec_bound.insert(f.clone()))
                .collect();
            defs.iter()
                .for_each(|(_, f)| collect_edges(&f.body, out, letrec_bound));
            collect_edges(body, out, letrec_bound);
            for f in added {
                letrec_bound.remove(&f);
            }
        }
        Expr::Apply { target, args } => {
            if let ApplyTarget::LocalFun(f) = target {
                if !letrec_bound.contains(f) {
                    out.push(Edge::Local(f.clone()));
                }
            }
            args.iter()
                .for_each(|a| collect_edges(a, out, letrec_bound));
        }
        Expr::Call { module, name, args } => {
            out.push(Edge::Remote(
                module.clone(),
                FunName {
                    name: name.clone(),
                    arity: args.len(),
                },
            ));
            args.iter()
                .for_each(|a| collect_edges(a, out, letrec_bound));
        }
        Expr::PrimOp { args, .. } => args
            .iter()
            .for_each(|a| collect_edges(a, out, letrec_bound)),
        Expr::Case { arg, clauses } => {
            collect_edges(arg, out, letrec_bound);
            for c in clauses {
                collect_edges(&c.guard, out, letrec_bound);
                collect_edges(&c.body, out, letrec_bound);
            }
        }
        Expr::Binary(segs) => {
            for s in segs {
                collect_edges(&s.value, out, letrec_bound);
                s.spec
                    .iter()
                    .for_each(|x| collect_edges(x, out, letrec_bound));
            }
        }
        Expr::Map { pairs, update } => {
            for (k, _, v) in pairs {
                collect_edges(k, out, letrec_bound);
                collect_edges(v, out, letrec_bound);
            }
            if let Some(u) = update {
                collect_edges(u, out, letrec_bound);
            }
        }
        Expr::Try {
            arg, body, handler, ..
        } => {
            collect_edges(arg, out, letrec_bound);
            collect_edges(body, out, letrec_bound);
            collect_edges(handler, out, letrec_bound);
        }
        Expr::Do(a, b) => {
            collect_edges(a, out, letrec_bound);
            collect_edges(b, out, letrec_bound);
        }
    }
}

fn is_true_atom(e: &Expr) -> bool {
    matches!(e, Expr::Lit(Literal::Atom(a)) if a == "true")
}

fn mangle(module: &str, f: &FunName) -> String {
    format!("mn_{}_{}_{}", sanitize(module), sanitize(&f.name), f.arity)
}

fn sanitize(s: &str) -> String {
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

fn be(e: inkwell::builder::BuilderError) -> String {
    format!("LLVM builder: {}", e)
}

fn call_result(call: CallSiteValue<'_>) -> CgResult<inkwell::values::BasicValueEnum<'_>> {
    match call.try_as_basic_value() {
        ValueKind::Basic(v) => Ok(v),
        ValueKind::Instruction(_) => Err("call to void function used as a value".into()),
    }
}
