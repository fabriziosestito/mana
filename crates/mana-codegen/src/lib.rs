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
    BasicMetadataValueEnum, CallSiteValue, FunctionValue, GlobalValue, IntValue, PointerValue,
    ValueKind,
};
use inkwell::AddressSpace;
use inkwell::IntPredicate;
use inkwell::OptimizationLevel;

use mana_syntax::{ApplyTarget, Clause, Expr, Fun, FunName, Literal, Module, Pattern};

const TAG_SMALL: u64 = 0b001;
const TAG_ATOM: u64 = 0b010;
const NIL: u64 = 0b011;
const TAG_CONS: u64 = 0b100;
const TAG_MASK: u64 = 0b111;
const KIND_TUPLE: u64 = 0;
const KIND_FLOAT: u64 = 1;
const KIND_FUN: u64 = 2;

/// ctx word offset of `roots_head` (ProcCtx contract).
const CTX_ROOTS: u64 = 2;

type CgResult<T> = Result<T, String>;
type GcSet = HashSet<(String, FunName)>;

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
        let cg = Cg::new(&context, &m.name, &gc_set);
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
    // per-function state
    cur_ctx: Cell<Option<PointerValue<'ctx>>>,
    cur_frame: Cell<Option<PointerValue<'ctx>>>,
    var_slots: RefCell<HashMap<String, u64>>,
    next_slot: Cell<u64>,
    slot_cap: Cell<u64>,
}

impl<'ctx, 'p> Cg<'ctx, 'p> {
    fn new(ctx: &'ctx Context, module_name: &str, gc_set: &'p GcSet) -> Self {
        let module = ctx.create_module(module_name);
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
            cur_ctx: Cell::new(None),
            cur_frame: Cell::new(None),
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

    fn rt_match_fail(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_match_fail", || {
            self.ctx
                .void_type()
                .fn_type(&[BasicMetadataTypeEnum::IntType(self.i64t)], false)
        })
    }

    fn rt_badfun(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_badfun", || {
            self.ctx
                .void_type()
                .fn_type(&[BasicMetadataTypeEnum::IntType(self.i64t)], false)
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
        let prev = self.load_word(ctx, CTX_ROOTS)?;
        self.store_word(frame, 0, prev)?;
        self.store_word(frame, 1, self.i64t.const_int(cap, false))?;
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
        self.store_word(ctx, CTX_ROOTS, frame_int)?;
        self.cur_frame.set(Some(frame));
        Ok(())
    }

    /// Unlink the frame (before any return or tail call).
    fn pop_frame(&self) -> CgResult<()> {
        if let Some(frame) = self.cur_frame.get() {
            let prev = self.load_word(frame, 0)?;
            self.store_word(self.ctx_val(), CTX_ROOTS, prev)?;
        }
        Ok(())
    }

    fn emit_ret(&self, v: IntValue<'ctx>) -> CgResult<()> {
        self.pop_frame()?;
        self.builder.build_return(Some(&v)).map_err(be)?;
        Ok(())
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
        self.builder.build_store(p, v).map_err(be)?;
        Ok(idx)
    }

    fn reload(&self, idx: u64) -> CgResult<IntValue<'ctx>> {
        let p = self.slot_ptr(idx)?;
        Ok(self
            .builder
            .build_load(self.i64t, p, "reload")
            .map_err(be)?
            .into_int_value())
    }

    fn bind_var(&self, scope: &mut Scope<'ctx>, name: &str, v: IntValue<'ctx>) -> CgResult<()> {
        if self.framed() {
            let idx = *self
                .var_slots
                .borrow()
                .get(name)
                .unwrap_or_else(|| panic!("no slot preassigned for variable {}", name));
            let p = self.slot_ptr(idx)?;
            self.builder.build_store(p, v).map_err(be)?;
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
        self.setup_frame(&fun.body, &fun.params, &[])?;
        let mut scope = Scope::default();
        for (i, p) in fun.params.iter().enumerate() {
            let v = f.get_nth_param(1 + i as u32).unwrap().into_int_value();
            v.set_name(p);
            self.bind_var(&mut scope, p, v)?;
        }
        self.compile_tail(f, &fun.body, &mut scope)
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
        let target = self.fns.borrow()[entry];
        self.builder
            .build_call(target, &[ctx.into()], "ret")
            .map_err(be)?;
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
                arg, vars, body, ..
            } => {
                // TODO(exceptions): degenerates to a let-binding for now.
                if vars.len() != 1 {
                    return Err("multi-value try is not supported".into());
                }
                let v = self.compile_value(f, arg, scope)?;
                self.bind_var(scope, &vars[0], v)?;
                self.compile_tail(f, body, scope)
            }
            Expr::Apply { target, args } => {
                let call = self.compile_apply(f, target, args, scope, true)?;
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
                self.compile_raise(f, name, args, scope)
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
                    let v = self.reload(*s)?;
                    self.store_word(p, 1 + i as u64, v)?;
                }
                self.builder
                    .build_ptr_to_int(p, self.i64t, "tuple")
                    .map_err(be)
            }
            Expr::Cons(h, t) => {
                let slots = self.eval_all_rooted(f, &[h.as_ref(), t.as_ref()], scope)?;
                let p = self.alloc_words(2)?;
                for (i, s) in slots.iter().enumerate() {
                    let v = self.reload(*s)?;
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
                arg, vars, body, ..
            } => {
                // TODO(exceptions): degenerates to a let-binding for now.
                if vars.len() != 1 {
                    return Err("multi-value try is not supported".into());
                }
                let v = self.compile_value(f, arg, scope)?;
                self.bind_var(scope, &vars[0], v)?;
                self.compile_value(f, body, scope)
            }
            Expr::Apply { target, args } => {
                let call = self.compile_apply(f, target, args, scope, false)?;
                Ok(call_result(call)?.into_int_value())
            }
            Expr::Call { module, name, args } => {
                if module == "erlang" {
                    self.compile_bif(f, name, args, scope)
                } else {
                    let callee = self.remote_fn(module, name, args.len());
                    let argv = self.eval_args(f, args, scope)?;
                    let call = self.builder.build_call(callee, &argv, "call").map_err(be)?;
                    Ok(call_result(call)?.into_int_value())
                }
            }
            Expr::PrimOp { name, args } if is_raise(name) => {
                self.compile_raise(f, name, args, scope)?;
                let dead = self.ctx.append_basic_block(f, "dead");
                self.builder.position_at_end(dead);
                Ok(self.i64t.get_undef())
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
            Expr::Map { .. } => Err("maps are not supported yet".into()),
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
            let v = self.compile_value(f, e, scope)?;
            if gc_after[i] && self.framed() {
                held.push(Held::Slot(self.spill(v)?));
            } else {
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
    /// an allocation). Only valid in framed functions.
    fn eval_all_rooted(
        &self,
        f: FunctionValue<'ctx>,
        exprs: &[&Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<Vec<u64>> {
        exprs
            .iter()
            .map(|e| {
                let v = self.compile_value(f, e, scope)?;
                self.spill(v)
            })
            .collect()
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
    fn compile_apply(
        &self,
        f: FunctionValue<'ctx>,
        target: &ApplyTarget,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
        tail: bool,
    ) -> CgResult<CallSiteValue<'ctx>> {
        match target {
            ApplyTarget::LocalFun(fname) => {
                if let Some((lf, cl_slot)) = scope.funs.get(fname).copied() {
                    let mut argv = self.eval_args(f, args, scope)?;
                    let closure = self.reload(cl_slot)?;
                    argv.push(closure.into());
                    if tail {
                        self.pop_frame()?;
                    }
                    self.builder.build_call(lf, &argv, "call").map_err(be)
                } else {
                    let callee = self.local_fn(fname)?;
                    let argv = self.eval_args(f, args, scope)?;
                    if tail {
                        self.pop_frame()?;
                    }
                    self.builder.build_call(callee, &argv, "call").map_err(be)
                }
            }
            ApplyTarget::Var(v) => {
                let argv = self.eval_args(f, args, scope)?;
                let fun_val = self.read_var(scope, v)?;
                self.compile_apply_value(f, fun_val, &argv, args.len(), tail)
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
        self.builder
            .build_call(self.rt_badfun(), &[fun_val.into()], "")
            .map_err(be)?;
        self.builder.build_unreachable().map_err(be)?;

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
            let slots = self.eval_all_rooted(f, &exprs, scope)?;
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
        self.builder
            .build_call(self.rt_match_fail(), &[self.nil().into()], "")
            .map_err(be)?;
        self.builder.build_unreachable().map_err(be)?;
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
            Pattern::Map(_) => Err("map patterns are not supported yet".into()),
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
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
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
                // Correct for small ints (tagging is monotone) and exact
                // (in)equality of immediates. TODO: full term ordering.
                let pred = match name {
                    "<" => IntPredicate::SLT,
                    "=<" => IntPredicate::SLE,
                    ">" => IntPredicate::SGT,
                    ">=" => IntPredicate::SGE,
                    "==" | "=:=" => IntPredicate::EQ,
                    _ => IntPredicate::NE,
                };
                let c = self
                    .builder
                    .build_int_compare(pred, argv[0], argv[1], "cmp")
                    .map_err(be)?;
                let t = self.atom_term("true")?;
                let fa = self.atom_term("false")?;
                Ok(self
                    .builder
                    .build_select(c, t, fa, "bool")
                    .map_err(be)?
                    .into_int_value())
            }
            ("display", 1) => {
                self.builder
                    .build_call(self.rt_display(), &[argv[0].into()], "")
                    .map_err(be)?;
                self.atom_term("true")
            }
            // raising BIFs terminate via the runtime (TODO(exceptions))
            ("error", 1) | ("error", 2) | ("exit", 1) | ("throw", 1) => {
                self.builder
                    .build_call(self.rt_match_fail(), &[argv[0].into()], "")
                    .map_err(be)?;
                self.builder.build_unreachable().map_err(be)?;
                let dead = self.ctx.append_basic_block(f, "dead");
                self.builder.position_at_end(dead);
                Ok(self.i64t.get_undef())
            }
            _ => Err(format!("unsupported BIF erlang:{}/{}", name, argv.len())),
        }
    }

    fn compile_raise(
        &self,
        f: FunctionValue<'ctx>,
        _name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<()> {
        let reason = match args.first() {
            Some(a) => self.compile_value(f, a, scope)?,
            None => self.nil(),
        };
        self.builder
            .build_call(self.rt_match_fail(), &[reason.into()], "")
            .map_err(be)?;
        self.builder.build_unreachable().map_err(be)?;
        Ok(())
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

        let top = self.load_word(ctx, 0)?;
        let new_top = self
            .builder
            .build_int_add(top, self.i64t.const_int(n * 8, false), "alloc.newtop")
            .map_err(be)?;
        let end = self.load_word(ctx, 1)?;
        let fits = self
            .builder
            .build_int_compare(IntPredicate::ULE, new_top, end, "alloc.fits")
            .map_err(be)?;
        self.builder
            .build_conditional_branch(fits, fast, slow)
            .map_err(be)?;

        self.builder.position_at_end(fast);
        self.store_word(ctx, 0, new_top)?;
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

    fn store_word(
        &self,
        p: PointerValue<'ctx>,
        index: u64,
        v: IntValue<'ctx>,
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
        self.builder.build_store(slot, v).map_err(be)?;
        Ok(())
    }

    fn load_word(&self, p: PointerValue<'ctx>, index: u64) -> CgResult<IntValue<'ctx>> {
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
        Ok(self
            .builder
            .build_load(self.i64t, slot, "word")
            .map_err(be)?
            .into_int_value())
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

enum CaseVals<'ctx> {
    Ssa(Vec<IntValue<'ctx>>),
    Slots(Vec<u64>),
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

/// Count bound variable names and expression nodes for frame sizing. Does
/// not descend into Fun/LetRec definition bodies (they get their own
/// frames when lifted).
fn frame_prepass(e: &Expr, vars: &mut BTreeSet<String>, nodes: &mut usize) {
    *nodes += 1;
    match e {
        Expr::Var(_) | Expr::Lit(_) | Expr::FunRef { .. } | Expr::Fun(_) => {}
        Expr::Tuple(items) | Expr::Values(items) => {
            items.iter().for_each(|i| frame_prepass(i, vars, nodes))
        }
        Expr::Cons(h, t) => {
            frame_prepass(h, vars, nodes);
            frame_prepass(t, vars, nodes);
        }
        Expr::Let { vars: vs, arg, body } => {
            vars.extend(vs.iter().cloned());
            frame_prepass(arg, vars, nodes);
            frame_prepass(body, vars, nodes);
        }
        Expr::LetRec { body, .. } => frame_prepass(body, vars, nodes),
        Expr::Apply { args, .. } => args.iter().for_each(|a| frame_prepass(a, vars, nodes)),
        Expr::Call { args, .. } | Expr::PrimOp { args, .. } => {
            args.iter().for_each(|a| frame_prepass(a, vars, nodes))
        }
        Expr::Case { arg, clauses } => {
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
            for (k, v) in pairs {
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
            for (k, v) in pairs {
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
                Edge::Remote(m, _) if m == "erlang" => continue, // BIF
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
            for (k, v) in pairs {
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
