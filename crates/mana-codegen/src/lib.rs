//! LLVM codegen for the sequential Core Erlang subset.
//!
//! Term representation matches mana-rt (see its crate docs): i64 words,
//! 3-bit tags — 001 small int, 010 atom ptr, 011 nil, 100 cons ptr,
//! 000 boxed ptr.
//!
//! Functions use the C calling convention with `tail` markers on calls in
//! tail position. TODO(lco): switch to tailcc + musttail with a uniform
//! signature so cross-function tail calls are guaranteed.

use std::collections::{HashMap, HashSet};
use std::path::Path;

use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module as LlvmModule;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine,
};
use inkwell::types::{BasicMetadataTypeEnum, IntType, PointerType};
use inkwell::values::{CallSiteValue, FunctionValue, GlobalValue, IntValue, ValueKind};
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

type CgResult<T> = Result<T, String>;
type Env<'ctx> = HashMap<String, IntValue<'ctx>>;

/// Compile `ast` to an object file. Only functions reachable from `entry`
/// are compiled (closed world) — this is what lets us ignore generated
/// functions like `__info__/1` and `module_info/0,1` that use unsupported
/// constructs. A C `main` calling `entry` (arity 0) is emitted.
pub fn compile_module(
    ast: &Module,
    out_obj: &Path,
    dump_ir: bool,
    entry: &FunName,
) -> CgResult<()> {
    let context = Context::create();
    let cg = Cg::new(&context, &ast.name);
    cg.compile(ast, entry)?;
    if dump_ir {
        eprintln!("{}", cg.module.print_to_string().to_string());
    }
    cg.module
        .verify()
        .map_err(|e| format!("LLVM verifier: {}", e))?;
    cg.emit_object(out_obj)
}

struct Cg<'ctx> {
    ctx: &'ctx Context,
    module: LlvmModule<'ctx>,
    builder: Builder<'ctx>,
    i64t: IntType<'ctx>,
    ptrt: PointerType<'ctx>,
    fns: std::cell::RefCell<HashMap<FunName, FunctionValue<'ctx>>>,
    atoms: std::cell::RefCell<HashMap<String, GlobalValue<'ctx>>>,
    module_name: String,
}

impl<'ctx> Cg<'ctx> {
    fn new(ctx: &'ctx Context, module_name: &str) -> Self {
        let module = ctx.create_module(module_name);
        Cg {
            ctx,
            module,
            builder: ctx.create_builder(),
            i64t: ctx.i64_type(),
            ptrt: ctx.ptr_type(AddressSpace::default()),
            fns: Default::default(),
            atoms: Default::default(),
            module_name: module_name.to_string(),
        }
    }

    // ---- runtime externs ----

    fn rt_fn(&self, name: &str, mk: impl FnOnce() -> inkwell::types::FunctionType<'ctx>) -> FunctionValue<'ctx> {
        self.module
            .get_function(name)
            .unwrap_or_else(|| self.module.add_function(name, mk(), None))
    }

    fn rt_display(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_display", || {
            self.ctx
                .void_type()
                .fn_type(&[BasicMetadataTypeEnum::IntType(self.i64t)], false)
        })
    }

    fn rt_alloc(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_alloc", || {
            self.ptrt
                .fn_type(&[BasicMetadataTypeEnum::IntType(self.i64t)], false)
        })
    }

    fn rt_match_fail(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_match_fail", || {
            self.ctx
                .void_type()
                .fn_type(&[BasicMetadataTypeEnum::IntType(self.i64t)], false)
        })
    }

    // ---- constants ----

    fn small_int(&self, n: i64) -> IntValue<'ctx> {
        // TODO(bignum): values outside the small range wrap silently.
        self.i64t
            .const_int(((n as u64) << 3) | TAG_SMALL, false)
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
                atoms.insert(name.to_string(), g);
                g
            }
        };
        let as_int = self
            .builder
            .build_ptr_to_int(global.as_pointer_value(), self.i64t, "atom.addr")
            .map_err(be)?;
        self.builder
            .build_or(
                as_int,
                self.i64t.const_int(TAG_ATOM, false),
                "atom",
            )
            .map_err(be)
    }

    // ---- module compilation ----

    fn compile(&self, ast: &Module, entry: &FunName) -> CgResult<()> {
        if entry.arity != 0 {
            return Err(format!(
                "entry function {}/{} must have arity 0",
                entry.name, entry.arity
            ));
        }
        let reachable = reachable_funs(ast, entry)?;

        // Declare reachable functions first so any order of definition works.
        for (fname, fun) in &ast.definitions {
            if !reachable.contains(fname) {
                continue;
            }
            let params: Vec<BasicMetadataTypeEnum> = (0..fun.params.len())
                .map(|_| BasicMetadataTypeEnum::IntType(self.i64t))
                .collect();
            let fty = self.i64t.fn_type(&params, false);
            let f = self
                .module
                .add_function(&mangle(&self.module_name, fname), fty, None);
            self.fns.borrow_mut().insert(fname.clone(), f);
        }

        for (fname, fun) in &ast.definitions {
            if !reachable.contains(fname) {
                continue;
            }
            self.compile_fn(fname, fun)?;
        }

        self.emit_main(entry)
    }

    fn compile_fn(&self, fname: &FunName, fun: &Fun) -> CgResult<()> {
        let f = self.fns.borrow()[fname];
        let entry = self.ctx.append_basic_block(f, "entry");
        self.builder.position_at_end(entry);
        let mut env: Env<'ctx> = HashMap::new();
        for (i, p) in fun.params.iter().enumerate() {
            let v = f.get_nth_param(i as u32).unwrap().into_int_value();
            v.set_name(p);
            env.insert(p.clone(), v);
        }
        self.compile_tail(f, &fun.body, &mut env)
    }

    fn emit_main(&self, entry: &FunName) -> CgResult<()> {
        let i32t = self.ctx.i32_type();
        let main = self.module.add_function("main", i32t.fn_type(&[], false), None);
        let bb = self.ctx.append_basic_block(main, "entry");
        self.builder.position_at_end(bb);
        let target = self.fns.borrow()[entry];
        self.builder
            .build_call(target, &[], "ret")
            .map_err(be)?;
        self.builder
            .build_return(Some(&i32t.const_zero()))
            .map_err(be)?;
        Ok(())
    }

    // ---- expression compilation ----

    /// Compile `e` in tail position: every path ends in `ret` (or unreachable).
    fn compile_tail(
        &self,
        f: FunctionValue<'ctx>,
        e: &Expr,
        env: &mut Env<'ctx>,
    ) -> CgResult<()> {
        match e {
            Expr::Let { vars, arg, body } => {
                self.bind_let(f, vars, arg, env)?;
                self.compile_tail(f, body, env)
            }
            Expr::Do(first, then) => {
                self.compile_value(f, first, env)?;
                self.compile_tail(f, then, env)
            }
            Expr::Case { arg, clauses } => {
                let vals = self.compile_case_arg(f, arg, env)?;
                self.compile_case(f, &vals, clauses, env, None)
            }
            Expr::Apply {
                target: ApplyTarget::LocalFun(fname),
                args,
            } => {
                let callee = self.local_fn(fname)?;
                let argv = self.compile_args(f, args, env)?;
                let call = self
                    .builder
                    .build_call(callee, &argv, "tail")
                    .map_err(be)?;
                call.set_tail_call(true);
                let v = call_result(call)?;
                self.builder.build_return(Some(&v)).map_err(be)?;
                Ok(())
            }
            Expr::PrimOp { name, args } if is_raise(name) => {
                self.compile_raise(f, name, args, env)
            }
            _ => {
                let v = self.compile_value(f, e, env)?;
                self.builder.build_return(Some(&v)).map_err(be)?;
                Ok(())
            }
        }
    }

    /// Compile `e` for its value in the current block.
    fn compile_value(
        &self,
        f: FunctionValue<'ctx>,
        e: &Expr,
        env: &mut Env<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        match e {
            Expr::Var(v) => env
                .get(v)
                .copied()
                .ok_or_else(|| format!("unbound variable {}", v)),
            Expr::Lit(l) => self.compile_literal(l),
            Expr::Tuple(items) => {
                let vals = items
                    .iter()
                    .map(|it| self.compile_value(f, it, env))
                    .collect::<CgResult<Vec<_>>>()?;
                let p = self.alloc_words(1 + vals.len() as u64)?;
                let header = self
                    .i64t
                    .const_int(((vals.len() as u64) << 8) | KIND_TUPLE, false);
                self.store_word(p, 0, header)?;
                for (i, v) in vals.iter().enumerate() {
                    self.store_word(p, 1 + i as u64, *v)?;
                }
                self.builder
                    .build_ptr_to_int(p, self.i64t, "tuple")
                    .map_err(be)
            }
            Expr::Cons(h, t) => {
                let hv = self.compile_value(f, h, env)?;
                let tv = self.compile_value(f, t, env)?;
                let p = self.alloc_words(2)?;
                self.store_word(p, 0, hv)?;
                self.store_word(p, 1, tv)?;
                let as_int = self
                    .builder
                    .build_ptr_to_int(p, self.i64t, "cons.addr")
                    .map_err(be)?;
                self.builder
                    .build_or(as_int, self.i64t.const_int(TAG_CONS, false), "cons")
                    .map_err(be)
            }
            Expr::Let { vars, arg, body } => {
                self.bind_let(f, vars, arg, env)?;
                self.compile_value(f, body, env)
            }
            Expr::Do(first, then) => {
                self.compile_value(f, first, env)?;
                self.compile_value(f, then, env)
            }
            Expr::Apply {
                target: ApplyTarget::LocalFun(fname),
                args,
            } => {
                let callee = self.local_fn(fname)?;
                let argv = self.compile_args(f, args, env)?;
                let call = self.builder.build_call(callee, &argv, "call").map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            Expr::Apply { .. } => Err("apply of a fun value is not supported yet (closures)".into()),
            Expr::Call { module, name, args } => self.compile_bif(f, module, name, args, env),
            Expr::PrimOp { name, args } if is_raise(name) => {
                self.compile_raise(f, name, args, env)?;
                // continue in a dead block so callers can keep building
                let dead = self.ctx.append_basic_block(f, "dead");
                self.builder.position_at_end(dead);
                Ok(self.i64t.get_undef())
            }
            Expr::PrimOp { name, .. } => Err(format!("unsupported primop {}", name)),
            Expr::Case { arg, clauses } => {
                let vals = self.compile_case_arg(f, arg, env)?;
                let merge = self.ctx.append_basic_block(f, "case.merge");
                let mut incoming: Vec<(IntValue<'ctx>, BasicBlock<'ctx>)> = Vec::new();
                self.compile_case(f, &vals, clauses, env, Some((merge, &mut incoming)))?;
                self.builder.position_at_end(merge);
                let phi = self.builder.build_phi(self.i64t, "case.val").map_err(be)?;
                for (v, bb) in &incoming {
                    phi.add_incoming(&[(v, *bb)]);
                }
                Ok(phi.as_basic_value().into_int_value())
            }
            Expr::Values(_) => Err("multi-value expression outside let/case".into()),
            Expr::Binary(_) => Err("bitstring construction is not supported yet".into()),
            Expr::Fun(_) => Err("fun expressions (closures) are not supported yet".into()),
            Expr::LetRec { .. } => {
                Err("letrec is not supported yet (list comprehensions)".into())
            }
        }
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
        env: &mut Env<'ctx>,
    ) -> CgResult<()> {
        match (vars.len(), arg) {
            (1, _) => {
                let v = self.compile_value(f, arg, env)?;
                env.insert(vars[0].clone(), v);
                Ok(())
            }
            (_, Expr::Values(es)) if es.len() == vars.len() => {
                for (var, e) in vars.iter().zip(es) {
                    let v = self.compile_value(f, e, env)?;
                    env.insert(var.clone(), v);
                }
                Ok(())
            }
            _ => Err("multi-value let from a non-values expression is not supported".into()),
        }
    }

    fn compile_case_arg(
        &self,
        f: FunctionValue<'ctx>,
        arg: &Expr,
        env: &mut Env<'ctx>,
    ) -> CgResult<Vec<IntValue<'ctx>>> {
        match arg {
            Expr::Values(es) => es
                .iter()
                .map(|e| self.compile_value(f, e, env))
                .collect(),
            other => Ok(vec![self.compile_value(f, other, env)?]),
        }
    }

    /// Compile case clauses as a chain of test blocks. In tail mode
    /// (merge == None) each body returns; otherwise bodies jump to merge.
    fn compile_case(
        &self,
        f: FunctionValue<'ctx>,
        vals: &[IntValue<'ctx>],
        clauses: &[Clause],
        env: &Env<'ctx>,
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
            if clause.patterns.len() != vals.len() {
                return Err(format!(
                    "clause has {} patterns but case argument has {} values",
                    clause.patterns.len(),
                    vals.len()
                ));
            }
            let mut cenv = env.clone();
            for (v, p) in vals.iter().zip(&clause.patterns) {
                self.match_pattern(f, *v, p, &mut cenv, next)?;
            }
            // guard
            if !is_true_atom(&clause.guard) {
                let g = self.compile_value(f, &clause.guard, &mut cenv)?;
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
                None => self.compile_tail(f, &clause.body, &mut cenv)?,
                Some((merge_bb, ref mut incoming)) => {
                    let v = self.compile_value(f, &clause.body, &mut cenv)?;
                    let cur = self.builder.get_insert_block().unwrap();
                    incoming.push((v, cur));
                    self.builder.build_unconditional_branch(merge_bb).map_err(be)?;
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

    /// Emit tests for `pat` against `val` in the current block, branching to
    /// `fail` on mismatch. Bindings go into `env`.
    fn match_pattern(
        &self,
        f: FunctionValue<'ctx>,
        val: IntValue<'ctx>,
        pat: &Pattern,
        env: &mut Env<'ctx>,
        fail: BasicBlock<'ctx>,
    ) -> CgResult<()> {
        match pat {
            Pattern::Var(v) => {
                env.insert(v.clone(), val);
                Ok(())
            }
            Pattern::Alias(v, inner) => {
                env.insert(v.clone(), val);
                self.match_pattern(f, val, inner, env, fail)
            }
            Pattern::Lit(Literal::Float(_)) => Err("float patterns not supported yet".into()),
            Pattern::Binary(_) => Err("bitstring patterns are not supported yet".into()),
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
                    self.match_pattern(f, elem, sub, env, fail)?;
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
                    .build_and(
                        val,
                        self.i64t.const_int(!TAG_MASK, false),
                        "cons.addr",
                    )
                    .map_err(be)?;
                let p = self
                    .builder
                    .build_int_to_ptr(addr, self.ptrt, "cons.ptr")
                    .map_err(be)?;
                let head = self.load_word(p, 0)?;
                self.match_pattern(f, head, h, env, fail)?;
                let tail = self.load_word(p, 1)?;
                self.match_pattern(f, tail, t, env, fail)
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

    // ---- BIFs ----

    fn compile_bif(
        &self,
        f: FunctionValue<'ctx>,
        module: &str,
        name: &str,
        args: &[Expr],
        env: &mut Env<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        if module != "erlang" {
            return Err(format!(
                "unsupported remote call {}:{}/{}",
                module,
                name,
                args.len()
            ));
        }
        let argv: Vec<IntValue<'ctx>> = args
            .iter()
            .map(|a| self.compile_value(f, a, env))
            .collect::<CgResult<_>>()?;

        match (name, argv.len()) {
            ("+", 2) | ("-", 2) | ("*", 2) | ("div", 2) | ("rem", 2) => {
                // TODO(bignum): no overflow checks; ints wrap in small range.
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
                // Correct for small ints (tagging is monotone) and for exact
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
            _ => Err(format!("unsupported BIF erlang:{}/{}", name, argv.len())),
        }
    }

    fn compile_raise(
        &self,
        f: FunctionValue<'ctx>,
        _name: &str,
        args: &[Expr],
        env: &mut Env<'ctx>,
    ) -> CgResult<()> {
        let reason = match args.first() {
            Some(a) => self.compile_value(f, a, env)?,
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

    fn compile_args(
        &self,
        f: FunctionValue<'ctx>,
        args: &[Expr],
        env: &mut Env<'ctx>,
    ) -> CgResult<Vec<inkwell::values::BasicMetadataValueEnum<'ctx>>> {
        args.iter()
            .map(|a| Ok(self.compile_value(f, a, env)?.into()))
            .collect()
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

    fn alloc_words(&self, n: u64) -> CgResult<inkwell::values::PointerValue<'ctx>> {
        let call = self
            .builder
            .build_call(
                self.rt_alloc(),
                &[self.i64t.const_int(n, false).into()],
                "alloc",
            )
            .map_err(be)?;
        Ok(call_result(call)?.into_pointer_value())
    }

    fn store_word(
        &self,
        p: inkwell::values::PointerValue<'ctx>,
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

    fn load_word(
        &self,
        p: inkwell::values::PointerValue<'ctx>,
        index: u64,
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

fn is_raise(primop: &str) -> bool {
    matches!(primop, "match_fail" | "raise" | "error" | "exit" | "throw")
}

/// Functions transitively reachable from `entry` via `apply` of local fnames.
/// (Fun-value escapes don't exist yet — closures are unsupported.)
fn reachable_funs(ast: &Module, entry: &FunName) -> CgResult<HashSet<FunName>> {
    let defs: HashMap<&FunName, &Fun> = ast.definitions.iter().map(|(f, b)| (f, b)).collect();
    if !defs.contains_key(entry) {
        let known: Vec<String> = ast
            .definitions
            .iter()
            .map(|(f, _)| format!("{}/{}", f.name, f.arity))
            .collect();
        return Err(format!(
            "entry function {}/{} is not defined in module '{}' (defined: {})",
            entry.name,
            entry.arity,
            ast.name,
            known.join(", ")
        ));
    }
    let mut seen: HashSet<FunName> = HashSet::new();
    let mut work = vec![entry.clone()];
    while let Some(f) = work.pop() {
        if !seen.insert(f.clone()) {
            continue;
        }
        if let Some(fun) = defs.get(&f) {
            let mut targets = Vec::new();
            collect_applies(&fun.body, &mut targets);
            work.extend(targets);
        }
    }
    Ok(seen)
}

fn collect_applies(e: &Expr, out: &mut Vec<FunName>) {
    match e {
        Expr::Var(_) | Expr::Lit(_) => {}
        Expr::Tuple(items) | Expr::Values(items) => {
            items.iter().for_each(|i| collect_applies(i, out))
        }
        Expr::Cons(h, t) => {
            collect_applies(h, out);
            collect_applies(t, out);
        }
        Expr::Fun(f) => collect_applies(&f.body, out),
        Expr::Let { arg, body, .. } => {
            collect_applies(arg, out);
            collect_applies(body, out);
        }
        Expr::LetRec { defs, body } => {
            defs.iter().for_each(|(_, f)| collect_applies(&f.body, out));
            collect_applies(body, out);
        }
        Expr::Apply { target, args } => {
            if let ApplyTarget::LocalFun(f) = target {
                out.push(f.clone());
            }
            args.iter().for_each(|a| collect_applies(a, out));
        }
        Expr::Call { args, .. } | Expr::PrimOp { args, .. } => {
            args.iter().for_each(|a| collect_applies(a, out))
        }
        Expr::Case { arg, clauses } => {
            collect_applies(arg, out);
            for c in clauses {
                collect_applies(&c.guard, out);
                collect_applies(&c.body, out);
            }
        }
        Expr::Binary(segs) => {
            for s in segs {
                collect_applies(&s.value, out);
                s.spec.iter().for_each(|x| collect_applies(x, out));
            }
        }
        Expr::Do(a, b) => {
            collect_applies(a, out);
            collect_applies(b, out);
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
