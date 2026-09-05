//! Module compilation: declare every included function, compile each body,
//! and emit `main` for the entry module.
//!
//! Contract: a function that the compiler cannot compile becomes a stub
//! that prints a message and exits. A call into a module that is not
//! compiled aborts at the call site. Both choices keep the may-raise
//! analysis consistent.

use crate::*;

impl<'ctx, 'p> Cg<'ctx, 'p> {
    pub(crate) fn compile(
        &self,
        ast: &Module,
        include: &HashSet<FunName>,
        entry: Option<&FunName>,
    ) -> CgResult<()> {
        // Module and function names are atoms on BEAM. They must satisfy
        // binary_to_existing_atom, and the S4 export table will need them.
        self.atom_global(&ast.name);
        for b in &ast.behaviours {
            self.atom_global(b);
            self.behaviours
                .borrow_mut()
                .push((ast.name.clone(), b.clone()));
        }
        for (fname, _) in &ast.definitions {
            if include.contains(fname) {
                self.atom_global(&fname.name);
            }
        }
        let exported: HashSet<&FunName> = ast.exports.iter().collect();
        for (fname, fun) in &ast.definitions {
            if !include.contains(fname) {
                continue;
            }
            let f = self.declare_compiled(&mangle(&self.module_name, fname), fun.params.len());
            self.fns.borrow_mut().insert(fname.clone(), f);
            if exported.contains(fname) && fname.name != "module_info" {
                self.exports.borrow_mut().push((fname.clone(), f));
            }
        }

        for (fname, fun) in &ast.definitions {
            if !include.contains(fname) {
                continue;
            }
            if self.emit_native_override(fname)? {
                continue;
            }
            if let Err(e) = self.compile_fn(fname, fun) {
                // Function-granular poisoning: stdlib modules contain
                // corners that we do not compile yet (sub-byte bitstrings,
                // and more). The function becomes a stub that reports and
                // exits if a program reaches it. Lifts that this function
                // already queued get stubbed too, because they were declared.
                eprintln!(
                    "manac: warning: {}:{}/{} stubbed (unsupported: {})",
                    self.module_name, fname.name, fname.arity, e
                );
                let msg =
                    format!("{}:{}/{}: {}", self.module_name, fname.name, fname.arity, e);
                let fv = self.fns.borrow()[fname];
                self.emit_unsupported_stub(fv, &msg)?;
                loop {
                    let next = self.pending.borrow_mut().pop();
                    let Some(l) = next else { break };
                    let lf = self.lifted.borrow()[l.f_index];
                    self.emit_unsupported_stub(lf, &msg)?;
                }
            }
            self.drain_lifts()?;
        }

        match entry {
            Some(e) => self.emit_main(e),
            None => Ok(()),
        }
    }

    /// Wipe a half-compiled function and replace its body with a loud
    /// runtime failure (print + exit). The stub aborts and does not raise.
    /// This keeps the may-raise analysis consistent, because callers do not
    /// always check.
    pub(crate) fn emit_unsupported_stub(&self, f: FunctionValue<'ctx>, msg: &str) -> CgResult<()> {
        // Never delete half-built blocks. If you erase a block that another
        // block still branches to, the module becomes corrupt. LLVM erase
        // does not fix up uses. This fault appeared as glibc heap
        // corruption. Instead, terminate every unterminated block and
        // prepend a fresh entry. The old body becomes unreachable garbage
        // that O2 removes.
        for bb in f.get_basic_blocks() {
            if bb.get_terminator().is_none() {
                self.builder.position_at_end(bb);
                self.builder.build_unreachable().map_err(be)?;
            }
        }
        let entry = match f.get_first_basic_block() {
            Some(first) => self
                .ctx
                .prepend_basic_block(first, "stub.entry"),
            None => self.ctx.append_basic_block(f, "entry"),
        };
        self.builder.position_at_end(entry);
        let ptr = self.static_bytes(msg.as_bytes())?;
        let callee = self.rt_fn("mana_rt_unsupported", || {
            self.ctx.void_type().fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        });
        self.builder
            .build_call(
                callee,
                &[
                    ptr.into(),
                    self.i64t.const_int(msg.len() as u64, false).into(),
                ],
                "",
            )
            .map_err(be)?;
        self.builder.build_unreachable().map_err(be)?;
        Ok(())
    }

    /// A call into a module that is not compiled. BEAM loads such code and
    /// fails only when the call executes. So the abort happens at the CALL
    /// SITE (print + exit, like unsupported stubs), and the whole caller is
    /// not stubbed. The abort keeps the may-raise analysis consistent.
    /// Guarded dead branches (`if mix_available?(), do: Mix...`) stay live.
    /// Returns a dummy value, positioned in a dead block.
    pub(crate) fn emit_missing_call_abort(
        &self,
        f: FunctionValue<'ctx>,
        module: &str,
        name: &str,
        arity: usize,
    ) -> CgResult<IntValue<'ctx>> {
        let msg = format!(
            "{}: call into missing module {}:{}/{}",
            self.module_name, module, name, arity
        );
        let ptr = self.static_bytes(msg.as_bytes())?;
        let callee = self.rt_fn("mana_rt_unsupported", || {
            self.ctx.void_type().fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        });
        self.builder
            .build_call(
                callee,
                &[
                    ptr.into(),
                    self.i64t.const_int(msg.len() as u64, false).into(),
                ],
                "",
            )
            .map_err(be)?;
        self.builder.build_unreachable().map_err(be)?;
        let dead = self.ctx.append_basic_block(f, "missing.dead");
        self.builder.position_at_end(dead);
        Ok(self.i64t.const_int(NIL, false))
    }

    /// Functions that BEAM implements in C (nif_error stubs in lists.erl and
    /// binary.erl) get native bodies. Returns true if this function handled
    /// the definition. A plan is (helper, drop_trailing_args,
    /// extra_const_args). The helper "" means the identity function
    /// (compile_pattern).
    pub(crate) fn emit_native_override(&self, fname: &FunName) -> CgResult<bool> {
        const NIL_C: u64 = 0b011;
        const SMALL0: u64 = 0b001;
        const SMALL1: u64 = (1 << 3) | 0b001;
        let plan: (&str, usize, &[u64]) =
            match (self.module_name.as_str(), fname.name.as_str(), fname.arity) {
                ("lists", "reverse", 2) => ("mana_rt_lists_reverse", 0, &[]),
                ("lists", "member", 2) => ("mana_rt_lists_member", 0, &[]),
                ("lists", "keyfind", 3) => ("mana_rt_lists_keyfind", 0, &[0]),
                ("lists", "keymember", 3) => ("mana_rt_lists_keyfind", 0, &[1]),
                ("lists", "keysearch", 3) => ("mana_rt_lists_keyfind", 0, &[2]),
                ("binary", "split", 2) => ("mana_rt_binary_split", 0, &[NIL_C]),
                ("binary", "split", 3) => ("mana_rt_binary_split", 0, &[]),
                ("binary", "match", 2) => ("mana_rt_binary_match", 0, &[0]),
                ("binary", "match", 3) => ("mana_rt_binary_match", 1, &[0]),
                ("binary", "matches", 2) => ("mana_rt_binary_match", 0, &[1]),
                ("binary", "matches", 3) => ("mana_rt_binary_match", 1, &[1]),
                ("binary", "part", 3) => ("mana_rt_binary_part", 0, &[]),
                ("binary", "copy", 1) => ("mana_rt_binary_copy", 0, &[SMALL1]),
                ("binary", "copy", 2) => ("mana_rt_binary_copy", 0, &[]),
                ("binary", "at", 2) => ("mana_rt_binary_at", 0, &[0]),
                ("binary", "first", 1) => ("mana_rt_binary_at", 0, &[SMALL0, 0]),
                ("binary", "last", 1) => ("mana_rt_binary_at", 0, &[SMALL0, 1]),
                ("binary", "encode_unsigned", 1) => ("mana_rt_binary_encode_unsigned", 0, &[0]),
                ("binary", "decode_unsigned", 1) => ("mana_rt_binary_decode_unsigned", 0, &[0]),
                ("binary", "decode_unsigned", 2) => ("mana_rt_binary_decode_unsigned", 0, &[]),
                ("binary", "longest_common_prefix", 1) => ("mana_rt_binary_lcp", 0, &[0]),
                ("binary", "longest_common_suffix", 1) => ("mana_rt_binary_lcp", 0, &[1]),
                ("binary", "list_to_bin", 1) => ("mana_rt_list_to_binary", 0, &[]),
                ("binary", "referenced_byte_size", 1) => ("mana_rt_byte_size", 0, &[]),
                ("binary", "compile_pattern", 1) => ("", 0, &[]),
                // TODO(bitstring): Elixir.Float decomposes IEEE bits with
                // sub-bit segments, so the precision ops go native (see the
                // Elixir.Float entries below).
                // The time functions of os.erl are nif_error stubs (real BIFs
                // on BEAM). The constant for the /0 form is 1_000_000_000 Hz,
                // that is, the native unit (nanoseconds).
                ("os", "system_time", 0) => {
                    ("mana_rt_system_time", 0, &[(1_000_000_000u64 << 3) | 0b001])
                }
                ("os", "system_time", 1) => ("mana_rt_system_time", 0, &[]),
                ("os", "getenv", 1) => ("mana_rt_os_getenv", 0, &[]),
                // Compiler-gap overrides (AGENTS.md "BIF rule" #3): Elixir
                // library code that we cannot compile yet. Delete each entry
                // when its gap closes. Never add one for code that compiles
                // today.
                // TODO(port): System.cmd uses Erlang ports.
                ("Elixir.System", "cmd", 2) => ("mana_rt_system_cmd", 0, &[NIL_C]),
                ("Elixir.System", "cmd", 3) => ("mana_rt_system_cmd", 0, &[]),
                // TODO(bitstring): Float.round/ceil/floor decompose IEEE
                // bits with sub-byte segments.
                ("Elixir.Float", "round", 2) => ("mana_rt_float_prec", 0, &[0]),
                ("Elixir.Float", "ceil", 2) => ("mana_rt_float_prec", 0, &[1]),
                ("Elixir.Float", "floor", 2) => ("mana_rt_float_prec", 0, &[2]),
                _ => return Ok(false),
            };
        let f = self.fns.borrow()[fname];
        let entry = self.ctx.append_basic_block(f, "entry");
        self.builder.position_at_end(entry);
        self.cur_ctx
            .set(Some(f.get_nth_param(0).unwrap().into_pointer_value()));
        self.handlers.borrow_mut().clear();
        self.propagate_bb.set(None);
        self.cur_frame.set(None); // frameless: the body is a single forwarding call
        if plan.0.is_empty() {
            // identity: compile_pattern patterns are plain binaries here
            let v = self.param_at(f, 0, fname.arity)?;
            self.builder.build_return(Some(&v)).map_err(be)?;
            return Ok(true);
        }
        let mut cargs: Vec<BasicMetadataValueEnum> = vec![self.ctx_val().into()];
        for i in 0..fname.arity - plan.1 {
            cargs.push(self.param_at(f, i, fname.arity)?.into());
        }
        for &c in plan.2 {
            cargs.push(self.i64t.const_int(c, false).into());
        }
        let nparams = cargs.len() - 1;
        let callee = self.rt_fn(plan.0, || {
            let mut ps: Vec<BasicMetadataTypeEnum> =
                vec![BasicMetadataTypeEnum::PointerType(self.ptrt)];
            ps.extend((0..nparams).map(|_| BasicMetadataTypeEnum::IntType(self.i64t)));
            self.i64t.fn_type(&ps, false)
        });
        let call = self.builder.build_call(callee, &cargs, "natbif").map_err(be)?;
        // raising convention: the sentinel propagates through the return value
        let v = call_result(call)?;
        self.builder.build_return(Some(&v)).map_err(be)?;
        Ok(true)
    }

    pub(crate) fn compile_fn(&self, fname: &FunName, fun: &Fun) -> CgResult<()> {
        let f = self.fns.borrow()[fname];
        let entry = self.ctx.append_basic_block(f, "entry");
        self.builder.position_at_end(entry);
        self.cur_ctx
            .set(Some(f.get_nth_param(0).unwrap().into_pointer_value()));
        self.handlers.borrow_mut().clear();
        self.propagate_bb.set(None);
        // Read the args first. The spill area is only valid until the next call.
        let n = fun.params.len();
        let vals: Vec<IntValue> = (0..n).map(|i| self.param_at(f, i, n)).collect::<CgResult<_>>()?;
        self.setup_frame(&fun.body, &fun.params, &[])?;
        let mut scope = Scope::default();
        for (i, p) in fun.params.iter().enumerate() {
            let v = vals[i];
            v.set_name(p);
            self.bind_var(&mut scope, p, v)?;
        }
        self.emit_reduction_check(f)?;
        let r = self.compile_tail(f, &fun.body, &mut scope);
        self.patch_frame();
        r
    }

    /// Preemption point: decrement the reduction budget, and yield to the
    /// scheduler when the budget is exhausted. Only framed functions get this
    /// check, and only AFTER the params are rooted. Yield points are GC
    /// points. Everything live is already in frame slots here, so preemption
    /// costs no extra spills.
    pub(crate) fn emit_reduction_check(&self, f: FunctionValue<'ctx>) -> CgResult<()> {
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

    /// Compile the bodies of the lambda-lifted funs that compilation queued.
    pub(crate) fn drain_lifts(&self) -> CgResult<()> {
        loop {
            // Pop in its own statement. A `while let` scrutinee holds the
            // RefMut across the body, and bodies push new lifts.
            let next = self.pending.borrow_mut().pop();
            let Some(l) = next else { break };
            let f = self.lifted.borrow()[l.f_index];
            if let Err(e) = self.compile_lift(f, &l) {
                // Function-granular poisoning, the same as for named functions.
                eprintln!(
                    "manac: warning: {} lifted fun stubbed (unsupported: {})",
                    self.module_name, e
                );
                let msg = format!("{}: anonymous fun: {}", self.module_name, e);
                self.emit_unsupported_stub(f, &msg)?;
            }
        }
        Ok(())
    }

    pub(crate) fn compile_lift(&self, f: FunctionValue<'ctx>, l: &Lift) -> CgResult<()> {
        {
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
            // Read the args first, with the trailing closure. The spill area
            // is only valid until the next call.
            let n = l.params.len() + 1;
            let vals: Vec<IntValue> = (0..n).map(|i| self.param_at(f, i, n)).collect::<CgResult<_>>()?;
            self.setup_frame(&l.body, &var_names, &sib_names)?;

            let mut scope = Scope::default();
            for (i, p) in l.params.iter().enumerate() {
                let v = vals[i];
                v.set_name(p);
                self.bind_var(&mut scope, p, v)?;
            }
            let closure = vals[l.params.len()];
            closure.set_name("closure");
            if !l.captures.is_empty() {
                // The loads happen before any GC point: this is the entry,
                // with no allocations yet.
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
                // The closure term itself must be rooted for sibling calls.
                // A member that never calls siblings can be frameless. Then
                // no sibling binding is ever consulted.
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
            let r = self.compile_tail(f, &l.body, &mut scope);
            self.patch_frame();
            r?;
        }
        Ok(())
    }

    /// `mana_call_fun(ctx, x0..x4, code) -> term`: the C-ABI door of the
    /// runtime into fun bodies. Fun bodies are `tailcc` with the uniform
    /// prototype. The runtime cannot call tailcc code directly (callee-pop
    /// versus caller-pop).
    pub(crate) fn emit_call_fun_trampoline(&self) -> CgResult<()> {
        let mut params: Vec<BasicMetadataTypeEnum> =
            vec![BasicMetadataTypeEnum::PointerType(self.ptrt)];
        params.extend((0..NREG).map(|_| BasicMetadataTypeEnum::IntType(self.i64t)));
        params.push(BasicMetadataTypeEnum::PointerType(self.ptrt)); // the code pointer
        let t = self.module.add_function("mana_call_fun", self.i64t.fn_type(&params, false), None);
        let bb = self.ctx.append_basic_block(t, "entry");
        self.builder.position_at_end(bb);
        let argv: Vec<BasicMetadataValueEnum> =
            (0..=NREG).map(|i| t.get_nth_param(i as u32).unwrap().into()).collect();
        let code = t.get_nth_param(1 + NREG as u32).unwrap().into_pointer_value();
        let call = self
            .builder
            .build_indirect_call(self.term_fn_type(0), code, &argv, "fun")
            .map_err(be)?;
        call.set_call_convention(Self::TAILCC);
        let v = call_result(call)?;
        self.builder.build_return(Some(&v)).map_err(be)?;
        Ok(())
    }

    pub(crate) fn emit_main(&self, entry: &FunName) -> CgResult<()> {
        self.emit_call_fun_trampoline()?;
        // make_fun/3 of an uncompiled function: a uniform tailcc body that
        // raises undef when the program applies the fun.
        let undef = self.declare_compiled("mana_fun_undef", 0);
        {
            let bb = self.ctx.append_basic_block(undef, "entry");
            self.builder.position_at_end(bb);
            let ctx = undef.get_nth_param(0).unwrap().into_pointer_value();
            let class = self.atom_term("error")?;
            let reason = self.atom_term("undef")?;
            self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
            self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
            self.builder.build_return(Some(&self.sentinel())).map_err(be)?;
        }
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
        // The runtime builds exit and monitor messages, so it needs the
        // well-known atom terms. Atoms are compiler statics.
        let names = [
            "normal", "killed", "kill", "EXIT", "DOWN", "process", "noproc", "true", "false",
            "badarg", "error", "badmap", "badkey", "undef", "ok", "module", "nofile",
            "value", "undefined", "badarith",
        ];
        let mut atom_args: Vec<BasicMetadataValueEnum> = Vec::new();
        for n in names {
            atom_args.push(self.atom_term(n)?.into());
        }
        self.builder
            .build_call(self.rt_register_atoms(), &atom_args, "")
            .map_err(be)?;

        // Seed the table in elixir_config that maps URI schemes to default
        // ports. BEAM does this in elixir:start/2. The closed world skips
        // that boot.
        self.builder
            .build_call(
                self.rt_p_void("mana_rt_seed_uri_defaults"),
                &[ctx.into()],
                "",
            )
            .map_err(be)?;

        let target = self.fns.borrow()[entry];
        let target = self.ccc_wrapper(target, 0);
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
}
