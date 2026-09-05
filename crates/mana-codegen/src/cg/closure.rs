//! Closures: free variable analysis, closure objects, lambda lifting of
//! `fun` and `letrec` bodies, and shims for top-level functions.
//!
//! Contract: a fun value is a boxed `[header | code | captures...]` object.
//! Every fun body takes the closure as its last argument, after the
//! arguments of the fun. The `apply` path checks the tag, the kind, and
//! the arity before it makes the indirect call.

use crate::*;

/// Collapse a directly nested letrec chain (`letrec A in letrec B in ...`)
/// into one group. Every member of the group sees every other member.
///
/// The Erlang compiler emits nested single-member letrecs for shared match
/// continuations. It annotates them `letrec_goto`. The body of an inner
/// label calls an outer label. After lambda lifting, the lifted inner body
/// gets a fresh scope. That scope does not see the outer label, so the
/// call does not resolve.
///
/// The merged group makes every label a sibling of every other label.
/// This visibility is a superset of the original visibility, where outer
/// labels are defined first. Therefore the merge is safe.
///
/// The loop stops when a bound name collides with a name in the group. It
/// also stops when the body is not directly another letrec, that is, when
/// something is bound between the letrecs.
pub(crate) fn flatten_letrec<'a>(
    defs: &[(FunName, Fun)],
    body: &'a Expr,
) -> (Vec<(FunName, Fun)>, &'a Expr) {
    let mut group: Vec<(FunName, Fun)> = defs.to_vec();
    let mut cur = body;
    while let Expr::LetRec {
        defs: inner_defs,
        body: inner_body,
    } = cur
    {
        let collides = inner_defs
            .iter()
            .any(|(n, _)| group.iter().any(|(m, _)| m == n));
        if collides {
            break;
        }
        group.extend(inner_defs.iter().cloned());
        cur = inner_body;
    }
    (group, cur)
}

pub(crate) fn free_vars(e: &Expr, bound: &mut HashSet<String>, out: &mut BTreeSet<String>) {
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
        Expr::CallDyn { module, name, args } => {
            free_vars(module, bound, out);
            free_vars(name, bound, out);
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

pub(crate) fn pattern_vars(p: &Pattern, out: &mut Vec<String>) {
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

impl<'ctx, 'p> Cg<'ctx, 'p> {
    /// Compile any `apply`. If `tail` is set, this pops the frame just before
    /// the call. Returns the call site and a flag that says if the callee can
    /// raise. A tail call propagates the sentinel through the return value at
    /// no cost. A non-tail caller must `check_exc`.
    pub(crate) fn compile_apply(
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
                    let call = self.call_compiled(lf, &argv, "call", tail)?;
                    Ok((call, true)) // letrec bodies: assume that they can raise
                } else {
                    let callee = self.local_fn(fname)?;
                    let may_raise = self
                        .raise_set
                        .contains(&(self.module_name.clone(), fname.clone()));
                    let argv = self.eval_args(f, args, scope)?;
                    if tail {
                        self.pop_frame()?;
                    }
                    let call = self.call_compiled(callee, &argv, "call", false)?;
                    Ok((call, may_raise))
                }
            }
            ApplyTarget::Var(v) => {
                let argv = self.eval_args(f, args, scope)?;
                let fun_val = self.read_var(scope, v)?;
                // A musttail releases this frame before the callee runs. Unlink
                // the root frame first, as in the LocalFun arms above. If not,
                // the GC of the callee walks a dead alloca.
                if tail {
                    self.pop_frame()?;
                }
                let call = self.compile_apply_value(f, fun_val, &argv, args.len(), tail)?;
                Ok((call, true))
            }
        }
    }

    /// Apply a fun value. Check the tag, the kind, and the arity. Then make
    /// an indirect call with `(ctx, args..., closure)`.
    pub(crate) fn compile_apply_value(
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
        let packed = self.pack_args(&full_args)?;
        let call = self
            .builder
            .build_indirect_call(self.term_fn_type(nargs + 1), code_ptr, &packed, "apply")
            .map_err(be)?;
        // Fun bodies (lifts and shims) are tailcc with the uniform prototype.
        call.set_call_convention(Self::TAILCC);
        if tail {
            self.mark_tail(call);
        }
        Ok(call)
    }

    /// Build a boxed (tag 000) closure `[header | code | captures...]`. It
    /// allocates first, then reads the captures from their variable bindings.
    /// This order is safe because the allocation is the only GC point.
    pub(crate) fn make_closure(
        &self,
        code: FunctionValue<'ctx>,
        arity: usize,
        capture_names: &[String],
        scope: &Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let header = self.i64t.const_int(
            ((capture_names.len() as u64) << 16) | ((arity as u64) << 8) | KIND_FUN,
            false,
        );
        // A fun without captures is a static constant per code pointer, with
        // no allocation. This is safe: forward_major/minor pass non-heap
        // boxed terms through.
        if capture_names.is_empty() {
            let sym = format!("mana_fun.{}", code.get_name().to_string_lossy());
            let g = match self.module.get_global(&sym) {
                Some(g) => g,
                None => {
                    let init = self.ctx.const_struct(
                        &[
                            header.into(),
                            code.as_global_value().as_pointer_value().into(),
                        ],
                        false,
                    );
                    let g = self.module.add_global(init.get_type(), None, &sym);
                    g.set_initializer(&init);
                    g.set_constant(true);
                    g.set_alignment(8);
                    g.set_linkage(Linkage::LinkOnceODR);
                    g
                }
            };
            return self
                .builder
                .build_ptr_to_int(g.as_pointer_value(), self.i64t, "fun.static")
                .map_err(be);
        }
        let p = self.alloc_words(2 + capture_names.len() as u64)?;
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

    pub(crate) fn declare_lift(&self, hint: &str, arity: usize) -> usize {
        let n = self.lift_counter.get();
        self.lift_counter.set(n + 1);
        let name = format!(
            "mn_{}.l{}.{}",
            sanitize(&self.module_name),
            n,
            sanitize(hint)
        );
        let f = self.declare_compiled(&name, arity + 1);
        f.set_linkage(Linkage::Internal);
        let mut lifted = self.lifted.borrow_mut();
        lifted.push(f);
        lifted.len() - 1
    }

    /// Lift a letrec group. The members share one capture environment and
    /// call each other directly. Returns the scope extended with the funs of
    /// the group.
    pub(crate) fn bind_letrec(
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

        // The whole group shares one closure object for direct calls. Its
        // code pointer (the first member) is never used through apply.
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

    /// Build a shim that adapts a plain top-level function to the closure
    /// calling convention. The shim is frameless: it holds no live terms
    /// across the call.
    pub(crate) fn fun_shim(&self, module: Option<&str>, fname: &FunName) -> CgResult<FunctionValue<'ctx>> {
        let target_mod = module.unwrap_or(&self.module_name);
        let sym = format!("{}.shim", mangle(target_mod, fname));
        if let Some(existing) = self.module.get_function(&sym) {
            return Ok(existing);
        }
        // A fun capture of a missing module follows BEAM: build the shim as
        // a stub that aborts if it is ever called. An Err here leaks a
        // bodyless linkonce declaration and poisons the whole caller.
        if module.is_some()
            && !is_bif_module(target_mod)
            && self.missing_modules.borrow().contains(target_mod)
        {
            let shim = self.declare_compiled(&sym, fname.arity + 1);
            shim.set_linkage(Linkage::LinkOnceODR);
            let saved_bb = self.builder.get_insert_block();
            let msg = format!(
                "fun {}:{}/{}: module '{}' is not compiled",
                target_mod, fname.name, fname.arity, target_mod
            );
            self.emit_unsupported_stub(shim, &msg)?;
            if let Some(bb) = saved_bb {
                self.builder.position_at_end(bb);
            }
            return Ok(shim);
        }
        let shim = self.declare_compiled(&sym, fname.arity + 1);
        shim.set_linkage(Linkage::LinkOnceODR);

        // A BIF-module target has no symbol to forward to. Give the shim a
        // real compiled body that calls the BIF.
        if module.is_some() && is_bif_module(target_mod) {
            let params: Vec<String> = (0..fname.arity).map(|i| format!("_bifshim{}", i)).collect();
            let body = Expr::Call {
                module: target_mod.to_string(),
                name: fname.name.clone(),
                args: params.iter().map(|p| Expr::Var(p.clone())).collect(),
            };
            let saved_bb = self.builder.get_insert_block();
            let saved_ctx = self.cur_ctx.get();
            let saved_handlers = std::mem::take(&mut *self.handlers.borrow_mut());
            let saved_prop = self.propagate_bb.get();
            let saved_frame = self.cur_frame.get();
            let saved_slots = self.var_slots.borrow().clone();
            let saved_next = self.next_slot.get();
            let saved_cap = self.slot_cap.get();
            let saved_peak = self.peak_slot.get();
            let saved_memset = self.frame_memset.get();
            let saved_len_store = self.frame_len_store.get();
            let saved_skip = self.frame_skip.get();

            let entry = self.ctx.append_basic_block(shim, "entry");
            self.builder.position_at_end(entry);
            self.cur_ctx
                .set(Some(shim.get_nth_param(0).unwrap().into_pointer_value()));
            self.propagate_bb.set(None);
            self.setup_frame(&body, &params, &[])?;
            let mut scope = Scope::default();
            // The shim signature is `args + closure`, that is, arity + 1 terms.
            for (i, p) in params.iter().enumerate() {
                let v = self.param_at(shim, i, fname.arity + 1)?;
                self.bind_var(&mut scope, p, v)?;
            }
            let r = self.compile_tail(shim, &body, &mut scope);
            self.patch_frame();

            *self.handlers.borrow_mut() = saved_handlers;
            self.propagate_bb.set(saved_prop);
            self.cur_ctx.set(saved_ctx);
            self.cur_frame.set(saved_frame);
            *self.var_slots.borrow_mut() = saved_slots;
            self.next_slot.set(saved_next);
            self.slot_cap.set(saved_cap);
            self.peak_slot.set(saved_peak);
            self.frame_memset.set(saved_memset);
            self.frame_len_store.set(saved_len_store);
            self.frame_skip.set(saved_skip);
            if let Err(e) = r {
                // The fun captures an unsupported BIF. The shim raises at run
                // time if the fun is ever called.
                let msg = format!("fun {}:{}/{}: {}", target_mod, fname.name, fname.arity, e);
                eprintln!("manac: warning: {} stubbed", msg);
                self.emit_unsupported_stub(shim, &msg)?;
            }
            if let Some(bb) = saved_bb {
                self.builder.position_at_end(bb);
            }
            return Ok(shim);
        }

        let target = if module.is_none() || module == Some(self.module_name.as_str()) {
            self.local_fn(fname)?
        } else {
            self.remote_fn(target_mod, &fname.name, fname.arity)
        };

        let saved = self.builder.get_insert_block();
        let bb = self.ctx.append_basic_block(shim, "entry");
        self.builder.position_at_end(bb);
        // Pass ctx and the args. Drop the trailing closure param of the shim
        // (the shim has arity+1 params).
        let mut argv: Vec<BasicMetadataValueEnum> = vec![shim.get_nth_param(0).unwrap().into()];
        for i in 0..fname.arity {
            argv.push(self.param_at(shim, i, fname.arity + 1)?.into());
        }
        let call = self.call_compiled(target, &argv, "fwd", true)?;
        let v = call_result(call)?;
        self.builder.build_return(Some(&v)).map_err(be)?;
        if let Some(bb) = saved {
            self.builder.position_at_end(bb);
        }
        Ok(shim)
    }
}
