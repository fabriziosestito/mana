use crate::*;

impl<'ctx, 'p> Cg<'ctx, 'p> {
    // ---- expression compilation ----

    pub(crate) fn compile_tail(
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
                let (group, inner_body) = flatten_letrec(defs, body);
                let mut inner = self.bind_letrec(f, &group, scope)?;
                self.compile_tail(f, inner_body, &mut inner)
            }
            Expr::Do(first, then) => {
                let wm = self.next_slot.get();
                self.compile_value(f, first, scope)?;
                self.next_slot.set(wm);
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
                // every compiled callee (named, lift, shim, fun object) has
                // the uniform tailcc prototype: guaranteed tail call
                self.mark_tail(call);
                let v = call_result(call)?;
                self.builder.build_return(Some(&v)).map_err(be)?;
                Ok(())
            }
            Expr::Call { module, name, args }
                if !is_bif_module(module) && !is_native_module(module) =>
            {
                if self.missing_modules.borrow().contains(module) {
                    let v = self.emit_missing_call_abort(f, module, name, args.len())?;
                    self.builder.build_return(Some(&v)).map_err(be)?;
                    return Ok(());
                }
                let callee = self.remote_fn(module, name, args.len());
                let argv = self.eval_args(f, args, scope)?;
                self.pop_frame()?;
                let call = self.call_compiled(callee, &argv, "tail", true)?;
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

    pub(crate) fn compile_value(
        &self,
        f: FunctionValue<'ctx>,
        e: &Expr,
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        match e {
            Expr::Var(v) => self.read_var(scope, v),
            Expr::Lit(l) => self.compile_literal(l),
            Expr::Tuple(items) => {
                if let Some(c) = self.const_term(f, e)? {
                    return Ok(c);
                }
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
                if let Some(c) = self.const_term(f, e)? {
                    return Ok(c);
                }
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
                let (group, inner_body) = flatten_letrec(defs, body);
                let mut inner = self.bind_letrec(f, &group, scope)?;
                self.compile_value(f, inner_body, &mut inner)
            }
            Expr::Do(first, then) => {
                let wm = self.next_slot.get();
                self.compile_value(f, first, scope)?;
                self.next_slot.set(wm);
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
                if let Some(nf) = native_fn(module, name, args.len()) {
                    // external native module: lower to a direct call to the
                    // package's linked symbol (ctx, args...) -> term
                    let callee = self.rt_fn(&nf.symbol, || self.c_fn_type(args.len()));
                    let argv = self.eval_args(f, args, scope)?;
                    let call = self
                        .builder
                        .build_call(callee, &argv, "native")
                        .map_err(be)?;
                    let v = call_result(call)?.into_int_value();
                    if nf.may_raise {
                        self.check_exc(f, v)
                    } else {
                        Ok(v)
                    }
                } else if is_bif_module(module) {
                    self.compile_bif(f, module, name, args, scope)
                } else if self.missing_modules.borrow().contains(module) {
                    self.emit_missing_call_abort(f, module, name, args.len())
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
                    let call = self.call_compiled(callee, &argv, "call", false)?;
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
            Expr::CallDyn { module, name, args } => {
                let mut children: Vec<&Expr> = vec![module.as_ref(), name.as_ref()];
                children.extend(args.iter());
                let rooted = self.eval_all_rooted(f, &children, scope)?;
                let list = self.build_list_from_rooted(&rooted[2..])?;
                let m = self.rooted_get(&rooted[0])?;
                let fa = self.rooted_get(&rooted[1])?;
                let call = self
                    .builder
                    .build_call(
                        self.rt_fn("mana_rt_apply3", || {
                            self.i64t.fn_type(
                                &[
                                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                ],
                                false,
                            )
                        }),
                        &[self.ctx_val().into(), m.into(), fa.into(), list.into()],
                        "dyncall",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            // stacktraces are not built — TODO(stacktraces); the raw
            // stacktrace argument was evaluated as part of the try lowering
            Expr::PrimOp { name, .. } if name == "build_stacktrace" => Ok(self.nil()),
            // re-raise with dynamic class + raw stacktrace (dropped)
            Expr::PrimOp { name, args } if name == "raw_raise" && args.len() == 3 => {
                let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
                let ctx = self.ctx_val();
                self.mem_store(ctx, CTX_EXC_CLASS, argv[0], MemKind::Ctx)?;
                self.mem_store(ctx, CTX_EXC_REASON, argv[1], MemKind::Ctx)?;
                let target = self.unwind_target(f)?;
                self.builder.build_unconditional_branch(target).map_err(be)?;
                let dead = self.ctx.append_basic_block(f, "rawraise.dead");
                self.builder.position_at_end(dead);
                Ok(self.i64t.get_undef())
            }
            // the writable-binary accumulator seed for <<acc/binary, ...>>
            // append loops (Base.decode64 etc.); the arg is only a capacity
            // hint and our binary construction copies on append, so an
            // empty static binary is semantically exact
            Expr::PrimOp { name, .. } if name == "bs_init_writable" => {
                self.static_binary(&[])
            }
            Expr::PrimOp { name, .. } => Err(format!("unsupported primop {}", name)),
            Expr::Case { arg, clauses } => {
                let vals = self.compile_case_arg(f, arg, clauses, scope)?;
                let merge = self.ctx.append_basic_block(f, "case.merge");
                let mut incoming: Vec<(Vec<IntValue<'ctx>>, BasicBlock<'ctx>)> = Vec::new();
                self.compile_case(f, &vals, clauses, scope, Some((merge, &mut incoming, 1)))?;
                self.builder.position_at_end(merge);
                let phi = self.builder.build_phi(self.i64t, "case.val").map_err(be)?;
                for (v, bb) in &incoming {
                    phi.add_incoming(&[(&v[0], *bb)]);
                }
                Ok(phi.as_basic_value().into_int_value())
            }
            Expr::Values(_) => Err("multi-value expression outside let/case".into()),
            Expr::Binary(segs) => self.compile_binary_construct(f, segs, scope),
            Expr::Map { pairs, update } => {
                match update {
                    None => {
                        // all-literal immediate keys (the struct/record case):
                        // term order is known at compile time — emit the map
                        // already sorted/deduped and skip mana_rt_map_norm.
                        // Values still evaluate in source order (effects).
                        let lit_keys: Option<Vec<&Literal>> = pairs
                            .iter()
                            .map(|(k, _, _)| match k {
                                Expr::Lit(
                                    l @ (Literal::Int(_) | Literal::Atom(_) | Literal::Nil),
                                ) => Some(l),
                                _ => None,
                            })
                            .collect();
                        if let Some(keys) = lit_keys {
                            let mut sorted: Vec<&Literal> = keys.clone();
                            sorted.sort_by(|a, b| lit_key_ord(a, b));
                            sorted.dedup();
                            let m2 = sorted.len();
                            let children: Vec<&Expr> =
                                pairs.iter().map(|(_, _, v)| v).collect();
                            let slots = self.eval_all_rooted(f, &children, scope)?;
                            let p = self.alloc_words(1 + 2 * m2 as u64)?;
                            let header =
                                self.i64t.const_int(((m2 as u64) << 8) | KIND_MAP, false);
                            self.store_word(p, 0, header)?;
                            for (i, l) in sorted.iter().enumerate() {
                                let k = self.compile_literal(l)?;
                                self.store_word(p, 1 + i as u64, k)?;
                            }
                            // original order: a duplicate key's later value
                            // overwrites the earlier store (last write wins)
                            for (i, l) in keys.iter().enumerate() {
                                let at = sorted
                                    .binary_search_by(|s| lit_key_ord(s, l))
                                    .expect("literal key in sorted set");
                                let v = self.rooted_get(&slots[i])?;
                                self.store_word(p, 1 + (m2 + at) as u64, v)?;
                            }
                            let raw = self
                                .builder
                                .build_ptr_to_int(p, self.i64t, "map.raw")
                                .map_err(be)?;
                            return Ok(raw);
                        }
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
                            let wm = self.next_slot.get();
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
                            self.next_slot.set(wm);
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
    pub(crate) fn eval_siblings(
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
        // spill slots die once reloaded below — release them for reuse
        let wm = self.next_slot.get();
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
        }        let out = held
            .into_iter()
            .map(|h| match h {
                Held::Val(v) => Ok(v),
                Held::Slot(s) => self.reload(s),
            })
            .collect();
        self.next_slot.set(wm);
        out
    }

    /// Evaluate and root every expression (used when the consumer itself is
    /// an allocation). In frameless functions this can only be reached in
    /// eternal-alloc (raise) mode, where allocation never collects — values
    /// stay in SSA.
    pub(crate) fn eval_all_rooted(
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

    pub(crate) fn rooted_get(&self, r: &Rooted<'ctx>) -> CgResult<IntValue<'ctx>> {
        match r {
            Rooted::Slot(idx) => self.reload(*idx),
            Rooted::Val(v) => Ok(*v),
        }
    }

    /// Arguments for a call: ctx first, then sibling-rule values.
    pub(crate) fn eval_args(
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
}
