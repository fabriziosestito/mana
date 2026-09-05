use crate::*;

impl<'ctx, 'p> Cg<'ctx, 'p> {
    pub(crate) fn compile_literal(&self, l: &Literal) -> CgResult<IntValue<'ctx>> {
        match l {
            Literal::Int(n) => Ok(self.small_int(*n)),
            Literal::Big(d) => {
                // An inert interned big-literal term. It orders, compares, and
                // prints correctly. Arithmetic on it is badarith at runtime
                // (TODO(bignum)). The pow10 tables and the >= guards of Decimal work.
                let ptr = self.static_bytes(d.as_bytes())?;
                let callee = self.rt_fn("mana_rt_big_literal", || {
                    self.i64t.fn_type(
                        &[
                            BasicMetadataTypeEnum::PointerType(self.ptrt),
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
                            ptr.into(),
                            self.i64t.const_int(d.len() as u64, false).into(),
                        ],
                        "biglit",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
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

    pub(crate) fn bind_let(
        &self,
        f: FunctionValue<'ctx>,
        vars: &[String],
        arg: &Expr,
        scope: &mut Scope<'ctx>,
    ) -> CgResult<()> {
        // Statement boundary. The temps that are rooted during the evaluation
        // of `arg` are dead when the values sit in the let-bound var slots.
        let wm = self.next_slot.get();
        let r = self.bind_let_inner(f, vars, arg, scope);
        self.next_slot.set(wm);
        r
    }

    pub(crate) fn bind_let_inner(
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
            (_, Expr::Case { arg: carg, clauses }) => {
                let vs = self.compile_case_values(f, carg, clauses, scope, vars.len())?;
                for (var, v) in vars.iter().zip(vs) {
                    self.bind_var(scope, var, v)?;
                }
                Ok(())
            }
            (_, Expr::Let { vars: iv, arg: ia, body }) => {
                self.bind_let(f, iv, ia, scope)?;
                self.bind_let(f, vars, body, scope)
            }
            (_, Expr::Do(a, b)) => {
                let wm = self.next_slot.get();
                self.compile_value(f, a, scope)?;
                self.next_slot.set(wm);
                self.bind_let(f, vars, b, scope)
            }
            _ => Err("multi-value let from a non-values expression is not supported".into()),
        }
    }

    /// Case scrutinees. If a guard or a pattern contains a GC point, each
    /// clause must reload the values. Later clauses match again after the
    /// guard ran. In that case all values go to slots. Otherwise, the values
    /// are plain SSA siblings.
    pub(crate) fn compile_case_arg(
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
        let any_pat_gc = clauses
            .iter()
            .any(|c| c.patterns.iter().any(pattern_may_gc));
        if (any_guard_gc || any_pat_gc) && self.framed() {
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

    /// Case pre-dispatch. It takes the longest prefix of clauses whose first
    /// pattern has a static discriminant. A static discriminant is a small-int
    /// literal, a nil literal, or a binary that starts with a constant byte.
    /// An LLVM `switch` jumps to the FIRST clause that has the key of the
    /// subject. From there the clauses run in order, as without the switch.
    /// A subject with no matching key, or of another shape, goes to the first
    /// clause without a key, or to nomatch. This turns the generated
    /// 1400-clause byte tables of Elixir (String.Unicode) from O(n) prefix
    /// compares per byte into one jump.
    pub(crate) fn emit_case_dispatch(
        &self,
        f: FunctionValue<'ctx>,
        vals: &CaseVals<'ctx>,
        clauses: &[Clause],
        blocks: &[BasicBlock<'ctx>],
        fail_bb: BasicBlock<'ctx>,
    ) -> CgResult<()> {
        let mut keys: Vec<DiscKey> = Vec::new();
        for c in clauses {
            match c.patterns.first().and_then(Self::clause_disc) {
                Some(k) => keys.push(k),
                None => break,
            }
        }
        // The switch needs one discriminant CLASS over the whole prefix.
        let all_word = keys.iter().all(|k| matches!(k, DiscKey::Word(_)));
        let all_byte = keys.iter().all(|k| matches!(k, DiscKey::Byte0(_)));
        if keys.len() < 4 || !(all_word || all_byte) {
            self.builder.build_unconditional_branch(blocks[0]).map_err(be)?;
            return Ok(());
        }
        let default_bb = if keys.len() < clauses.len() { blocks[keys.len()] } else { fail_bb };
        let subject = match vals {
            CaseVals::Ssa(vs) => vs[0],
            CaseVals::Slots(slots) => self.reload(slots[0])?,
        };
        // One arm per distinct key. The first clause with that key wins.
        let mut seen: HashSet<DiscKey> = HashSet::new();
        let mut arms: Vec<(IntValue<'ctx>, BasicBlock<'ctx>)> = Vec::new();
        for (i, k) in keys.iter().enumerate() {
            if seen.insert(*k) {
                let c = match k {
                    DiscKey::Word(w) => self.i64t.const_int(*w, false),
                    DiscKey::Byte0(b) => self.i64t.const_int(*b as u64, false),
                };
                arms.push((c, blocks[i]));
            }
        }
        let disc = if all_word {
            subject
        } else {
            // For a binary subject with len >= 1, the discriminant is its first
            // byte. For any other subject, it is the impossible key 256, which
            // goes to default.
            let miss_bb = self.ctx.append_basic_block(f, "disp.miss");
            let bin_bb = self.ctx.append_basic_block(f, "disp.bin");
            let merge = self.ctx.append_basic_block(f, "disp.merge");
            let ok = self.kind_test(f, subject, |s, header| {
                let k = s.builder.build_and(header, s.i64t.const_int(0xff, false), "dp.k").map_err(be)?;
                let k2 = s.builder.build_or(k, s.i64t.const_int(8, false), "dp.k2").map_err(be)?;
                let is_bin = s
                    .builder
                    .build_int_compare(IntPredicate::EQ, k2, s.i64t.const_int(13, false), "dp.bin")
                    .map_err(be)?;
                let len = s
                    .builder
                    .build_right_shift(header, s.i64t.const_int(8, false), false, "dp.len")
                    .map_err(be)?;
                let nonempty = s
                    .builder
                    .build_int_compare(IntPredicate::UGE, len, s.i64t.const_int(1, false), "dp.ne")
                    .map_err(be)?;
                s.builder.build_and(is_bin, nonempty, "dp.ok").map_err(be)
            })?;
            let entry_end = self.builder.get_insert_block().unwrap();
            self.builder.build_conditional_branch(ok, bin_bb, miss_bb).map_err(be)?;
            self.builder.position_at_end(bin_bb);
            let base = self.bin_base_addr(f, subject)?;
            let bp = self.builder.build_int_to_ptr(base, self.ptrt, "dp.p").map_err(be)?;
            let b = self
                .builder
                .build_load(self.ctx.i8_type(), bp, "dp.b0")
                .map_err(be)?
                .into_int_value();
            let b64 = self.builder.build_int_z_extend(b, self.i64t, "dp.b64").map_err(be)?;
            let bin_end = self.builder.get_insert_block().unwrap();
            self.builder.build_unconditional_branch(merge).map_err(be)?;
            self.builder.position_at_end(miss_bb);
            let miss = self.i64t.const_int(256, false);
            self.builder.build_unconditional_branch(merge).map_err(be)?;
            self.builder.position_at_end(merge);
            let phi = self.builder.build_phi(self.i64t, "dp.disc").map_err(be)?;
            phi.add_incoming(&[(&b64, bin_end), (&miss, miss_bb)]);
            let _ = entry_end;
            phi.as_basic_value().into_int_value()
        };
        self.builder.build_switch(disc, default_bb, &arms).map_err(be)?;
        Ok(())
    }

    /// The static discriminant of the FIRST pattern of a clause, for the case
    /// pre-dispatch switch. For a small-int or nil literal, the key is the
    /// whole term word. For a binary pattern that starts with a constant
    /// byte-sized integer segment, the key is the first byte. None means that
    /// this clause can match any subject (variable, atom, tuple, alias, and
    /// more). Such a clause ends the switchable prefix. The switch skips only
    /// `Some` clauses, and only when the key of the subject is known to
    /// differ. As a result, the order, the guards, and the fallthrough
    /// semantics do not change.
    pub(crate) fn clause_disc(p: &Pattern) -> Option<DiscKey> {
        match p {
            Pattern::Lit(Literal::Int(n)) if (-(1i64 << 60)..(1i64 << 60)).contains(n) => {
                Some(DiscKey::Word(((*n as u64) << 3) | TAG_SMALL))
            }
            Pattern::Lit(Literal::Nil) => Some(DiscKey::Word(NIL)),
            Pattern::Binary(segs) => {
                let first = segs.first()?;
                let spec = parse_seg_spec(&first.spec).ok()?;
                match (&*first.value, spec.kind) {
                    (Pattern::Lit(l @ (Literal::Int(_) | Literal::Big(_))), SegKind::Int { size: SegSize::Bytes(n) })
                        if n >= 1 =>
                    {
                        let bytes = seg_const_bytes(&Expr::Lit(l.clone()), n, spec.little).ok()??;
                        Some(DiscKey::Byte0(bytes[0]))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    pub(crate) fn compile_case(
        &self,
        f: FunctionValue<'ctx>,
        vals: &CaseVals<'ctx>,
        clauses: &[Clause],
        scope: &Scope<'ctx>,
        mut merge: Option<(
            BasicBlock<'ctx>,
            &mut Vec<(Vec<IntValue<'ctx>>, BasicBlock<'ctx>)>,
            usize,
        )>,
    ) -> CgResult<()> {
        let fail_bb = self.ctx.append_basic_block(f, "case.nomatch");
        let blocks: Vec<BasicBlock<'ctx>> = (0..clauses.len())
            .map(|i| self.ctx.append_basic_block(f, &format!("clause{}", i)))
            .collect();
        self.emit_case_dispatch(f, vals, clauses, &blocks, fail_bb)?;

        // Clauses are mutually exclusive at runtime. Each attempt can reuse
        // the temp slots of the previous attempt. The subject slots sit below wm.
        let wm = self.next_slot.get();
        for (i, clause) in clauses.iter().enumerate() {
            self.next_slot.set(wm);
            self.builder.position_at_end(blocks[i]);
            let next = if i + 1 < clauses.len() { blocks[i + 1] } else { fail_bb };
            let nvals = match vals {
                CaseVals::Ssa(vs) => vs.len(),
                CaseVals::Slots(slots) => slots.len(),
            };
            if clause.patterns.len() != nvals {
                return Err(format!(
                    "clause has {} patterns but case argument has {} values",
                    clause.patterns.len(),
                    nvals
                ));
            }
            let mut cscope = scope.clone();
            for (i, p) in clause.patterns.iter().enumerate() {
                // Reload late. A binary pattern earlier in this clause can
                // allocate. That allocation invalidates the SSA copies of
                // later subjects.
                let v = match vals {
                    CaseVals::Ssa(vs) => vs[i],
                    CaseVals::Slots(slots) => self.reload(slots[i])?,
                };
                self.match_pattern(f, v, p, &mut cscope, next)?;
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
                Some((merge_bb, ref mut incoming, nvals)) => {
                    let vs =
                        self.compile_body_values(f, &clause.body, &mut cscope, nvals)?;
                    let cur = self.builder.get_insert_block().unwrap();
                    incoming.push((vs, cur));
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

    /// A clause body that produces `nvals` values. These are the Core Erlang
    /// `<a, b>` bodies under multi-value lets. For nvals == 1, the body can
    /// be any expression. For more values, the body must be Values, or a Let,
    /// Do, or Case wrapper around Values.
    pub(crate) fn compile_body_values(
        &self,
        f: FunctionValue<'ctx>,
        body: &Expr,
        scope: &mut Scope<'ctx>,
        nvals: usize,
    ) -> CgResult<Vec<IntValue<'ctx>>> {
        if nvals == 1 {
            return Ok(vec![self.compile_value(f, body, scope)?]);
        }
        match body {
            Expr::Values(es) if es.len() == nvals => es
                .iter()
                .map(|e| self.compile_value(f, e, scope))
                .collect(),
            Expr::Let { vars, arg, body } => {
                self.bind_let(f, vars, arg, scope)?;
                self.compile_body_values(f, body, scope, nvals)
            }
            Expr::Do(a, b) => {
                let wm = self.next_slot.get();
                self.compile_value(f, a, scope)?;
                self.next_slot.set(wm);
                self.compile_body_values(f, b, scope, nvals)
            }
            Expr::Case { arg, clauses } => {
                Ok(self.compile_case_values(f, arg, clauses, scope, nvals)?)
            }
            // A body that raises produces no values. The phi inputs are dead.
            Expr::PrimOp { name, args } if is_raise(name) => {
                self.compile_raise(f, name, args, scope)?;
                Ok(vec![self.i64t.get_undef(); nvals])
            }
            Expr::Call { module, name, args }
                if module == "erlang"
                    && matches!(
                        (name.as_str(), args.len()),
                        ("error", 1) | ("error", 2) | ("error", 3) | ("exit", 1)
                            | ("throw", 1)
                    ) =>
            {
                self.compile_raise(f, name, &args[..1.max(args.len().min(2))], scope)?;
                Ok(vec![self.i64t.get_undef(); nvals])
            }
            other => Err(format!(
                "multi-value body shape not supported ({} values): {:.60?}",
                nvals, other
            )),
        }
    }

    /// A case in value position. It yields `nvals` values through N phis.
    pub(crate) fn compile_case_values(
        &self,
        f: FunctionValue<'ctx>,
        arg: &Expr,
        clauses: &[Clause],
        scope: &mut Scope<'ctx>,
        nvals: usize,
    ) -> CgResult<Vec<IntValue<'ctx>>> {
        let vals = self.compile_case_arg(f, arg, clauses, scope)?;
        let merge = self.ctx.append_basic_block(f, "mcase.merge");
        let mut incoming: Vec<(Vec<IntValue<'ctx>>, BasicBlock<'ctx>)> = Vec::new();
        self.compile_case(f, &vals, clauses, scope, Some((merge, &mut incoming, nvals)))?;
        self.builder.position_at_end(merge);
        let mut out = Vec::with_capacity(nvals);
        for i in 0..nvals {
            let phi = self
                .builder
                .build_phi(self.i64t, &format!("mcase.v{}", i))
                .map_err(be)?;
            for (vs, bb) in &incoming {
                phi.add_incoming(&[(&vs[i], *bb)]);
            }
            out.push(phi.as_basic_value().into_int_value());
        }
        Ok(out)
    }
}
