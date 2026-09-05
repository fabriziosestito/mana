//! GC root frames and slots. A framed function keeps its live terms in an
//! alloca `[prev | len | slots...]` and links it into `CTX_ROOTS` at entry.
//! A prepass over the body decides the frame size. The function must unlink
//! the frame before every return or tail call. A slot that holds 0 is
//! empty, and the collector skips it.

use crate::*;

/// Returns true if a match of this pattern can allocate. A binary pattern
/// with binary-type segments builds sub-binaries.
pub(crate) fn pattern_may_gc(p: &Pattern) -> bool {
    match p {
        Pattern::Binary(segs) => segs
            .iter()
            .any(|s| matches!(parse_seg_spec(&s.spec), Ok(sp) if sp.kind.allocates())),
        Pattern::Alias(_, inner) => pattern_may_gc(inner),
        Pattern::Tuple(ps) => ps.iter().any(pattern_may_gc),
        Pattern::Cons(h, t) => pattern_may_gc(h) || pattern_may_gc(t),
        Pattern::Map(pairs) => pairs.iter().any(|(_, sub)| pattern_may_gc(sub)),
        _ => false,
    }
}

/// Count the frame slots that the match compiler will spill for this
/// pattern. The subjects are parked across sub-matches that allocate.
/// See pattern_subject_slot.
pub(crate) fn pattern_spill_sites(p: &Pattern) -> usize {
    let own = pattern_may_gc(p) as usize;
    own + match p {
        Pattern::Alias(_, inner) => pattern_spill_sites(inner),
        Pattern::Tuple(ps) => ps.iter().map(pattern_spill_sites).sum(),
        Pattern::Cons(h, t) => pattern_spill_sites(h) + pattern_spill_sites(t),
        Pattern::Map(pairs) => pairs.iter().map(|(_, s)| pattern_spill_sites(s)).sum(),
        _ => 0,
    }
}

/// Count the bound variable names and the *spill sites* for frame sizing.
/// Spills happen only at these sites:
/// - children of allocations (eval_all_rooted)
/// - call and BIF arguments (eval_siblings)
/// - case scrutinees
/// - letrec closures
///
/// The sum over those sites bounds any execution path. The prepass does not
/// descend into Fun or LetRec definition bodies. Those bodies get their own
/// frames when they are lifted.
pub(crate) fn frame_prepass(e: &Expr, vars: &mut BTreeSet<String>, nodes: &mut usize) {
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
            *nodes += 1; // the shared closure slot
            frame_prepass(body, vars, nodes);
        }
        Expr::Apply { args, .. } => {
            *nodes += args.len();
            args.iter().for_each(|a| frame_prepass(a, vars, nodes))
        }
        Expr::CallDyn { module, name, args } => {
            *nodes += args.len() + 2;
            frame_prepass(module, vars, nodes);
            frame_prepass(name, vars, nodes);
            args.iter().for_each(|a| frame_prepass(a, vars, nodes));
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
                // Binary sub-patterns that allocate spill their subjects.
                c.patterns
                    .iter()
                    .for_each(|p| *nodes += pattern_spill_sites(p));
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

impl<'ctx, 'p> Cg<'ctx, 'p> {
    /// Set up the root frame for the function that owns the current insert
    /// block of the builder. `body` decides if the function is framed.
    /// `var_names` lists all names that can be bound: params, captures, and
    /// body binds.
    pub(crate) fn setup_frame(
        &self,
        body: &Expr,
        var_names: &[String],
        letrec_sibs: &[FunName],
    ) -> CgResult<()> {
        self.var_slots.borrow_mut().clear();
        self.frame_memset.set(None);
        self.frame_len_store.set(None);
        self.frame_skip.set(0);
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

        // var_names (params and captures) take the leading slots. Every caller
        // stores them right after this returns, before the first GC point.
        // Therefore the zeroing memset can skip them.
        let skip;
        {
            let mut slots = self.var_slots.borrow_mut();
            for v in var_names {
                if !slots.contains_key(v) {
                    let i = slots.len() as u64;
                    slots.insert(v.clone(), i);
                }
            }
            skip = slots.len() as u64;
            for v in vars.iter() {
                if !slots.contains_key(v.as_str()) {
                    let i = slots.len() as u64;
                    slots.insert(v.clone(), i);
                }
            }
        }
        self.next_slot.set(nvars);
        self.slot_cap.set(cap);
        self.peak_slot.set(nvars);
        self.frame_skip.set(skip);

        let frame_ty = self.i64t.array_type((cap + 2) as u32);
        let frame = self
            .builder
            .build_alloca(frame_ty, "gc.frame")
            .map_err(be)?;
        let ctx = self.ctx_val();
        let prev = self.mem_load(ctx, CTX_ROOTS, MemKind::Ctx)?;
        self.mem_store(frame, 0, prev, MemKind::Frame)?;
        // len is a placeholder. patch_frame lowers it to the slot high-water
        // mark after the body is compiled.
        let len_slot = unsafe {
            self.builder
                .build_in_bounds_gep(
                    self.i64t,
                    frame,
                    &[self.i64t.const_int(1, false)],
                    "len",
                )
                .map_err(be)?
        };
        let len_store = self
            .builder
            .build_store(len_slot, self.i64t.const_int(cap, false))
            .map_err(be)?;
        let _ = len_store.set_metadata(self.tbaa_frame, self.tbaa_kind);
        self.frame_len_store.set(Some(len_store));
        // One memset zeroes the slots that are not prebound. A 0 marks an
        // empty slot that the collector skips. This is cheaper than a NIL
        // store per slot. The size is a placeholder that patch_frame patches.
        let slots = unsafe {
            self.builder
                .build_in_bounds_gep(
                    self.i64t,
                    frame,
                    &[self.i64t.const_int(2 + skip, false)],
                    "slots",
                )
                .map_err(be)?
        };
        let ms = self
            .builder
            .build_memset(
                slots,
                8,
                self.ctx.i8_type().const_zero(),
                self.i64t.const_int((cap - skip) * 8, false),
            )
            .map_err(be)?;
        self.frame_memset.set(ms.as_instruction());
        let frame_int = self
            .builder
            .build_ptr_to_int(frame, self.i64t, "frame.addr")
            .map_err(be)?;
        self.mem_store(ctx, CTX_ROOTS, frame_int, MemKind::Ctx)?;
        self.cur_frame.set(Some(frame));
        Ok(())
    }

    /// Shrink the frame len and the entry memset to the true slot high-water
    /// mark. The mark is known after the body is compiled. The prepass cap
    /// is an over-approximation. The alloca keeps the padded size, because
    /// untouched stack costs nothing.
    pub(crate) fn patch_frame(&self) {
        let peak = self.peak_slot.get();
        if let Some(ls) = self.frame_len_store.take() {
            let ok = ls.set_operand(0, self.i64t.const_int(peak, false));
            debug_assert!(ok, "frame len store operand patch failed");
        }
        if let Some(ms) = self.frame_memset.take() {
            let skip = self.frame_skip.get();
            let ok = ms.set_operand(2, self.i64t.const_int((peak - skip) * 8, false));
            debug_assert!(ok, "frame memset size operand patch failed");
        }
    }

    /// Unlink the frame. Call this before any return or tail call.
    pub(crate) fn pop_frame(&self) -> CgResult<()> {
        if let Some(frame) = self.cur_frame.get() {
            let prev = self.mem_load(frame, 0, MemKind::Frame)?;
            self.mem_store(self.ctx_val(), CTX_ROOTS, prev, MemKind::Ctx)?;
        }
        Ok(())
    }

    pub(crate) fn emit_ret(&self, v: IntValue<'ctx>) -> CgResult<()> {
        self.pop_frame()?;
        self.builder.build_return(Some(&v)).map_err(be)?;
        Ok(())
    }

    /// Build an eternal (non-moving) 2-tuple for an exception reason.
    pub(crate) fn eternal_pair(
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

    pub(crate) fn slot_ptr(&self, idx: u64) -> CgResult<PointerValue<'ctx>> {
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

    pub(crate) fn alloc_temp(&self) -> u64 {
        let n = self.next_slot.get();
        assert!(n < self.slot_cap.get(), "frame slot capacity exceeded");
        self.next_slot.set(n + 1);
        if n + 1 > self.peak_slot.get() {
            self.peak_slot.set(n + 1);
        }
        n
    }

    pub(crate) fn spill(&self, v: IntValue<'ctx>) -> CgResult<u64> {
        let idx = self.alloc_temp();
        let p = self.slot_ptr(idx)?;
        let inst = self.builder.build_store(p, v).map_err(be)?;
        let _ = inst.set_metadata(self.tbaa_frame, self.tbaa_kind);
        Ok(idx)
    }

    pub(crate) fn reload(&self, idx: u64) -> CgResult<IntValue<'ctx>> {
        let p = self.slot_ptr(idx)?;
        let v = self.builder.build_load(self.i64t, p, "reload").map_err(be)?;
        if let Some(inst) = v.as_instruction_value() {
            let _ = inst.set_metadata(self.tbaa_frame, self.tbaa_kind);
        }
        Ok(v.into_int_value())
    }

    pub(crate) fn bind_var(&self, scope: &mut Scope<'ctx>, name: &str, v: IntValue<'ctx>) -> CgResult<()> {
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

    pub(crate) fn read_var(&self, scope: &Scope<'ctx>, name: &str) -> CgResult<IntValue<'ctx>> {
        match scope.vars.get(name) {
            Some(Binding::Reg(v)) => Ok(*v),
            Some(Binding::Slot(idx)) => self.reload(*idx),
            None => Err(format!("unbound variable {}", name)),
        }
    }
}
