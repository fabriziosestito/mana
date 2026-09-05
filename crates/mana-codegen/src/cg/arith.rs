use crate::*;

impl<'ctx, 'p> Cg<'ctx, 'p> {
    pub(crate) fn bool_term(&self, cond: IntValue<'ctx>) -> CgResult<IntValue<'ctx>> {
        let t = self.atom_term("true")?;
        let fa = self.atom_term("false")?;
        Ok(self
            .builder
            .build_select(cond, t, fa, "bool")
            .map_err(be)?
            .into_int_value())
    }

    /// Returns an i1 that is true when `a` is a small int. If `b` is given,
    /// the i1 is true only when both are small ints.
    pub(crate) fn small_test(
        &self,
        a: IntValue<'ctx>,
        b: Option<IntValue<'ctx>>,
    ) -> CgResult<IntValue<'ctx>> {
        let tag_of = |v: IntValue<'ctx>, n: &str| -> CgResult<IntValue<'ctx>> {
            let t = self
                .builder
                .build_and(v, self.i64t.const_int(TAG_MASK, false), n)
                .map_err(be)?;
            self.builder
                .build_int_compare(
                    IntPredicate::EQ,
                    t,
                    self.i64t.const_int(TAG_SMALL, false),
                    n,
                )
                .map_err(be)
        };
        match b {
            None => tag_of(a, "sm.a"),
            Some(b) => {
                // ((a^1) | (b^1)) & 7 == 0 holds exactly when both tags are 001.
                let xa = self
                    .builder
                    .build_xor(a, self.i64t.const_int(TAG_SMALL, false), "sm.xa")
                    .map_err(be)?;
                let xb = self
                    .builder
                    .build_xor(b, self.i64t.const_int(TAG_SMALL, false), "sm.xb")
                    .map_err(be)?;
                let or = self.builder.build_or(xa, xb, "sm.or").map_err(be)?;
                let m = self
                    .builder
                    .build_and(or, self.i64t.const_int(TAG_MASK, false), "sm.m")
                    .map_err(be)?;
                self.builder
                    .build_int_compare(IntPredicate::EQ, m, self.i64t.const_zero(), "sm.ok")
                    .map_err(be)
            }
        }
    }

    /// Numeric op with an inline path for two small ints and the mana_rt_arith
    /// slow path (floats, badarith). The slow path can raise. It never runs a GC.
    pub(crate) fn arith_fastslow(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        opcode: u64,
        a: IntValue<'ctx>,
        b: Option<IntValue<'ctx>>,
    ) -> CgResult<IntValue<'ctx>> {
        let both = self.small_test(a, b)?;
        let fast = self.ctx.append_basic_block(f, "ar.fast");
        let slow = self.ctx.append_basic_block(f, "ar.slow");
        let merge = self.ctx.append_basic_block(f, "ar.merge");
        self.builder
            .build_conditional_branch(both, fast, slow)
            .map_err(be)?;

        self.builder.position_at_end(fast);
        // Small results that leave the 61-bit range go to the slow path for
        // bignum promotion. The +, -, and * cases use overflow intrinsics on
        // tagged values. Because tagged(x) = 8x+1, a + (b-1) and a - (b-1) are
        // tagged sums. Their i64 overflow flag fires exactly when the true
        // result leaves the small range. Untagged 61-bit values can never
        // overflow an i64 intrinsic.
        let to_slow = |cond: IntValue<'ctx>, tag: &str| -> CgResult<()> {
            let cont = self.ctx.append_basic_block(f, tag);
            self.builder
                .build_conditional_branch(cond, slow, cont)
                .map_err(be)?;
            self.builder.position_at_end(cont);
            Ok(())
        };
        let ovf = |l: IntValue<'ctx>,
                   r: IntValue<'ctx>,
                   which: &str|
         -> CgResult<(IntValue<'ctx>, IntValue<'ctx>)> {
            let intr = inkwell::intrinsics::Intrinsic::find(which)
                .ok_or_else(|| format!("missing intrinsic {}", which))?;
            let decl = intr
                .get_declaration(&self.module, &[self.i64t.into()])
                .ok_or("intrinsic declaration")?;
            let call = self
                .builder
                .build_call(decl, &[l.into(), r.into()], "ovf")
                .map_err(be)?;
            let sv = call_result(call)?.into_struct_value();
            let v = self
                .builder
                .build_extract_value(sv, 0, "ovf.v")
                .map_err(be)?
                .into_int_value();
            let o = self
                .builder
                .build_extract_value(sv, 1, "ovf.o")
                .map_err(be)?
                .into_int_value();
            Ok((v, o))
        };
        let small_range_ok = |v: IntValue<'ctx>| -> CgResult<IntValue<'ctx>> {
            // (v << 3) >> 3 == v holds exactly when v fits the 61-bit small range.
            let sh = self
                .builder
                .build_left_shift(v, self.i64t.const_int(3, false), "rng.l")
                .map_err(be)?;
            let back = self
                .builder
                .build_right_shift(sh, self.i64t.const_int(3, false), true, "rng.r")
                .map_err(be)?;
            self.builder
                .build_int_compare(IntPredicate::NE, back, v, "rng.bad")
                .map_err(be)
        };
        let fastv = match (name, b) {
            ("+", Some(b)) => {
                let b1 = self
                    .builder
                    .build_int_sub(b, self.i64t.const_int(1, false), "add.b")
                    .map_err(be)?;
                let (v, o) = ovf(a, b1, "llvm.sadd.with.overflow")?;
                to_slow(o, "add.k")?;
                v // The sum is already tagged.
            }
            ("-", Some(b)) => {
                let b1 = self
                    .builder
                    .build_int_sub(b, self.i64t.const_int(1, false), "sub.b")
                    .map_err(be)?;
                let (v, o) = ovf(a, b1, "llvm.ssub.with.overflow")?;
                to_slow(o, "sub.k")?;
                v // The difference is already tagged.
            }
            ("*", Some(b)) => {
                let ua = self.untag_int(a)?;
                let b8 = self
                    .builder
                    .build_xor(b, self.i64t.const_int(1, false), "mul.b")
                    .map_err(be)?;
                let (v, o) = ovf(ua, b8, "llvm.smul.with.overflow")?;
                to_slow(o, "mul.k")?;
                self.builder
                    .build_or(v, self.i64t.const_int(1, false), "mul.t")
                    .map_err(be)?
            }
            ("div", Some(b)) => {
                let ua = self.untag_int(a)?;
                let ub = self.untag_int(b)?;
                let zero = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, ub, self.i64t.const_zero(), "div.z")
                    .map_err(be)?;
                to_slow(zero, "div.k")?;
                let q = self
                    .builder
                    .build_int_signed_div(ua, ub, "div")
                    .map_err(be)?;
                // -2^60 div -1 leaves the small range.
                let bad = small_range_ok(q)?;
                to_slow(bad, "div.k2")?;
                self.retag_int(q)?
            }
            ("rem", Some(b)) => {
                let ua = self.untag_int(a)?;
                let ub = self.untag_int(b)?;
                let zero = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, ub, self.i64t.const_zero(), "rem.z")
                    .map_err(be)?;
                to_slow(zero, "rem.k")?;
                let r = self
                    .builder
                    .build_int_signed_rem(ua, ub, "rem")
                    .map_err(be)?;
                self.retag_int(r)?
            }
            ("band", Some(b)) => {
                let (ua, ub) = (self.untag_int(a)?, self.untag_int(b)?);
                let v = self.builder.build_and(ua, ub, "band").map_err(be)?;
                self.retag_int(v)?
            }
            ("bor", Some(b)) => {
                let (ua, ub) = (self.untag_int(a)?, self.untag_int(b)?);
                let v = self.builder.build_or(ua, ub, "bor").map_err(be)?;
                self.retag_int(v)?
            }
            ("bxor", Some(b)) => {
                let (ua, ub) = (self.untag_int(a)?, self.untag_int(b)?);
                let v = self.builder.build_xor(ua, ub, "bxor").map_err(be)?;
                self.retag_int(v)?
            }
            ("bnot", None) => {
                let ua = self.untag_int(a)?;
                let v = self
                    .builder
                    .build_xor(ua, self.i64t.const_all_ones(), "bnot")
                    .map_err(be)?;
                self.retag_int(v)?
            }
            ("neg", None) => {
                let ua = self.untag_int(a)?;
                let v = self
                    .builder
                    .build_int_sub(self.i64t.const_zero(), ua, "neg")
                    .map_err(be)?;
                let bad = small_range_ok(v)?; // -(-2^60) leaves the small range.
                to_slow(bad, "neg.k")?;
                self.retag_int(v)?
            }
            ("abs", None) => {
                let ua = self.untag_int(a)?;
                let neg = self
                    .builder
                    .build_int_compare(IntPredicate::SLT, ua, self.i64t.const_zero(), "abs.n")
                    .map_err(be)?;
                let nv = self
                    .builder
                    .build_int_sub(self.i64t.const_zero(), ua, "abs.neg")
                    .map_err(be)?;
                let v = self
                    .builder
                    .build_select(neg, nv, ua, "abs")
                    .map_err(be)?
                    .into_int_value();
                let bad = small_range_ok(v)?; // abs(-2^60) leaves the small range.
                to_slow(bad, "abs.k")?;
                self.retag_int(v)?
            }
            _ => return Err(format!("arith_fastslow: bad op {}", name)),
        };
        let fast_end = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(merge).map_err(be)?;

        self.builder.position_at_end(slow);
        let bb = b.unwrap_or(self.i64t.const_int(1, false)); // For unary ops, the second argument is the small 0.
        let call = self
            .builder
            .build_call(
                self.rt_arith(),
                &[
                    self.ctx_val().into(),
                    self.i64t.const_int(opcode, false).into(),
                    a.into(),
                    bb.into(),
                ],
                "ar",
            )
            .map_err(be)?;
        let sv = call_result(call)?.into_int_value();
        let sv = self.check_exc(f, sv)?;
        let slow_end = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(merge).map_err(be)?;

        self.builder.position_at_end(merge);
        let phi = self.builder.build_phi(self.i64t, "ar.v").map_err(be)?;
        phi.add_incoming(&[(&fastv, fast_end), (&sv, slow_end)]);
        Ok(phi.as_basic_value().into_int_value())
    }

    /// Byte-data base address of a bin-kind subject (KIND_BIN or a
    /// KIND_SUBBIN view). The caller must already preflight the subject as a
    /// bin kind. Bit 3 of the header distinguishes 5 from 13. The function emits
    /// pure loads. Callers must recompute after any GC point, because the parent
    /// moves.
    pub(crate) fn bin_base_addr(
        &self,
        f: FunctionValue<'ctx>,
        subject: IntValue<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let (parent, poff) = self.bin_parent_off(f, subject)?;
        let pdata = self
            .builder
            .build_int_add(parent, self.i64t.const_int(8, false), "bba.pd")
            .map_err(be)?;
        self.builder
            .build_int_add(pdata, poff, "bba.base")
            .map_err(be)
    }

    /// Returns (root binary term, byte offset into it) for a preflighted binary
    /// subject. For a plain KIND_BIN, the result is the subject with offset 0.
    /// For a KIND_SUBBIN, the result is the parent of the view and the stored
    /// offset. The code branches inline on the view bit. Kinds 5 and 13 differ
    /// only in bit 3.
    pub(crate) fn bin_parent_off(
        &self,
        f: FunctionValue<'ctx>,
        subject: IntValue<'ctx>,
    ) -> CgResult<(IntValue<'ctx>, IntValue<'ctx>)> {
        let sp = self
            .builder
            .build_int_to_ptr(subject, self.ptrt, "bba.p")
            .map_err(be)?;
        let header = self
            .builder
            .build_load(self.i64t, sp, "bba.h")
            .map_err(be)?
            .into_int_value();
        let viewbit = self
            .builder
            .build_and(header, self.i64t.const_int(8, false), "bba.vb")
            .map_err(be)?;
        let is_view = self
            .builder
            .build_int_compare(IntPredicate::NE, viewbit, self.i64t.const_zero(), "bba.iv")
            .map_err(be)?;
        let cur = self.builder.get_insert_block().unwrap();
        let view_bb = self.ctx.append_basic_block(f, "bba.view");
        let merge = self.ctx.append_basic_block(f, "bba.merge");
        self.builder
            .build_conditional_branch(is_view, view_bb, merge)
            .map_err(be)?;
        self.builder.position_at_end(view_bb);
        let parent_gep = unsafe {
            self.builder
                .build_in_bounds_gep(self.i64t, sp, &[self.i64t.const_int(1, false)], "bba.pg")
                .map_err(be)?
        };
        let parent = self
            .builder
            .build_load(self.i64t, parent_gep, "bba.parent")
            .map_err(be)?
            .into_int_value();
        let off_gep = unsafe {
            self.builder
                .build_in_bounds_gep(self.i64t, sp, &[self.i64t.const_int(2, false)], "bba.og")
                .map_err(be)?
        };
        let poff = self
            .builder
            .build_load(self.i64t, off_gep, "bba.off")
            .map_err(be)?
            .into_int_value();
        let view_end = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(merge).map_err(be)?;
        self.builder.position_at_end(merge);
        let pphi = self
            .builder
            .build_phi(self.i64t, "bba.parent")
            .map_err(be)?;
        pphi.add_incoming(&[(&subject, cur), (&parent, view_end)]);
        let ophi = self.builder.build_phi(self.i64t, "bba.poff").map_err(be)?;
        let zero = self.i64t.const_zero();
        ophi.add_incoming(&[(&zero, cur), (&poff, view_end)]);
        Ok((
            pphi.as_basic_value().into_int_value(),
            ophi.as_basic_value().into_int_value(),
        ))
    }

    /// Computes `boxed(v) && header.kind == kind` as an i1, via control flow.
    /// The `test` closure computes the header part of the condition.
    pub(crate) fn kind_test(
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
        let okptr = self
            .builder
            .build_and(is_boxed, nonzero, "kt.ptr")
            .map_err(be)?;
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
}
