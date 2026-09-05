use crate::*;

impl<'ctx, 'p> Cg<'ctx, 'p> {
    /// Emits tests for `pat` against `val`. On a mismatch, the code branches
    /// to `fail`.
    ///
    /// Patterns do not allocate, with one exception. Binary patterns with
    /// binary-type segments build sub-binaries, and these are GC points.
    /// Where a sub-pattern can allocate, the enclosing arm keeps its subject
    /// in a frame slot. It derives the pointers again after the sub-match.
    /// As a result, no stale SSA pointer is used across a collection. Effect
    /// analysis frames the functions that hold such patterns. Bound variables
    /// are already backed by slots.
    pub(crate) fn match_pattern(
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
            Pattern::Lit(l @ Literal::Big(_)) => {
                // Interned big-literal terms have pointer identity. But a
                // value that is equal under `==` can also arrive from another
                // intern site. The comparison must be exact.
                let expect = self.compile_literal(l)?;
                let call = self
                    .builder
                    .build_call(
                        self.rt_tt_i64("mana_rt_eq_exact"),
                        &[val.into(), expect.into()],
                        "bigpat",
                    )
                    .map_err(be)?;
                let e = call_result(call)?.into_int_value();
                let ok = self
                    .builder
                    .build_int_compare(IntPredicate::NE, e, self.i64t.const_zero(), "bigpat.ok")
                    .map_err(be)?;
                self.branch_test(f, ok, fail)
            }
            Pattern::Lit(Literal::Float(x)) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_tt_i64("mana_rt_float_pat"),
                        &[val.into(), self.i64t.const_int(x.to_bits(), false).into()],
                        "fpat",
                    )
                    .map_err(be)?;
                let ok = call_result(call)?.into_int_value();
                let ok = self
                    .builder
                    .build_int_compare(IntPredicate::NE, ok, self.i64t.const_zero(), "fpat.ok")
                    .map_err(be)?;
                self.branch_test(f, ok, fail)
            }
            Pattern::Binary(segs) => self.match_binary(f, val, segs, scope, fail),
            Pattern::Map(pairs) => {
                // A map pattern only matches maps. This also holds for the
                // empty `~{}~`, which requires no keys.
                let is_map = self.kind_test(f, val, |s, header| {
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
                self.branch_test(f, is_map, fail)?;
                let slot = self.pattern_subject_slot(pat, val)?;
                for (k, sub) in pairs {
                    let subject = match slot {
                        Some(s) => self.reload(s)?,
                        None => val,
                    };
                    // Immediate literal keys (atoms, small integers, nil) are
                    // equal only to bit-identical terms. The code scans the
                    // key words inline, with no runtime call.
                    let immediate_key = matches!(k, Expr::Lit(Literal::Atom(_) | Literal::Nil))
                        || matches!(k, Expr::Lit(Literal::Int(v)) if v.unsigned_abs() < (1 << 60));
                    let v = if immediate_key {
                        let key = self.compile_value(f, k, scope)?;
                        self.inline_map_get(f, subject, key, fail)?
                    } else {
                        let key = self.compile_value(f, k, scope)?;
                        let call = self
                            .builder
                            .build_call(
                                self.rt_tt_i64("mana_rt_map_pat_get"),
                                &[subject.into(), key.into()],
                                "mpat",
                            )
                            .map_err(be)?;
                        let v = call_result(call)?.into_int_value();
                        let hit = self
                            .builder
                            .build_int_compare(IntPredicate::NE, v, self.sentinel(), "mpat.h")
                            .map_err(be)?;
                        self.branch_test(f, hit, fail)?;
                        v
                    };
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
                    .build_int_compare(IntPredicate::EQ, tag, self.i64t.const_zero(), "is.boxed")
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
                let slot = self.pattern_subject_slot(pat, val)?;
                for (i, sub) in ps.iter().enumerate() {
                    let p = match slot {
                        Some(s) => {
                            let subject = self.reload(s)?;
                            self.builder
                                .build_int_to_ptr(subject, self.ptrt, "tuple.ptr")
                                .map_err(be)?
                        }
                        None => p,
                    };
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
                let slot = self.pattern_subject_slot(pat, val)?;
                let head = self.load_word(p, 0)?;
                self.match_pattern(f, head, h, scope, fail)?;
                let p = match slot {
                    Some(s) => {
                        let subject = self.reload(s)?;
                        let addr = self
                            .builder
                            .build_and(subject, self.i64t.const_int(!TAG_MASK, false), "cons.addr")
                            .map_err(be)?;
                        self.builder
                            .build_int_to_ptr(addr, self.ptrt, "cons.ptr")
                            .map_err(be)?
                    }
                    None => p,
                };
                let tail = self.load_word(p, 1)?;
                self.match_pattern(f, tail, t, scope, fail)
            }
        }
    }

    /// If the sub-matches of this pattern contain a GC point, this function
    /// spills the subject to a frame slot. The caller can then derive the
    /// pointers again after each sub-match.
    pub(crate) fn pattern_subject_slot(
        &self,
        pat: &Pattern,
        val: IntValue<'ctx>,
    ) -> CgResult<Option<u64>> {
        if !pattern_may_gc(pat) {
            return Ok(None);
        }
        if !self.framed() {
            return Err("internal: allocating pattern in frameless function".into());
        }
        Ok(Some(self.spill(val)?))
    }

    /// Matches a bitstring pattern. The byte offset becomes a runtime value
    /// after the first segment with a dynamic size or a utf8 type.
    /// Binary-type segments allocate sub-binaries. The subject stays in a
    /// frame slot across those segments (see match_pattern). Constant-size
    /// integer literals compare against static byte arrays.
    pub(crate) fn match_binary(
        &self,
        f: FunctionValue<'ctx>,
        val: IntValue<'ctx>,
        segs: &[mana_syntax::BinSegment<Box<Pattern>>],
        scope: &mut Scope<'ctx>,
        fail: BasicBlock<'ctx>,
    ) -> CgResult<()> {
        let specs = segs
            .iter()
            .map(|s| parse_seg_spec(&s.spec))
            .collect::<Result<Vec<_>, _>>()?;
        let slot = if specs.iter().any(|s| s.kind.allocates()) {
            if !self.framed() {
                return Err("internal: allocating binary pattern in frameless function".into());
            }
            Some(self.spill(val)?)
        } else {
            None
        };
        let all_const = !specs.iter().any(|s| s.kind.dynamic());
        let rest = specs
            .iter()
            .any(|s| matches!(s.kind, SegKind::Bin { size: SegSize::All }));
        let const_total_bits: u64 = specs
            .iter()
            .map(|s| match s.kind {
                SegKind::Int {
                    size: SegSize::Bytes(n),
                }
                | SegKind::Bin {
                    size: SegSize::Bytes(n),
                } => 8 * n,
                SegKind::Int {
                    size: SegSize::Bits(b),
                } => b,
                _ => 0,
            })
            .sum();
        let at_least = rest || !all_const;
        if !at_least && const_total_bits % 8 != 0 {
            // Binaries are byte-aligned. An exact pattern with a total size
            // that is not a multiple of 8 bits can never match.
            self.builder.build_unconditional_branch(fail).map_err(be)?;
            let dead = self.ctx.append_basic_block(f, "bm.dead");
            self.builder.position_at_end(dead);
            return Ok(());
        }
        let const_total: u64 = const_total_bits.div_ceil(8);
        // Preflight: the is-binary test and the length check. For all-constant
        // patterns the length check is exact. For dynamic patterns it is a
        // lower bound, and each segment checks its bounds again. The tag
        // test, the kind byte, and the length compare are inline, with no
        // runtime call.
        let ok = self.kind_test(f, val, |s, header| {
            let k = s
                .builder
                .build_and(header, s.i64t.const_int(0xff, false), "bl.k")
                .map_err(be)?;
            // Kinds 5 (bin) and 13 (sub-binary view) differ only in bit 3.
            // Both carry len<<8 in the header, so one length check serves
            // both.
            let k2 = s
                .builder
                .build_or(k, s.i64t.const_int(8, false), "bl.k2")
                .map_err(be)?;
            let is_bin = s
                .builder
                .build_int_compare(IntPredicate::EQ, k2, s.i64t.const_int(13, false), "bl.bin")
                .map_err(be)?;
            let len = s
                .builder
                .build_right_shift(header, s.i64t.const_int(8, false), false, "bl.len")
                .map_err(be)?;
            let want = s.i64t.const_int(const_total, false);
            let lok = s
                .builder
                .build_int_compare(
                    if at_least {
                        IntPredicate::UGE
                    } else {
                        IntPredicate::EQ
                    },
                    len,
                    want,
                    "bl.ok",
                )
                .map_err(be)?;
            s.builder.build_and(is_bin, lok, "bl.and").map_err(be)
        })?;
        self.branch_test(f, ok, fail)?;

        let mut off: IntValue<'ctx> = self.i64t.const_zero();
        // prefix_static is true while every previous segment had a static
        // byte width. In that case the preflight (len >= const_total) already
        // bounds-checks this segment. Constant and byte reads can then inline
        // without a runtime call. static_bits tracks the exact bit offset
        // while prefix_static holds.
        let mut prefix_static = true;
        let mut static_bits: u64 = 0;
        for (spec, seg) in specs.iter().zip(segs) {
            if prefix_static
                && static_bits % 8 != 0
                && !matches!(
                    spec.kind,
                    SegKind::Int {
                        size: SegSize::Bits(_)
                    }
                )
            {
                return Err("TODO(bitstring): byte segment at a sub-byte offset".into());
            }
            let subject = match slot {
                Some(s) => self.reload(s)?,
                None => val,
            };
            match &spec.kind {
                SegKind::Int { size } => {
                    if let SegSize::Bits(s) = size {
                        // A sub-byte unsigned big-endian read at a constant
                        // bit offset. This is the nibble destructuring shape
                        // in Code.Identifier.escape and similar functions.
                        if !prefix_static {
                            return Err(
                                "TODO(bitstring): sub-byte segment after dynamic prefix".into()
                            );
                        }
                        let s = *s;
                        let first = static_bits / 8;
                        let last = (static_bits + s - 1) / 8;
                        let base = self.bin_base_addr(f, subject)?;
                        let bp = self
                            .builder
                            .build_int_to_ptr(base, self.ptrt, "bb.p")
                            .map_err(be)?;
                        let mut acc = self.i64t.const_zero();
                        for byte_i in first..=last {
                            let gep = unsafe {
                                self.builder
                                    .build_in_bounds_gep(
                                        self.ctx.i8_type(),
                                        bp,
                                        &[self.i64t.const_int(byte_i, false)],
                                        "bb.g",
                                    )
                                    .map_err(be)?
                            };
                            let b = self
                                .builder
                                .build_load(self.ctx.i8_type(), gep, "bb.b")
                                .map_err(be)?
                                .into_int_value();
                            let w = self
                                .builder
                                .build_int_z_extend(b, self.i64t, "bb.w")
                                .map_err(be)?;
                            let shifted = self
                                .builder
                                .build_left_shift(acc, self.i64t.const_int(8, false), "bb.sh")
                                .map_err(be)?;
                            acc = self.builder.build_or(shifted, w, "bb.acc").map_err(be)?;
                        }
                        let span_bits = (last - first + 1) * 8;
                        let shift = span_bits - (static_bits - first * 8) - s;
                        let down = self
                            .builder
                            .build_right_shift(
                                acc,
                                self.i64t.const_int(shift, false),
                                false,
                                "bb.dn",
                            )
                            .map_err(be)?;
                        let masked = self
                            .builder
                            .build_and(down, self.i64t.const_int((1u64 << s) - 1, false), "bb.msk")
                            .map_err(be)?;
                        let v = self.retag_int(masked)?;
                        self.match_pattern(f, v, &seg.value, scope, fail)?;
                        static_bits += s;
                        if static_bits % 8 == 0 {
                            off = self.i64t.const_int(static_bits / 8, false);
                        }
                        continue;
                    }
                    let nbytes = self.seg_bytes(f, size, scope, Some(fail))?;
                    // Constant integer sub-patterns with constant sizes
                    // compare as bytes. This covers the wide folded literals
                    // from erlc.
                    if let (
                        SegSize::Bytes(n),
                        Pattern::Lit(l @ (Literal::Int(_) | Literal::Big(_))),
                    ) = (size, seg.value.as_ref())
                    {
                        if let Some(bytes) =
                            seg_const_bytes(&Expr::Lit(l.clone()), *n, spec.little)?
                        {
                            // Short literals under a preflighted length use
                            // inline byte loads and compares. The whitespace
                            // trim pyramid runs about 20 of these per string.
                            if prefix_static && bytes.len() <= 16 {
                                let base = self.bin_base_addr(f, subject)?;
                                let bp = self
                                    .builder
                                    .build_int_to_ptr(base, self.ptrt, "bm.p")
                                    .map_err(be)?;
                                let mut ok = self.ctx.bool_type().const_all_ones();
                                for (j, byte) in bytes.iter().enumerate() {
                                    let idx = self
                                        .builder
                                        .build_int_add(
                                            off,
                                            self.i64t.const_int(j as u64, false),
                                            "bm.i",
                                        )
                                        .map_err(be)?;
                                    let gep = unsafe {
                                        self.builder
                                            .build_in_bounds_gep(
                                                self.ctx.i8_type(),
                                                bp,
                                                &[idx],
                                                "bm.g",
                                            )
                                            .map_err(be)?
                                    };
                                    let b = self
                                        .builder
                                        .build_load(self.ctx.i8_type(), gep, "bm.b")
                                        .map_err(be)?
                                        .into_int_value();
                                    let eq = self
                                        .builder
                                        .build_int_compare(
                                            IntPredicate::EQ,
                                            b,
                                            self.ctx.i8_type().const_int(*byte as u64, false),
                                            "bm.eq",
                                        )
                                        .map_err(be)?;
                                    ok = self.builder.build_and(ok, eq, "bm.and").map_err(be)?;
                                }
                                self.branch_test(f, ok, fail)?;
                                off = self
                                    .builder
                                    .build_int_add(
                                        off,
                                        self.i64t.const_int(bytes.len() as u64, false),
                                        "boff",
                                    )
                                    .map_err(be)?;
                                static_bits += 8 * bytes.len() as u64;
                                continue;
                            }
                            let ptr = self.static_bytes(&bytes)?;
                            let call = self
                                .builder
                                .build_call(
                                    self.rt_fn("mana_rt_bin_match_bytes", || {
                                        self.i64t.fn_type(
                                            &[
                                                BasicMetadataTypeEnum::IntType(self.i64t),
                                                BasicMetadataTypeEnum::IntType(self.i64t),
                                                BasicMetadataTypeEnum::PointerType(self.ptrt),
                                                BasicMetadataTypeEnum::IntType(self.i64t),
                                            ],
                                            false,
                                        )
                                    }),
                                    &[
                                        subject.into(),
                                        off.into(),
                                        ptr.into(),
                                        self.i64t.const_int(bytes.len() as u64, false).into(),
                                    ],
                                    "bmb",
                                )
                                .map_err(be)?;
                            let ok = call_result(call)?.into_int_value();
                            let ok = self
                                .builder
                                .build_int_compare(
                                    IntPredicate::NE,
                                    ok,
                                    self.i64t.const_zero(),
                                    "bmb.ok",
                                )
                                .map_err(be)?;
                            self.branch_test(f, ok, fail)?;
                            off = self
                                .builder
                                .build_int_add(
                                    off,
                                    self.i64t.const_int(bytes.len() as u64, false),
                                    "boff",
                                )
                                .map_err(be)?;
                            static_bits += 8 * bytes.len() as u64;
                            continue;
                        }
                    }
                    if matches!(size, SegSize::Bytes(n) if *n > 8) {
                        return Err(
                            "TODO(bignum-segments): binding integer segments over 64 bits".into(),
                        );
                    }
                    // A 1-byte unsigned read under a preflighted length is an
                    // inline load. This is the string-walk shape
                    // <<h, rest::binary>>.
                    if prefix_static && matches!(size, SegSize::Bytes(1)) && !spec.signed {
                        let base = self.bin_base_addr(f, subject)?;
                        let bp = self
                            .builder
                            .build_int_to_ptr(base, self.ptrt, "br.p")
                            .map_err(be)?;
                        let gep = unsafe {
                            self.builder
                                .build_in_bounds_gep(self.ctx.i8_type(), bp, &[off], "br.g")
                                .map_err(be)?
                        };
                        let b = self
                            .builder
                            .build_load(self.ctx.i8_type(), gep, "br.b")
                            .map_err(be)?
                            .into_int_value();
                        let w = self
                            .builder
                            .build_int_z_extend(b, self.i64t, "br.w")
                            .map_err(be)?;
                        let v = self.retag_int(w)?;
                        self.match_pattern(f, v, &seg.value, scope, fail)?;
                        off = self
                            .builder
                            .build_int_add(off, self.i64t.const_int(1, false), "boff")
                            .map_err(be)?;
                        static_bits += 8;
                        continue;
                    }
                    let flags = (spec.little as u64) | ((spec.signed as u64) << 1);
                    let call = self
                        .builder
                        .build_call(
                            self.rt_fn("mana_rt_bin_read_int", || {
                                self.i64t.fn_type(
                                    &[
                                        BasicMetadataTypeEnum::IntType(self.i64t),
                                        BasicMetadataTypeEnum::IntType(self.i64t),
                                        BasicMetadataTypeEnum::IntType(self.i64t),
                                        BasicMetadataTypeEnum::IntType(self.i64t),
                                    ],
                                    false,
                                )
                            }),
                            &[
                                subject.into(),
                                off.into(),
                                nbytes.into(),
                                self.i64t.const_int(flags, false).into(),
                            ],
                            "bri",
                        )
                        .map_err(be)?;
                    let v = call_result(call)?.into_int_value();
                    if !all_const {
                        let ok = self
                            .builder
                            .build_int_compare(IntPredicate::NE, v, self.sentinel(), "bri.ok")
                            .map_err(be)?;
                        self.branch_test(f, ok, fail)?;
                    }
                    self.match_pattern(f, v, &seg.value, scope, fail)?;
                    off = self
                        .builder
                        .build_int_add(off, nbytes, "boff")
                        .map_err(be)?;
                }
                SegKind::Bin { size } => {
                    // `rest::binary` after a static prefix is the string-walk
                    // shape <<c, rest::binary>>. The code builds the zero-copy
                    // view inline: 3 words, no runtime call, no byte copy. The
                    // preflight already proved len >= off. The code allocates
                    // first and then reads the subject again. The allocation
                    // can run a GC that moves the subject.
                    if matches!(size, SegSize::All) && prefix_static && slot.is_some() {
                        let vp = self.alloc_words(3)?;
                        let subject = self.reload(slot.unwrap())?;
                        let sp = self
                            .builder
                            .build_int_to_ptr(subject, self.ptrt, "brv.p")
                            .map_err(be)?;
                        let header = self
                            .builder
                            .build_load(self.i64t, sp, "brv.h")
                            .map_err(be)?
                            .into_int_value();
                        let total = self
                            .builder
                            .build_right_shift(
                                header,
                                self.i64t.const_int(8, false),
                                false,
                                "brv.tot",
                            )
                            .map_err(be)?;
                        let len = self
                            .builder
                            .build_int_sub(total, off, "brv.len")
                            .map_err(be)?;
                        let (parent, poff) = self.bin_parent_off(f, subject)?;
                        let abs = self
                            .builder
                            .build_int_add(poff, off, "brv.abs")
                            .map_err(be)?;
                        let hdr = self
                            .builder
                            .build_or(
                                self.builder
                                    .build_left_shift(len, self.i64t.const_int(8, false), "brv.l8")
                                    .map_err(be)?,
                                self.i64t.const_int(KIND_SUBBIN, false),
                                "brv.hdr",
                            )
                            .map_err(be)?;
                        self.store_word(vp, 0, hdr)?;
                        self.store_word(vp, 1, parent)?;
                        self.store_word(vp, 2, abs)?;
                        let v = self
                            .builder
                            .build_ptr_to_int(vp, self.i64t, "brv")
                            .map_err(be)?;
                        self.match_pattern(f, v, &seg.value, scope, fail)?;
                        continue;
                    }
                    let len: IntValue<'ctx> = match size {
                        SegSize::All => self.i64t.const_int(u64::MAX, false), // -1
                        _ => self.seg_bytes(f, size, scope, Some(fail))?,
                    };
                    let call = self
                        .builder
                        .build_call(
                            self.rt_fn("mana_rt_bin_slice", || {
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
                            &[
                                self.ctx_val().into(),
                                subject.into(),
                                off.into(),
                                len.into(),
                            ],
                            "brs",
                        )
                        .map_err(be)?;
                    let v = call_result(call)?.into_int_value();
                    let ok = self
                        .builder
                        .build_int_compare(IntPredicate::NE, v, self.sentinel(), "brs.ok")
                        .map_err(be)?;
                    self.branch_test(f, ok, fail)?;
                    self.match_pattern(f, v, &seg.value, scope, fail)?;
                    if !matches!(size, SegSize::All) {
                        off = self.builder.build_int_add(off, len, "boff").map_err(be)?;
                    }
                }
                SegKind::Utf8 => {
                    let call = self
                        .builder
                        .build_call(
                            self.rt_tt_i64("mana_rt_bin_read_utf8"),
                            &[subject.into(), off.into()],
                            "bru",
                        )
                        .map_err(be)?;
                    let raw = call_result(call)?.into_int_value();
                    let ok = self
                        .builder
                        .build_int_compare(IntPredicate::SGE, raw, self.i64t.const_zero(), "bru.ok")
                        .map_err(be)?;
                    self.branch_test(f, ok, fail)?;
                    let cp = self
                        .builder
                        .build_and(raw, self.i64t.const_int(0xffff_ffff, false), "bru.cp")
                        .map_err(be)?;
                    let cpt = self.retag_int(cp)?;
                    self.match_pattern(f, cpt, &seg.value, scope, fail)?;
                    let width = self
                        .builder
                        .build_right_shift(raw, self.i64t.const_int(32, false), false, "bru.w")
                        .map_err(be)?;
                    off = self.builder.build_int_add(off, width, "boff").map_err(be)?;
                }
            }
            match &spec.kind {
                SegKind::Int {
                    size: SegSize::Bytes(n),
                }
                | SegKind::Bin {
                    size: SegSize::Bytes(n),
                } => static_bits += 8 * n,
                _ => prefix_static = false,
            }
        }
        // Without a rest segment, the pattern must consume the binary exactly.
        if !rest && !all_const {
            let subject = match slot {
                Some(s) => self.reload(s)?,
                None => val,
            };
            let call = self
                .builder
                .build_call(
                    self.rt_fn("mana_rt_bin_len_check", || {
                        self.i64t.fn_type(
                            &[
                                BasicMetadataTypeEnum::IntType(self.i64t),
                                BasicMetadataTypeEnum::IntType(self.i64t),
                                BasicMetadataTypeEnum::IntType(self.i64t),
                            ],
                            false,
                        )
                    }),
                    &[subject.into(), off.into(), self.i64t.const_zero().into()],
                    "blen.end",
                )
                .map_err(be)?;
            let ok = call_result(call)?.into_int_value();
            let ok = self
                .builder
                .build_int_compare(IntPredicate::NE, ok, self.i64t.const_zero(), "blen.end.ok")
                .map_err(be)?;
            self.branch_test(f, ok, fail)?;
        }
        Ok(())
    }

    /// Returns the byte count of a segment as a runtime value. Dynamic sizes
    /// check that the size is a small integer and byte-aligned. In a pattern
    /// (`fail` is set), a bad size is a match failure. In construction, a bad
    /// size raises badarg.
    pub(crate) fn seg_bytes(
        &self,
        f: FunctionValue<'ctx>,
        size: &SegSize,
        scope: &mut Scope<'ctx>,
        fail: Option<BasicBlock<'ctx>>,
    ) -> CgResult<IntValue<'ctx>> {
        match size {
            SegSize::Bytes(n) => Ok(self.i64t.const_int(*n, false)),
            SegSize::Bits(_) => Err("internal: seg_bytes on sub-byte segment".into()),
            SegSize::All => Err("internal: seg_bytes on rest segment".into()),
            SegSize::Dyn { size, unit } => {
                let v = self.compile_value(f, size, scope)?;
                let tag = self.tag_of(v)?;
                let is_int = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_int(TAG_SMALL, false),
                        "sz.int",
                    )
                    .map_err(be)?;
                match fail {
                    Some(fail) => self.branch_test(f, is_int, fail)?,
                    None => self.guard_badarg(f, is_int)?,
                }
                let raw = self
                    .builder
                    .build_right_shift(v, self.i64t.const_int(3, false), true, "sz.raw")
                    .map_err(be)?;
                let bits = self
                    .builder
                    .build_int_mul(raw, self.i64t.const_int(*unit as u64, false), "sz.bits")
                    .map_err(be)?;
                let low = self
                    .builder
                    .build_and(bits, self.i64t.const_int(7, false), "sz.low")
                    .map_err(be)?;
                let aligned = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, low, self.i64t.const_zero(), "sz.al")
                    .map_err(be)?;
                let nonneg = self
                    .builder
                    .build_int_compare(IntPredicate::SGE, bits, self.i64t.const_zero(), "sz.nn")
                    .map_err(be)?;
                let ok = self
                    .builder
                    .build_and(aligned, nonneg, "sz.ok")
                    .map_err(be)?;
                match fail {
                    Some(fail) => self.branch_test(f, ok, fail)?,
                    None => self.guard_badarg(f, ok)?,
                }
                self.builder
                    .build_right_shift(bits, self.i64t.const_int(3, false), false, "sz.bytes")
                    .map_err(be)
            }
        }
    }

    pub(crate) fn branch_test(
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
}
