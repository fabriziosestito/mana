//! The `erlang` module BIFs on data: numbers, type tests, binaries,
//! lists, tuples, and maps. One method per family.
//!
//! Each method matches `(name, argv.len())` and returns `Ok(None)` for a
//! pair it does not own. `compile_bif` calls the methods in a chain. A pair
//! must appear in exactly one family. The process, timer, and system
//! families live in `bif_erlang_proc.rs`.

use crate::*;

impl<'ctx, 'p> Cg<'ctx, 'p> {
    pub(crate) fn bif_arith(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        argv: &[IntValue<'ctx>],
    ) -> CgResult<Option<IntValue<'ctx>>> {
        let v: CgResult<IntValue<'ctx>> = match (name, argv.len()) {
            ("+", 2) | ("-", 2) | ("*", 2) | ("div", 2) | ("rem", 2) => {
                // The inline path handles two small integers. It does not
                // allocate and does not raise. All other operands take the
                // runtime slow path. Floats box without a GC (see
                // box_float), so this call is NOT a may-gc site.
                let opcode = match name {
                    "+" => AR_ADD,
                    "-" => AR_SUB,
                    "*" => AR_MUL,
                    "div" => AR_IDIV, // the slow path raises badarith
                    _ => AR_REM,
                };
                self.arith_fastslow(f, name, opcode, argv[0], Some(argv[1]))
            }
            ("-", 1) => self.arith_fastslow(f, "neg", AR_NEG, argv[0], None),
            ("+", 1) => {
                // +X returns a number unchanged. Any other term raises badarith.
                let both = self.small_test(argv[0], None)?;
                let slow = self.ctx.append_basic_block(f, "pos.slow");
                let merge = self.ctx.append_basic_block(f, "pos.merge");
                let fast_bb = self.builder.get_insert_block().unwrap();
                self.builder
                    .build_conditional_branch(both, merge, slow)
                    .map_err(be)?;
                self.builder.position_at_end(slow);
                // The operand is a float or junk. The runtime computes 0 + X.
                // This returns the float unchanged or raises badarith.
                let zero = self.i64t.const_int(1, false); // small 0
                let call = self
                    .builder
                    .build_call(
                        self.rt_arith(),
                        &[
                            self.ctx_val().into(),
                            self.i64t.const_zero().into(),
                            zero.into(),
                            argv[0].into(),
                        ],
                        "pos",
                    )
                    .map_err(be)?;
                let sv = call_result(call)?.into_int_value();
                let sv = self.check_exc(f, sv)?;
                let slow_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(merge).map_err(be)?;
                self.builder.position_at_end(merge);
                let phi = self.builder.build_phi(self.i64t, "pos.v").map_err(be)?;
                phi.add_incoming(&[(&argv[0], fast_bb), (&sv, slow_end)]);
                Ok(phi.as_basic_value().into_int_value())
            }
            ("<", 2)
            | ("=<", 2)
            | (">", 2)
            | (">=", 2)
            | ("==", 2)
            | ("/=", 2)
            | ("=:=", 2)
            | ("=/=", 2) => {
                // The fast path compares two small integers. The tag layout
                // keeps the integer order. The slow path uses the full
                // Erlang term order in the runtime.
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
            ("/", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_arith(),
                        &[
                            self.ctx_val().into(),
                            self.i64t.const_int(AR_FDIV, false).into(),
                            argv[0].into(),
                            argv[1].into(),
                        ],
                        "fdiv",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("band", 2) | ("bor", 2) | ("bxor", 2) => {
                let opcode = match name {
                    "band" => AR_BAND,
                    "bor" => AR_BOR,
                    _ => AR_BXOR,
                };
                self.arith_fastslow(f, name, opcode, argv[0], Some(argv[1]))
            }
            ("bnot", 1) => self.arith_fastslow(f, "bnot", AR_BNOT, argv[0], None),
            ("bsl", 2) | ("bsr", 2) => {
                // Shifts have no inline fast path. The runtime holds the
                // shift rules: negative amounts and the 61-bit overflow abort.
                let opcode = if name == "bsl" { AR_BSL } else { AR_BSR };
                let call = self
                    .builder
                    .build_call(
                        self.rt_arith(),
                        &[
                            self.ctx_val().into(),
                            self.i64t.const_int(opcode, false).into(),
                            argv[0].into(),
                            argv[1].into(),
                        ],
                        "bshift",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("float", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_to_float"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "tofl",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("trunc", 1) | ("round", 1) | ("floor", 1) | ("ceil", 1) => {
                let mode = match name {
                    "trunc" => F2I_TRUNC,
                    "round" => F2I_ROUND,
                    "floor" => F2I_FLOOR,
                    _ => F2I_CEIL,
                };
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_f2i"),
                        &[
                            self.ctx_val().into(),
                            self.i64t.const_int(mode, false).into(),
                            argv[0].into(),
                        ],
                        "f2i",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("float_to_binary", 1)
            | ("float_to_binary", 2)
            | ("float_to_list", 1)
            | ("float_to_list", 2) => {
                let opts = if argv.len() == 2 { argv[1] } else { self.nil() };
                let callee = self.rt_fn("mana_rt_float_to_binary", || {
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
                            argv[0].into(),
                            opts.into(),
                            self.i64t
                                .const_int(name.ends_with("list") as u64, false)
                                .into(),
                        ],
                        "f2b",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("binary_to_float", 1) | ("list_to_float", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_parse_float"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "pf",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("abs", 1) => self.arith_fastslow(f, "abs", AR_ABS, argv[0], None),
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
            _ => return Ok(None),
        };
        v.map(Some)
    }

    pub(crate) fn bif_type_tests(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        argv: &[IntValue<'ctx>],
    ) -> CgResult<Option<IntValue<'ctx>>> {
        let v: CgResult<IntValue<'ctx>> = match (name, argv.len()) {
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
            ("is_integer", 1) => {
                let tag = self.tag_of(argv[0])?;
                let small = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, tag, self.i64t.const_int(1, false), "ii.s")
                    .map_err(be)?;
                let isbig = self.kind_test(f, argv[0], |s, header| {
                    let k = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xff, false), "k")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            k,
                            s.i64t.const_int(3, false), // KIND_BIGNUM
                            "k.big",
                        )
                        .map_err(be)
                })?;
                let c = self.builder.build_or(small, isbig, "isint").map_err(be)?;
                self.bool_term(c)
            }
            ("is_atom", 1) | ("is_pid", 1) | ("is_reference", 1) => {
                let want: u64 = match name {
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
                    .build_int_compare(IntPredicate::EQ, tag, self.i64t.const_int(1, false), "n.s")
                    .map_err(be)?;
                let isf = self.kind_test(f, argv[0], |s, header| {
                    let k = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xff, false), "k")
                        .map_err(be)?;
                    let f1 = s
                        .builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            k,
                            s.i64t.const_int(KIND_FLOAT, false),
                            "k.f",
                        )
                        .map_err(be)?;
                    let bg = s
                        .builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            k,
                            s.i64t.const_int(3, false), // KIND_BIGNUM
                            "k.b",
                        )
                        .map_err(be)?;
                    s.builder.build_or(f1, bg, "k.n").map_err(be)
                })?;
                let c = self.builder.build_or(small, isf, "isnum").map_err(be)?;
                self.bool_term(c)
            }
            ("is_binary", 1) | ("is_bitstring", 1) => {
                // All binaries are byte-aligned. So is_binary and
                // is_bitstring give the same answer.
                let c = self.kind_test(f, argv[0], |s, header| {
                    let k = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xff, false), "k")
                        .map_err(be)?;
                    // The test accepts kind 5 (binary) and kind 13 (sub-binary view).
                    let k2 = s
                        .builder
                        .build_or(k, s.i64t.const_int(8, false), "k2")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(IntPredicate::EQ, k2, s.i64t.const_int(13, false), "k.b")
                        .map_err(be)
                })?;
                self.bool_term(c)
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
            _ => return Ok(None),
        };
        v.map(Some)
    }

    pub(crate) fn bif_binaries(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        argv: &[IntValue<'ctx>],
    ) -> CgResult<Option<IntValue<'ctx>>> {
        let v: CgResult<IntValue<'ctx>> = match (name, argv.len()) {
            ("term_to_binary", 1)
            | ("term_to_binary", 2)
            | ("binary_to_term", 1)
            | ("binary_to_term", 2) => {
                let helper = if name == "term_to_binary" {
                    "mana_rt_term_to_binary"
                } else {
                    "mana_rt_binary_to_term"
                };
                let opts = argv.get(1).copied().unwrap_or(self.nil());
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64(helper),
                        &[self.ctx_val().into(), argv[0].into(), opts.into()],
                        "etf",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("phash2", 1) | ("phash2", 2) => {
                let callee = self.rt_fn("mana_rt_phash2", || {
                    self.i64t.fn_type(
                        &[
                            BasicMetadataTypeEnum::PointerType(self.ptrt),
                            BasicMetadataTypeEnum::IntType(self.i64t),
                            BasicMetadataTypeEnum::IntType(self.i64t),
                        ],
                        false,
                    )
                });
                let range = argv.get(1).copied().unwrap_or(self.i64t.const_zero());
                let call = self
                    .builder
                    .build_call(
                        callee,
                        &[self.ctx_val().into(), argv[0].into(), range.into()],
                        "ph2",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("iolist_size", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_iolist_size"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "iosz",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("decode_packet", 3) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_fn("mana_rt_decode_packet", || {
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
                            argv[0].into(),
                            argv[1].into(),
                            argv[2].into(),
                        ],
                        "dpkt",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("byte_size", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_byte_size"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "bsz",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("bit_size", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_byte_size"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "bsz",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                let v = self.check_exc(f, v)?;
                let raw = self
                    .builder
                    .build_right_shift(v, self.i64t.const_int(3, false), true, "bits.raw")
                    .map_err(be)?;
                let bits = self
                    .builder
                    .build_int_mul(raw, self.i64t.const_int(8, false), "bits")
                    .map_err(be)?;
                self.retag_int(bits)
            }
            ("binary_part", 3) => {
                let callee = self.rt_fn("mana_rt_binary_part", || {
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
                            argv[0].into(),
                            argv[1].into(),
                            argv[2].into(),
                        ],
                        "bpart",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("binary_to_integer", 1)
            | ("binary_to_integer", 2)
            | ("list_to_integer", 1)
            | ("list_to_integer", 2) => {
                let helper = if name == "binary_to_integer" {
                    "mana_rt_binary_to_integer"
                } else {
                    "mana_rt_list_to_integer"
                };
                let base = if argv.len() == 2 {
                    argv[1]
                } else {
                    self.i64t.const_int((10 << 3) | 1, false)
                };
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64(helper),
                        &[self.ctx_val().into(), argv[0].into(), base.into()],
                        "x2i",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("integer_to_binary", 1)
            | ("integer_to_binary", 2)
            | ("integer_to_list", 1)
            | ("integer_to_list", 2) => {
                let helper = if name == "integer_to_binary" {
                    "mana_rt_integer_to_binary"
                } else {
                    "mana_rt_integer_to_list"
                };
                let base = if argv.len() == 2 {
                    argv[1]
                } else {
                    self.i64t.const_int((10 << 3) | 1, false)
                };
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64(helper),
                        &[self.ctx_val().into(), argv[0].into(), base.into()],
                        "i2x",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("pid_to_list", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_pid_to_list"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "p2l",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("list_to_tuple", 1) | ("tuple_to_list", 1) => {
                let helper = if name == "list_to_tuple" {
                    "mana_rt_list_to_tuple"
                } else {
                    "mana_rt_tuple_to_list"
                };
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64(helper),
                        &[self.ctx_val().into(), argv[0].into()],
                        "t2l",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("split_binary", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_split_binary"),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "splb",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("list_to_atom", 1) | ("list_to_existing_atom", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_list_to_atom"),
                        &[
                            self.ctx_val().into(),
                            argv[0].into(),
                            self.i64t
                                .const_int((name == "list_to_existing_atom") as u64, false)
                                .into(),
                        ],
                        "l2a",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("atom_to_list", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_atom_to_list"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "a2l",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("binary_to_list", 1)
            | ("list_to_binary", 1)
            | ("iolist_to_binary", 1)
            | ("atom_to_binary", 1)
            | ("atom_to_binary", 2)
            | ("binary_to_atom", 1)
            | ("binary_to_atom", 2)
            | ("binary_to_existing_atom", 1)
            | ("binary_to_existing_atom", 2) => {
                // The code ignores the encoding argument (latin1 or utf8).
                // Atom names are always utf8.
                if name == "binary_to_atom" || name == "binary_to_existing_atom" {
                    let call = self
                        .builder
                        .build_call(
                            self.rt_ptt_i64("mana_rt_binary_to_atom"),
                            &[
                                self.ctx_val().into(),
                                argv[0].into(),
                                self.i64t
                                    .const_int((name == "binary_to_existing_atom") as u64, false)
                                    .into(),
                            ],
                            "b2a",
                        )
                        .map_err(be)?;
                    let v = call_result(call)?.into_int_value();
                    return self.check_exc(f, v).map(Some);
                }
                let helper = match name {
                    "binary_to_list" => "mana_rt_binary_to_list",
                    "list_to_binary" => "mana_rt_list_to_binary",
                    "iolist_to_binary" => "mana_rt_iolist_to_binary",
                    _ => "mana_rt_atom_to_binary",
                };
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64(helper),
                        &[self.ctx_val().into(), argv[0].into()],
                        "bconv",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            _ => return Ok(None),
        };
        v.map(Some)
    }

    pub(crate) fn bif_lists_tuples_maps(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        argv: &[IntValue<'ctx>],
    ) -> CgResult<Option<IntValue<'ctx>>> {
        let v: CgResult<IntValue<'ctx>> = match (name, argv.len()) {
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
                // element(I, Tuple) counts from 1. A bad index, a bad index
                // type, or a non-tuple raises badarg.
                let (i, t) = (argv[0], argv[1]);
                let ti = self.tag_of(i)?;
                let i_ok = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, ti, self.i64t.const_int(1, false), "el.i")
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
                    params.extend((1..nargs).map(|_| BasicMetadataTypeEnum::IntType(self.i64t)));
                    self.i64t.fn_type(&params, false)
                });
                let call = self
                    .builder
                    .build_call(callee, &args_ll, "rtb")
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("display", 1) => {
                self.builder
                    .build_call(self.rt_display(), &[argv[0].into()], "")
                    .map_err(be)?;
                self.atom_term("true")
            }
            _ => return Ok(None),
        };
        v.map(Some)
    }
}
