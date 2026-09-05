//! The `erlang` module BIFs, one method per family.
//!
//! Each method matches `(name, argv.len())` and returns `Ok(None)` for a
//! pair it does not own. `compile_bif` calls the methods in a chain. A pair
//! must appear in exactly one family.

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
                // both-small inline (no allocation, no raise); anything else
                // takes the runtime slow path (floats box without triggering
                // GC — see box_float — so this is NOT a may-gc site)
                let opcode = match name {
                    "+" => 0u64,   // AR_ADD
                    "-" => 1,      // AR_SUB
                    "*" => 2,      // AR_MUL
                    "div" => 4,    // AR_IDIV (slow path = badarith)
                    _ => 5,        // AR_REM
                };
                self.arith_fastslow(f, name, opcode, argv[0], Some(argv[1]))
            }
            ("-", 1) => self.arith_fastslow(f, "neg", 6, argv[0], None),
            ("+", 1) => {
                // +X is a no-op for numbers; badarith otherwise
                let both = self.small_test(argv[0], None)?;
                let slow = self.ctx.append_basic_block(f, "pos.slow");
                let merge = self.ctx.append_basic_block(f, "pos.merge");
                let fast_bb = self.builder.get_insert_block().unwrap();
                self.builder
                    .build_conditional_branch(both, merge, slow)
                    .map_err(be)?;
                self.builder.position_at_end(slow);
                // float or junk: 0 + X coerces/validates
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
            ("<", 2) | ("=<", 2) | (">", 2) | (">=", 2) | ("==", 2) | ("/=", 2)
            | ("=:=", 2) | ("=/=", 2) => {
                // fast path: both small ints (tagging is order-preserving);
                // slow path: full Erlang term order in the runtime
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
                            self.i64t.const_int(3, false).into(), // AR_FDIV
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
                    "band" => 8u64, // AR_BAND
                    "bor" => 9,     // AR_BOR
                    _ => 10,        // AR_BXOR
                };
                self.arith_fastslow(f, name, opcode, argv[0], Some(argv[1]))
            }
            ("bnot", 1) => self.arith_fastslow(f, "bnot", 13, argv[0], None),
            ("bsl", 2) | ("bsr", 2) => {
                // no inline fast path: shift semantics (negative amounts,
                // 61-bit overflow abort) live in the runtime
                let opcode = if name == "bsl" { 11u64 } else { 12 }; // AR_BSL/AR_BSR
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
                    "trunc" => 0u64,
                    "round" => 1,
                    "floor" => 2,
                    _ => 3,
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
            ("float_to_binary", 1) | ("float_to_binary", 2) | ("float_to_list", 1)
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
            ("abs", 1) => self.arith_fastslow(f, "abs", 7, argv[0], None),
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

    pub(crate) fn bif_process(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        argv: &[IntValue<'ctx>],
    ) -> CgResult<Option<IntValue<'ctx>>> {
        let v: CgResult<IntValue<'ctx>> = match (name, argv.len()) {
            ("raise", 3) => {
                // re-raise with a dynamic class; the stacktrace argument is
                // dropped — TODO(stacktraces)
                let ctx = self.ctx_val();
                self.mem_store(ctx, CTX_EXC_CLASS, argv[0], MemKind::Ctx)?;
                self.mem_store(ctx, CTX_EXC_REASON, argv[1], MemKind::Ctx)?;
                let target = self.unwind_target(f)?;
                self.builder.build_unconditional_branch(target).map_err(be)?;
                let dead = self.ctx.append_basic_block(f, "raise3.dead");
                self.builder.position_at_end(dead);
                Ok(self.i64t.get_undef())
            }
            ("self", 0) => {
                let call = self
                    .builder
                    .build_call(self.rt_p_i64("mana_rt_self"), &[self.ctx_val().into()], "self")
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("spawn", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_spawn(),
                        &[self.ctx_val().into(), argv[0].into()],
                        "spawn",
                    )
                    .map_err(be)?;
                let pid = call_result(call)?.into_int_value();
                // 0 = not an arity-0 fun
                let bad = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, pid, self.i64t.const_zero(), "spawn.bad")
                    .map_err(be)?;
                let bad_bb = self.ctx.append_basic_block(f, "spawn.badarg");
                let ok_bb = self.ctx.append_basic_block(f, "spawn.ok");
                self.builder
                    .build_conditional_branch(bad, bad_bb, ok_bb)
                    .map_err(be)?;
                self.builder.position_at_end(bad_bb);
                let class = self.atom_term("error")?;
                let reason = self.atom_term("badarg")?;
                let ctx = self.ctx_val();
                self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
                self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
                let target = self.unwind_target(f)?;
                self.builder.build_unconditional_branch(target).map_err(be)?;
                self.builder.position_at_end(ok_bb);
                Ok(pid)
            }
            ("make_ref", 0) => {
                let call = self
                    .builder
                    .build_call(self.rt_p_i64("mana_rt_make_ref"), &[self.ctx_val().into()], "r")
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("link", 1) => {
                self.builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_link"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "",
                    )
                    .map_err(be)?;
                self.atom_term("true")
            }
            ("unlink", 1) => {
                self.builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_unlink"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "",
                    )
                    .map_err(be)?;
                self.atom_term("true")
            }
            ("monitor", 2) => {
                // monitor(process, Pid) — first arg assumed 'process'
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_monitor"),
                        &[self.ctx_val().into(), argv[1].into()],
                        "mref",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("demonitor", 1) => {
                self.builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_demonitor"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "",
                    )
                    .map_err(be)?;
                self.atom_term("true")
            }
            ("spawn_link", 1) | ("spawn_monitor", 1) => {
                let fname = if name == "spawn_link" {
                    "mana_rt_spawn_link"
                } else {
                    "mana_rt_spawn_monitor"
                };
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64(fname),
                        &[self.ctx_val().into(), argv[0].into()],
                        "sp",
                    )
                    .map_err(be)?;
                let r = call_result(call)?.into_int_value();
                let bad = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, r, self.i64t.const_zero(), "sp.bad")
                    .map_err(be)?;
                let bad_bb = self.ctx.append_basic_block(f, "sp.badarg");
                let ok_bb = self.ctx.append_basic_block(f, "sp.ok");
                self.builder
                    .build_conditional_branch(bad, bad_bb, ok_bb)
                    .map_err(be)?;
                self.builder.position_at_end(bad_bb);
                let class = self.atom_term("error")?;
                let reason = self.atom_term("badarg")?;
                let ctx = self.ctx_val();
                self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
                self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
                let target = self.unwind_target(f)?;
                self.builder.build_unconditional_branch(target).map_err(be)?;
                self.builder.position_at_end(ok_bb);
                Ok(r)
            }
            ("process_flag", 2) => {
                // dispatch on the flag name: trap_exit is real, the rest
                // are accepted no-ops returning a plausible old value
                let call = self
                    .builder
                    .build_call(
                        self.rt_fn("mana_rt_process_flag", || {
                            self.i64t.fn_type(
                                &[
                                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                ],
                                false,
                            )
                        }),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "prev",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("system_flag", 2) => {
                // VM tuning knobs: accepted no-ops (badarg on unknown flags)
                let call = self
                    .builder
                    .build_call(
                        self.rt_fn("mana_rt_system_flag", || {
                            self.i64t.fn_type(
                                &[
                                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                ],
                                false,
                            )
                        }),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "prev",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("exit", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_fn("mana_rt_exit2", || {
                            self.i64t.fn_type(
                                &[
                                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                ],
                                false,
                            )
                        }),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "",
                    )
                    .map_err(be)?;
                let _ = call;
                self.atom_term("true")
            }
            ("!", 2) | ("send", 2) | ("send", 3) => {
                // send/3's options (noconnect/nosuspend) are distribution
                // concerns — ignored; it returns ok instead of the message
                self.builder
                    .build_call(
                        self.rt_send(),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "",
                    )
                    .map_err(be)?;
                if argv.len() == 3 {
                    self.atom_term("ok")
                } else {
                    Ok(argv[1])
                }
            }
            ("apply", 3) | ("apply", 2) => {
                let helper = if argv.len() == 3 { "mana_rt_apply3" } else { "mana_rt_apply_fun" };
                let mut cargs: Vec<BasicMetadataValueEnum> = vec![self.ctx_val().into()];
                cargs.extend(argv.iter().map(|v| BasicMetadataValueEnum::from(*v)));
                let callee = if argv.len() == 3 {
                    self.rt_fn(helper, || {
                        self.i64t.fn_type(
                            &[
                                BasicMetadataTypeEnum::PointerType(self.ptrt),
                                BasicMetadataTypeEnum::IntType(self.i64t),
                                BasicMetadataTypeEnum::IntType(self.i64t),
                                BasicMetadataTypeEnum::IntType(self.i64t),
                            ],
                            false,
                        )
                    })
                } else {
                    self.rt_ptt_i64(helper)
                };
                let call = self.builder.build_call(callee, &cargs, "apply").map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("spawn_opt", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_spawn_opt_fun"),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "spawnopt2",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("spawn_opt", 4) | ("spawn", 3) | ("spawn_link", 3) => {
                let callee = self.rt_fn("mana_rt_spawn_opt_mfa", || {
                    self.i64t.fn_type(
                        &[
                            BasicMetadataTypeEnum::PointerType(self.ptrt),
                            BasicMetadataTypeEnum::IntType(self.i64t),
                            BasicMetadataTypeEnum::IntType(self.i64t),
                            BasicMetadataTypeEnum::IntType(self.i64t),
                            BasicMetadataTypeEnum::IntType(self.i64t),
                        ],
                        false,
                    )
                });
                let opts = match name {
                    "spawn_opt" => argv[3],
                    "spawn_link" => {
                        // [link]
                        let p = self.alloc_words_kind(2, true)?;
                        let link = self.atom_term("link")?;
                        self.store_word(p, 0, link)?;
                        self.store_word(p, 1, self.nil())?;
                        let addr = self
                            .builder
                            .build_ptr_to_int(p, self.i64t, "opt.addr")
                            .map_err(be)?;
                        self.builder
                            .build_or(addr, self.i64t.const_int(TAG_CONS, false), "opt")
                            .map_err(be)?
                    }
                    _ => self.nil(),
                };
                let call = self
                    .builder
                    .build_call(
                        callee,
                        &[
                            self.ctx_val().into(),
                            argv[0].into(),
                            argv[1].into(),
                            argv[2].into(),
                            opts.into(),
                        ],
                        "spawnopt",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
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
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_int(1, false),
                        "ii.s",
                    )
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
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_int(1, false),
                        "n.s",
                    )
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
                // byte-aligned only: binary <=> bitstring
                let c = self.kind_test(f, argv[0], |s, header| {
                    let k = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xff, false), "k")
                        .map_err(be)?;
                    // bin (5) or sub-binary view (13)
                    let k2 = s
                        .builder
                        .build_or(k, s.i64t.const_int(8, false), "k2")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            k2,
                            s.i64t.const_int(13, false),
                            "k.b",
                        )
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

    pub(crate) fn bif_pdict_timers(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        argv: &[IntValue<'ctx>],
    ) -> CgResult<Option<IntValue<'ctx>>> {
        let v: CgResult<IntValue<'ctx>> = match (name, argv.len()) {
            ("put", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_pd_put"),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "pdput",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("get", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_pd_get"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "pdget",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("erase", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_pd_erase"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "pderase",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("get", 0) => {
                let callee = self.rt_fn("mana_rt_pd_get_all", || {
                    self.i64t.fn_type(
                        &[BasicMetadataTypeEnum::PointerType(self.ptrt)],
                        false,
                    )
                });
                let call = self
                    .builder
                    .build_call(callee, &[self.ctx_val().into()], "pdall")
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("register", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_register"),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "reg",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("whereis", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_whereis"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "whereis",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("unregister", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_unregister"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "unreg",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("demonitor", 2) => {
                // options: [flush] (and/or info) — flush is honored, the
                // info return value approximated; options list is constant
                // in practice so it is not inspected
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_demonitor_flush"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "demon2",
                    )
                    .map_err(be)?;
                let _ = call_result(call)?;
                self.atom_term("true")
            }
            ("process_info", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_process_info2"),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "pinfo",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("monitor", 3) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_monitor3"),
                        &[self.ctx_val().into(), argv[1].into(), argv[2].into()],
                        "mon3",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("send_after", 3) | ("start_timer", 3) => {
                let callee = self.rt_fn("mana_rt_send_after", || {
                    self.i64t.fn_type(
                        &[
                            BasicMetadataTypeEnum::PointerType(self.ptrt),
                            BasicMetadataTypeEnum::IntType(self.i64t),
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
                            self.i64t
                                .const_int((name == "start_timer") as u64, false)
                                .into(),
                        ],
                        "sendafter",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("cancel_timer", 1) | ("cancel_timer", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_cancel_timer"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "canceltimer",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("monotonic_time", 0) | ("monotonic_time", 1) | ("system_time", 0)
            | ("system_time", 1) => {
                let helper = if name == "monotonic_time" {
                    "mana_rt_monotonic_time"
                } else {
                    "mana_rt_system_time"
                };
                let unit = if argv.len() == 1 {
                    argv[0]
                } else {
                    self.atom_term("native")?
                };
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64(helper),
                        &[self.ctx_val().into(), unit.into()],
                        "time",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("convert_time_unit", 3) => {
                let callee = self.rt_fn("mana_rt_convert_time_unit", || {
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
                        "ctu",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            _ => return Ok(None),
        };
        v.map(Some)
    }

    pub(crate) fn bif_system(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        argv: &[IntValue<'ctx>],
    ) -> CgResult<Option<IntValue<'ctx>>> {
        let v: CgResult<IntValue<'ctx>> = match (name, argv.len()) {
            ("get_module_info", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_get_module_info"),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "gmi",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("get_module_info", 1) => Ok(self.nil()),
            ("module_loaded", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_module_loaded"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "mld",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("unique_integer", 0) | ("unique_integer", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_p_i64("mana_rt_unique_integer"),
                        &[self.ctx_val().into()],
                        "uniq",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("get_keys", 0) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_p_i64("mana_rt_pd_keys"),
                        &[self.ctx_val().into()],
                        "pdkeys",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("hibernate", 3) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_fn("mana_rt_hibernate", || {
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
                        "hib",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("is_record", 3) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_fn("mana_rt_is_record", || {
                            self.i64t.fn_type(
                                &[
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                ],
                                false,
                            )
                        }),
                        &[argv[0].into(), argv[1].into(), argv[2].into()],
                        "isrec",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("fun_info", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_fun_info"),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "funinfo",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("fun_info_mfa", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_fun_info_mfa"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "fmfa",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("is_process_alive", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_is_process_alive"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "alive",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("make_fun", 3) => {
                let callee = self.rt_fn("mana_rt_make_fun", || {
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
                        "mkfun",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("function_exported", 3) => {
                let callee = self.rt_fn("mana_rt_function_exported", || {
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
                        "fexp",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("system_info", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_system_info"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "sysinfo",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("memory", 0) => {
                // allocator stats over OUR heaps (values diverge from BEAM)
                let call = self
                    .builder
                    .build_call(
                        self.rt_fn("mana_rt_memory", || {
                            self.i64t.fn_type(
                                &[BasicMetadataTypeEnum::PointerType(self.ptrt)],
                                false,
                            )
                        }),
                        &[self.ctx_val().into()],
                        "mem",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("statistics", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_statistics"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "stats",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("garbage_collect", 0) => self.atom_term("true"),
            // garbage_collect(Pid) — collection is implicit; report success
            ("garbage_collect", 1) => self.atom_term("true"),
            ("is_port", 1) => self.atom_term("false"),
            // no distribution: everything lives on nonode@nohost
            ("node", 0) | ("node", 1) => self.atom_term("nonode@nohost"),
            ("nodes", 0) | ("nodes", 1) => Ok(self.nil()),
            ("is_alive", 0) => self.atom_term("false"),
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
            ("term_to_binary", 1) | ("term_to_binary", 2)
            | ("binary_to_term", 1) | ("binary_to_term", 2) => {
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
                // encoding args (latin1/utf8) are irrelevant: names are utf8
                if name == "binary_to_atom" || name == "binary_to_existing_atom" {
                    let call = self
                        .builder
                        .build_call(
                            self.rt_ptt_i64("mana_rt_binary_to_atom"),
                            &[
                                self.ctx_val().into(),
                                argv[0].into(),
                                self.i64t
                                    .const_int(
                                        (name == "binary_to_existing_atom") as u64,
                                        false,
                                    )
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
                // element(I, Tuple), 1-based; badarg on any misuse
                let (i, t) = (argv[0], argv[1]);
                let ti = self.tag_of(i)?;
                let i_ok = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        ti,
                        self.i64t.const_int(1, false),
                        "el.i",
                    )
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
                    params.extend(
                        (1..nargs).map(|_| BasicMetadataTypeEnum::IntType(self.i64t)),
                    );
                    self.i64t.fn_type(&params, false)
                });
                let call = self.builder.build_call(callee, &args_ll, "rtb").map_err(be)?;
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
