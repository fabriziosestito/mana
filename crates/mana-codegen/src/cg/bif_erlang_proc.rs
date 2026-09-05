//! The `erlang` module BIFs on processes, timers, and the system:
//! spawn, send, links, the process dictionary, the name registry, timers,
//! and system information. Same contract as `bif_erlang.rs`.

use crate::*;

impl<'ctx, 'p> Cg<'ctx, 'p> {
    pub(crate) fn bif_process(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        argv: &[IntValue<'ctx>],
    ) -> CgResult<Option<IntValue<'ctx>>> {
        let v: CgResult<IntValue<'ctx>> = match (name, argv.len()) {
            ("raise", 3) => {
                // raise/3 raises again with a class that the caller chooses at
                // run time. TODO(stacktraces): the code ignores the
                // stacktrace argument.
                let ctx = self.ctx_val();
                self.mem_store(ctx, CTX_EXC_CLASS, argv[0], MemKind::Ctx)?;
                self.mem_store(ctx, CTX_EXC_REASON, argv[1], MemKind::Ctx)?;
                let target = self.unwind_target(f)?;
                self.builder
                    .build_unconditional_branch(target)
                    .map_err(be)?;
                let dead = self.ctx.append_basic_block(f, "raise3.dead");
                self.builder.position_at_end(dead);
                Ok(self.i64t.get_undef())
            }
            ("self", 0) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_p_i64("mana_rt_self"),
                        &[self.ctx_val().into()],
                        "self",
                    )
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
                // The runtime returns 0 when the argument is not a fun of arity 0.
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
                self.builder
                    .build_unconditional_branch(target)
                    .map_err(be)?;
                self.builder.position_at_end(ok_bb);
                Ok(pid)
            }
            ("make_ref", 0) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_p_i64("mana_rt_make_ref"),
                        &[self.ctx_val().into()],
                        "r",
                    )
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
                // monitor(process, Pid). The code does not check the first
                // argument. It assumes the atom 'process'.
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
                self.builder
                    .build_unconditional_branch(target)
                    .map_err(be)?;
                self.builder.position_at_end(ok_bb);
                Ok(r)
            }
            ("process_flag", 2) => {
                // The runtime dispatches on the flag name. Only trap_exit has
                // an effect. The runtime accepts the other flags, does
                // nothing, and returns a plausible old value.
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
                // system_flag/2 sets VM tuning options. The runtime accepts
                // the known flags and does nothing. An unknown flag raises badarg.
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
                // The options of send/3 (noconnect, nosuspend) only matter for
                // distribution. The code ignores them. send/3 returns ok, not
                // the message.
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
                let helper = if argv.len() == 3 {
                    "mana_rt_apply3"
                } else {
                    "mana_rt_apply_fun"
                };
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
                let call = self
                    .builder
                    .build_call(callee, &cargs, "apply")
                    .map_err(be)?;
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
                        // spawn_link/3 passes the option list [link].
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
                    self.i64t
                        .fn_type(&[BasicMetadataTypeEnum::PointerType(self.ptrt)], false)
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
                // The option list holds flush, or info, or both. The code
                // does not inspect the list, because callers pass a constant
                // list in practice. It always flushes. The return value for
                // info is an approximation: it is always true.
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
            ("monotonic_time", 0)
            | ("monotonic_time", 1)
            | ("system_time", 0)
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
                // memory/0 reports allocator statistics for the heaps of this
                // runtime. The values differ from the values that BEAM reports.
                let call = self
                    .builder
                    .build_call(
                        self.rt_fn("mana_rt_memory", || {
                            self.i64t
                                .fn_type(&[BasicMetadataTypeEnum::PointerType(self.ptrt)], false)
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
            // The runtime collects garbage on its own schedule. garbage_collect/1
            // starts no collection and reports success.
            ("garbage_collect", 1) => self.atom_term("true"),
            ("is_port", 1) => self.atom_term("false"),
            // There is no distribution. Every process lives on nonode@nohost.
            ("node", 0) | ("node", 1) => self.atom_term("nonode@nohost"),
            ("nodes", 0) | ("nodes", 1) => Ok(self.nil()),
            ("is_alive", 0) => self.atom_term("false"),
            _ => return Ok(None),
        };
        v.map(Some)
    }
}
