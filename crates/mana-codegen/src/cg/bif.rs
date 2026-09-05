use crate::*;

impl<'ctx, 'p> Cg<'ctx, 'p> {
    /// Lower a call to a BIF module (`erlang`, `maps`, `file`, ...).
    ///
    /// Calls into modules other than `erlang` go to their own lowering
    /// method first. The `erlang` BIFs live in `bif_erlang.rs` as family
    /// methods that return `None` when they do not know the (name, arity)
    /// pair. No pair belongs to two families, so the chain order does not
    /// matter. Arguments are evaluated once, before the chain.
    ///
    /// Arithmetic can allocate bignums, but through `alloc_shared`. That is
    /// never a GC point, so the may-gc analysis does not change.
    pub(crate) fn compile_bif(
        &self,
        f: FunctionValue<'ctx>,
        module: &str,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        if module == "maps" {
            return self.compile_maps_bif(f, name, args, scope);
        }
        if module == "gen_tcp" || module == "inet" {
            return self.compile_tcp_bif(f, module, name, args, scope);
        }
        if module == "crypto" {
            return self.compile_crypto_bif(f, name, args, scope);
        }
        if module == "io" {
            return self.compile_io_bif(f, name, args, scope);
        }
        if module == "unicode" {
            return self.compile_unicode_bif(f, name, args, scope);
        }
        if module == "persistent_term" {
            return self.compile_pt_bif(f, name, args, scope);
        }
        if module == "code" {
            return self.compile_code_bif(f, name, args, scope);
        }
        if module == "io_lib" {
            return self.compile_io_lib_bif(f, name, args, scope);
        }
        if module == "math" {
            return self.compile_math_bif(f, name, args, scope);
        }
        if module == "re" {
            return self.compile_re_bif(f, name, args, scope);
        }
        if module == "timer" {
            // no timer server in a static binary: start is a no-op, tc is
            // native; send_after/apply_after wait for the timers milestone
            let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
            return match (name, argv.len()) {
                ("start", 0) | ("start_link", 0) => self.atom_term("ok"),
                // unit helpers: N * 1000^k as small-int arithmetic
                ("seconds", 1) | ("minutes", 1) | ("hours", 1) => {
                    let factor: u64 = match name {
                        "seconds" => 1000,
                        "minutes" => 60 * 1000,
                        _ => 60 * 60 * 1000,
                    };
                    self.arith_fastslow(
                        f,
                        "*",
                        2, // AR_MUL
                        argv[0],
                        Some(self.i64t.const_int((factor << 3) | 0b001, false)),
                    )
                }
                ("tc", 1) => {
                    let call = self
                        .builder
                        .build_call(
                            self.rt_ptt_i64("mana_rt_timer_tc"),
                            &[self.ctx_val().into(), argv[0].into(), self.nil().into()],
                            "tc",
                        )
                        .map_err(be)?;
                    let v = call_result(call)?.into_int_value();
                    self.check_exc(f, v)
                }
                ("tc", 2) => {
                    let call = self
                        .builder
                        .build_call(
                            self.rt_ptt_i64("mana_rt_timer_tc"),
                            &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                            "tc",
                        )
                        .map_err(be)?;
                    let v = call_result(call)?.into_int_value();
                    self.check_exc(f, v)
                }
                _ => Err(format!("unsupported BIF timer:{}/{}", name, argv.len())),
            };
        }
        if module == "ets" {
            return self.compile_ets_bif(f, name, args, scope);
        }
        if module == "application" {
            return self.compile_application_bif(f, name, args, scope);
        }
        if module == "net_kernel" && name == "monitor_nodes" {
            // single node, forever: subscribing to node events is a no-op
            // (pg's init calls this — the rest of net_kernel keeps raising)
            self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
            return self.atom_term("ok");
        }
        if module == "zlib" {
            if let Some(v) = self.compile_zlib_bif(f, name, args, scope)? {
                return Ok(v);
            }
            // unhandled zlib names fall through to the raise arm below
        }
        if matches!(
            module,
            "erts_internal" | "elixir_erl" | "erl_eval" | "beam_lib" | "global"
                | "global_group" | "net_kernel" | "zlib"
        ) {
            // BEAM/compiler/distribution guts: compile the call as a runtime
            // raise instead of poisoning the whole caller — reached code
            // often only touches these on branches that never run
            // (GenServer.whereis' {global, Name} arm, ...). Args evaluated.
            self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
            let module_atom = self.atom_term(module)?;
            let reason = self.eternal_pair("unsupported", module_atom)?;
            let class = self.atom_term("error")?;
            let ctx = self.ctx_val();
            self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
            self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
            let target = self.unwind_target(f)?;
            self.builder.build_unconditional_branch(target).map_err(be)?;
            let dead = self.ctx.append_basic_block(f, "unsup.dead");
            self.builder.position_at_end(dead);
            return Ok(self.i64t.get_undef());
        }
        if (module == "file") && name == "sendfile" && args.len() == 5 {
            // read-at + parking send loop in the runtime (Plug.Static)
            let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
            let call = self
                .builder
                .build_call(
                    self.rt_fn("mana_rt_sendfile", || {
                        self.i64t.fn_type(
                            &[
                                BasicMetadataTypeEnum::PointerType(self.ptrt),
                                BasicMetadataTypeEnum::IntType(self.i64t),
                                BasicMetadataTypeEnum::IntType(self.i64t),
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
                        argv[3].into(),
                        argv[4].into(),
                    ],
                    "sf",
                )
                .map_err(be)?;
            let v = call_result(call)?.into_int_value();
            return self.check_exc(f, v);
        }
        if module == "file" || module == "prim_file" {
            // native file cut (OTP's file.erl/prim_file never compiled) —
            // implemented names dispatch to mana_rt_file by opcode; the
            // rest keep answering {error, enotsup}. prim_file shares the
            // table (Plug.Static stats files through it directly).
            let op: Option<u64> = match (name, args.len()) {
                ("read_file", 1) => Some(0),
                ("write_file", 2) => Some(1),
                ("write_file", 3) => Some(2),
                ("open", 2) => Some(3),
                ("close", 1) => Some(4),
                ("read", 2) => Some(5),
                ("write", 2) => Some(6),
                ("position", 2) => Some(7),
                ("delete", 1) => Some(8),
                ("rename", 2) => Some(9),
                ("make_dir", 1) => Some(10),
                ("del_dir", 1) => Some(11),
                ("list_dir", 1) | ("list_dir_all", 1) => Some(12),
                ("read_file_info", 1) | ("read_link_info", 1) => Some(13),
                ("read_file_info", 2) | ("read_link_info", 2) => Some(14),
                ("copy", 2) => Some(15),
                ("get_cwd", 0) => Some(16),
                _ => None,
            };
            let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
            if let Some(op) = op {
                let callee = self.rt_fn("mana_rt_file", || {
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
                let zero = self.i64t.const_zero();
                let arg = |i: usize| -> IntValue<'ctx> {
                    argv.get(i).copied().unwrap_or(zero)
                };
                let call = self
                    .builder
                    .build_call(
                        callee,
                        &[
                            self.ctx_val().into(),
                            self.i64t.const_int(op, false).into(),
                            arg(0).into(),
                            arg(1).into(),
                            arg(2).into(),
                        ],
                        "fileop",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                return self.check_exc(f, v);
            }
            let p = self.alloc_words(3)?;
            let header = self.i64t.const_int((2 << 8) | KIND_TUPLE, false);
            self.store_word(p, 0, header)?;
            let e = self.atom_term("error")?;
            self.store_word(p, 1, e)?;
            let reason = self.atom_term("enotsup")?;
            self.store_word(p, 2, reason)?;
            return self
                .builder
                .build_ptr_to_int(p, self.i64t, "fileerr")
                .map_err(be);
        }
        if module == "logger" {
            // logging is disabled in mana binaries: allow/2 says no (which
            // prunes every emit path), everything else is an ok no-op —
            // TODO(logger): a real stderr handler. Args still evaluated.
            self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
            return match name {
                "allow" => self.atom_term("false"),
                // Logger.metadata cases on undefined | map
                "get_process_metadata" => self.atom_term("undefined"),
                _ => self.atom_term("ok"),
            };
        }
        // raising BIFs: reason terms use the eternal allocator so raise
        // paths don't create GC points
        if matches!(
            (name, args.len()),
            ("error", 1) | ("error", 2) | ("exit", 1) | ("throw", 1)
        ) {
            self.compile_raise(f, name, args, scope)?;
            return Ok(self.i64t.get_undef());
        }
        if name == "error" && args.len() == 3 {
            // error/3: the error_info options only affect stacktrace
            // decoration — TODO(stacktraces)
            self.compile_raise(f, "error", &args[..1], scope)?;
            return Ok(self.i64t.get_undef());
        }
        if name == "nif_error" {
            // a nif stub without a native override: raise like error/1
            self.compile_raise(f, "error", &args[..1], scope)?;
            return Ok(self.i64t.get_undef());
        }

        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;

        if let Some(v) = self.bif_arith(f, name, &argv)? {
            return Ok(v);
        }
        if let Some(v) = self.bif_process(f, name, &argv)? {
            return Ok(v);
        }
        if let Some(v) = self.bif_type_tests(f, name, &argv)? {
            return Ok(v);
        }
        if let Some(v) = self.bif_pdict_timers(f, name, &argv)? {
            return Ok(v);
        }
        if let Some(v) = self.bif_system(f, name, &argv)? {
            return Ok(v);
        }
        if let Some(v) = self.bif_binaries(f, name, &argv)? {
            return Ok(v);
        }
        if let Some(v) = self.bif_lists_tuples_maps(f, name, &argv)? {
            return Ok(v);
        }
        Err(format!("unsupported BIF erlang:{}/{}", name, argv.len()))
    }
}
