use crate::*;

impl<'ctx, 'p> Cg<'ctx, 'p> {
    /// The io_lib cut. The format engine runs in the runtime and returns
    /// charlists.
    pub(crate) fn compile_io_lib_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        let call = match (name, argv.len()) {
            ("format", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_io_lib_format"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "ilf",
                )
                .map_err(be)?,
            ("write", 1) | ("write", 2) => self
                .builder
                .build_call(
                    self.rt_pt_i64("mana_rt_io_lib_write"),
                    &[self.ctx_val().into(), argv[0].into()],
                    "ilw",
                )
                .map_err(be)?,
            _ => return Err(format!("unsupported BIF io_lib:{}/{}", name, argv.len())),
        };
        let v = call_result(call)?.into_int_value();
        self.check_exc(f, v)
    }

    /// The re cut runs on the Rust regex crate. version() returns "mana".
    /// With that version, Elixir's Regex recompiles each regex from source.
    /// It does not trust the PCRE blobs that sigils bake in.
    pub(crate) fn compile_re_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        let trip = |helper: &str| {
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
        };
        let call = match (name, argv.len()) {
            ("version", 0) => return self.compile_binary_const_term(f, b"mana", scope),
            ("run", 2) => self
                .builder
                .build_call(
                    trip("mana_rt_re_run"),
                    &[
                        self.ctx_val().into(),
                        argv[0].into(),
                        argv[1].into(),
                        self.nil().into(),
                    ],
                    "rerun",
                )
                .map_err(be)?,
            ("run", 3) => self
                .builder
                .build_call(
                    trip("mana_rt_re_run"),
                    &[
                        self.ctx_val().into(),
                        argv[0].into(),
                        argv[1].into(),
                        argv[2].into(),
                    ],
                    "rerun",
                )
                .map_err(be)?,
            ("compile", 1) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_re_compile"),
                    &[self.ctx_val().into(), argv[0].into(), self.nil().into()],
                    "rec",
                )
                .map_err(be)?,
            ("compile", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_re_compile"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "rec",
                )
                .map_err(be)?,
            ("inspect", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_re_inspect"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "rei",
                )
                .map_err(be)?,
            _ => return Err(format!("unsupported BIF re:{}/{}", name, argv.len())),
        };
        let v = call_result(call)?.into_int_value();
        self.check_exc(f, v)
    }

    /// The math cut. The f64 operations run in the runtime. box_float is
    /// never a GC point.
    pub(crate) fn compile_math_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        let op: u64 = match (name, argv.len()) {
            ("sqrt", 1) => 0,
            ("pow", 2) => 1,
            ("log", 1) => 2,
            ("log2", 1) => 3,
            ("log10", 1) => 4,
            ("exp", 1) => 5,
            ("sin", 1) => 6,
            ("cos", 1) => 7,
            ("tan", 1) => 8,
            ("asin", 1) => 9,
            ("acos", 1) => 10,
            ("atan", 1) => 11,
            ("atan2", 2) => 12,
            ("fmod", 2) => 13,
            ("pi", 0) => 14,
            ("floor", 1) => 15,
            ("ceil", 1) => 16,
            _ => return Err(format!("unsupported BIF math:{}/{}", name, argv.len())),
        };
        let dummy = self.i64t.const_int(1, false); // the small integer 0
        let a = argv.first().copied().unwrap_or(dummy);
        let b = argv.get(1).copied().unwrap_or(dummy);
        let callee = self.rt_fn("mana_rt_math", || {
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
                    self.i64t.const_int(op, false).into(),
                    a.into(),
                    b.into(),
                ],
                "math",
            )
            .map_err(be)?;
        let v = call_result(call)?.into_int_value();
        self.check_exc(f, v)
    }

    /// The zlib cut: streaming compression over miniz_oxide. A handled name
    /// returns Some(result). An unknown zlib function returns None, and the
    /// caller falls through to the runtime-raise arm. Handle terms are
    /// opaque {mana_zlib, N} tuples.
    pub(crate) fn compile_zlib_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<Option<IntValue<'ctx>>> {
        let arity = args.len();
        // The runtime function type for n terms: a ctx pointer, then n i64 terms.
        let ty = |n: usize| {
            let mut params: Vec<BasicMetadataTypeEnum> =
                vec![BasicMetadataTypeEnum::PointerType(self.ptrt)];
            params.extend((0..n).map(|_| BasicMetadataTypeEnum::IntType(self.i64t)));
            self.i64t.fn_type(&params, false)
        };
        let small = |v: i64| self.i64t.const_int(((v << 3) as u64) | 0b001, false);

        // A plan is (runtime symbol, count of call args to pass, extra terms).
        // The extra terms go after the evaluated call args.
        let plan: Option<(&str, usize, Vec<IntValue<'ctx>>)> = match (name, arity) {
            ("open", 0) => Some(("mana_rt_zlib_open", 0, vec![])),
            ("close", 1) => Some(("mana_rt_zlib_close", 1, vec![])),
            ("inflateInit", 1) => Some(("mana_rt_zlib_inflate_init", 1, vec![small(15)])),
            ("inflateInit", 2) => Some(("mana_rt_zlib_inflate_init", 2, vec![])),
            ("deflateInit", 2) => Some((
                "mana_rt_zlib_deflate_init",
                2,
                vec![small(15), self.atom_term("default")?],
            )),
            // deflateInit/6 takes Z, Level, Method, WindowBits, MemLevel, Strategy.
            // The lowering passes Level(1), WindowBits(3), and Strategy(5).
            // It drops the rest.
            ("deflateInit", 6) => None, // lowered below
            ("deflate", 2) => Some((
                "mana_rt_zlib_deflate",
                2,
                vec![self.atom_term("none")?],
            )),
            ("deflate", 3) => Some(("mana_rt_zlib_deflate", 3, vec![])),
            ("safeInflate", 2) => Some(("mana_rt_zlib_safe_inflate", 2, vec![])),
            ("inflateReset", 1) | ("deflateReset", 1) => Some(("mana_rt_zlib_reset", 1, vec![])),
            ("inflateEnd", 1) | ("deflateEnd", 1) => Some(("mana_rt_zlib_end", 1, vec![])),
            ("gzip", 1) => Some(("mana_rt_zlib_gzip", 1, vec![])),
            ("gunzip", 1) => Some(("mana_rt_zlib_gunzip", 1, vec![])),
            ("compress", 1) => Some(("mana_rt_zlib_compress", 1, vec![small(0)])),
            ("zip", 1) => Some(("mana_rt_zlib_compress", 1, vec![small(1)])),
            ("uncompress", 1) => Some(("mana_rt_zlib_uncompress", 1, vec![small(0)])),
            ("unzip", 1) => Some(("mana_rt_zlib_uncompress", 1, vec![small(1)])),
            _ => return Ok(None),
        };

        if name == "deflateInit" && arity == 6 {
            let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
            let callee = self.rt_fn("mana_rt_zlib_deflate_init", || ty(4));
            let call = self
                .builder
                .build_call(
                    callee,
                    &[
                        self.ctx_val().into(),
                        argv[0].into(), // Z
                        argv[1].into(), // Level
                        argv[3].into(), // WindowBits
                        argv[5].into(), // Strategy
                    ],
                    "zlib",
                )
                .map_err(be)?;
            let v = call_result(call)?.into_int_value();
            return Ok(Some(self.check_exc(f, v)?));
        }

        let Some((sym, nargs, extra)) = plan else {
            return Ok(None);
        };
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        let mut call_args: Vec<BasicMetadataValueEnum> = vec![self.ctx_val().into()];
        for a in argv.iter().take(nargs) {
            call_args.push((*a).into());
        }
        for e in &extra {
            call_args.push((*e).into());
        }
        let callee = self.rt_fn(sym, || ty(nargs + extra.len()));
        let call = self
            .builder
            .build_call(callee, &call_args, "zlib")
            .map_err(be)?;
        let v = call_result(call)?.into_int_value();
        Ok(Some(self.check_exc(f, v)?))
    }

    /// The ets cut: a global key-value store. Only keypos 1 is supported.
    /// Match specs cover the shapes that Registry and Phoenix.PubSub use.
    pub(crate) fn compile_ets_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        let quad = |helper: &str| {
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
        };
        let quint = |helper: &str| {
            self.rt_fn(helper, || {
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
            })
        };
        let call = match (name, argv.len()) {
            // A table is identified by its name term. The runtime parses the
            // option list for the table kind (set, bag, or duplicate_bag).
            ("new", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_ets_new"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "ets",
                )
                .map_err(be)?,
            ("info", 1) => self
                .builder
                .build_call(
                    self.rt_pt_i64("mana_rt_ets_info"),
                    &[self.ctx_val().into(), argv[0].into()],
                    "ets",
                )
                .map_err(be)?,
            ("select", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_ets_select"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "ets",
                )
                .map_err(be)?,
            ("match_delete", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_ets_match_delete"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "ets",
                )
                .map_err(be)?,
            ("insert", 2) | ("insert_new", 2) => self
                .builder
                .build_call(
                    quad("mana_rt_ets_insert"),
                    &[
                        self.ctx_val().into(),
                        argv[0].into(),
                        argv[1].into(),
                        self.i64t
                            .const_int((name == "insert_new") as u64, false)
                            .into(),
                    ],
                    "ets",
                )
                .map_err(be)?,
            ("lookup", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_ets_lookup"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "ets",
                )
                .map_err(be)?,
            ("match", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_ets_match"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "ets",
                )
                .map_err(be)?,
            ("lookup_element", 3) => self
                .builder
                .build_call(
                    quad("mana_rt_ets_lookup_element"),
                    &[
                        self.ctx_val().into(),
                        argv[0].into(),
                        argv[1].into(),
                        argv[2].into(),
                    ],
                    "ets",
                )
                .map_err(be)?,
            ("lookup_element", 4) => self
                .builder
                .build_call(
                    quint("mana_rt_ets_lookup_element4"),
                    &[
                        self.ctx_val().into(),
                        argv[0].into(),
                        argv[1].into(),
                        argv[2].into(),
                        argv[3].into(),
                    ],
                    "ets",
                )
                .map_err(be)?,
            ("delete", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_ets_delete"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "ets",
                )
                .map_err(be)?,
            ("take", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_ets_take"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "ets",
                )
                .map_err(be)?,
            ("member", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_ets_member"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "ets",
                )
                .map_err(be)?,
            ("delete_object", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_ets_delete_object"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "ets",
                )
                .map_err(be)?,
            ("select_count", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_ets_select_count"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "ets",
                )
                .map_err(be)?,
            ("select_delete", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_ets_select_delete"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "ets",
                )
                .map_err(be)?,
            // TODO(ets): whole-table delete returns true and does nothing.
            // Tables die with the process in this closed world.
            ("delete", 1) => return self.atom_term("true"),
            _ => return Err(format!("unsupported BIF ets:{}/{}", name, argv.len())),
        };
        let v = call_result(call)?.into_int_value();
        self.check_exc(f, v)
    }

    /// The application cut: an env store. No application starts.
    pub(crate) fn compile_application_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        let get_env = || {
            self.rt_fn("mana_rt_app_get_env", || {
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
            })
        };
        match (name, argv.len()) {
            ("get_env", 2) => {
                let undef = self.atom_term("undefined")?;
                let call = self
                    .builder
                    .build_call(
                        get_env(),
                        &[
                            self.ctx_val().into(),
                            argv[0].into(),
                            argv[1].into(),
                            undef.into(),
                            self.i64t.const_int(1, false).into(),
                        ],
                        "appenv",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            ("get_env", 3) => {
                let call = self
                    .builder
                    .build_call(
                        get_env(),
                        &[
                            self.ctx_val().into(),
                            argv[0].into(),
                            argv[1].into(),
                            argv[2].into(),
                            self.i64t.const_zero().into(),
                        ],
                        "appenv",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            // The opts of set_env/4 (timeout, persistent) have no effect here.
            ("set_env", 3) | ("set_env", 4) => {
                let callee = self.rt_fn("mana_rt_app_set_env", || {
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
                        "appenv",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("get_key", 2) | ("get_all_key", 1) | ("get_application", 0)
            | ("get_application", 1) => self.atom_term("undefined"),
            _ => Err(format!(
                "unsupported BIF application:{}/{}",
                name,
                argv.len()
            )),
        }
    }

    /// The code cut. A module is "loaded" when it is compiled into this
    /// binary.
    pub(crate) fn compile_code_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        match (name, argv.len()) {
            ("root_dir", 0) | ("lib_dir", 0) => {
                // A static binary has no OTP tree. A plausible path keeps the
                // callers that print headers alive. They only display the path.
                let s = b"/mana";
                let bin = self.compile_binary_const_term(f, s, scope)?;
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_binary_to_list"),
                        &[self.ctx_val().into(), bin.into()],
                        "cl",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("lib_dir", 1) | ("priv_dir", 1) => {
                // The --app boot generator bakes the per-app dirs under the env
                // key {:mana_app_dirs, App}. An app that is not baked gets
                // {error, bad_name}. BEAM returns the same error for an unknown
                // app.
                let is_priv = self.i64t.const_int((name == "priv_dir") as u64, false);
                let call = self
                    .builder
                    .build_call(
                        self.rt_fn("mana_rt_code_app_dir", || {
                            self.i64t.fn_type(
                                &[
                                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                ],
                                false,
                            )
                        }),
                        &[self.ctx_val().into(), argv[0].into(), is_priv.into()],
                        "appdir",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("ensure_loaded", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_code_ensure_loaded"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "cel",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("is_loaded", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_code_is_loaded"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "cil",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            _ => Err(format!("unsupported BIF code:{}/{}", name, argv.len())),
        }
    }

    /// The persistent_term cut: a global table of eternal deep copies.
    pub(crate) fn compile_pt_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        let quad = || {
            self.rt_fn("mana_rt_pt_get", || {
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
        };
        let call = match (name, argv.len()) {
            ("put", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_pt_put"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "ptput",
                )
                .map_err(be)?,
            ("get", 1) => self
                .builder
                .build_call(
                    quad(),
                    &[
                        self.ctx_val().into(),
                        argv[0].into(),
                        self.i64t.const_zero().into(),
                        self.i64t.const_zero().into(),
                    ],
                    "ptget",
                )
                .map_err(be)?,
            ("get", 2) => self
                .builder
                .build_call(
                    quad(),
                    &[
                        self.ctx_val().into(),
                        argv[0].into(),
                        argv[1].into(),
                        self.i64t.const_int(1, false).into(),
                    ],
                    "ptget",
                )
                .map_err(be)?,
            ("info", 0) => self
                .builder
                .build_call(
                    self.rt_fn("mana_rt_pt_info", || {
                        self.i64t.fn_type(
                            &[BasicMetadataTypeEnum::PointerType(self.ptrt)],
                            false,
                        )
                    }),
                    &[self.ctx_val().into()],
                    "ptinfo",
                )
                .map_err(be)?,
            _ => {
                return Err(format!(
                    "unsupported BIF persistent_term:{}/{}",
                    name,
                    argv.len()
                ))
            }
        };
        let v = call_result(call)?.into_int_value();
        self.check_exc(f, v)
    }

    /// The unicode cut. Chardata conversion runs in the runtime and supports
    /// utf8 only. The encoding arguments are evaluated and ignored.
    pub(crate) fn compile_unicode_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        let helper = match (name, argv.len()) {
            ("characters_to_binary", 1..=3) => "mana_rt_unicode_to_binary",
            ("characters_to_list", 1 | 2) => "mana_rt_unicode_to_list",
            ("characters_to_nfc_list", 1) => "mana_rt_unicode_to_nfc_list",
            _ => return Err(format!("unsupported BIF unicode:{}/{}", name, argv.len())),
        };
        let call = self
            .builder
            .build_call(
                self.rt_pt_i64(helper),
                &[self.ctx_val().into(), argv[0].into()],
                "uconv",
            )
            .map_err(be)?;
        let v = call_result(call)?.into_int_value();
        self.check_exc(f, v)
    }

    /// The crypto cut: the Plug.Crypto subset over RustCrypto.
    pub(crate) fn compile_crypto_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let op: u64 = match (name, args.len()) {
            ("strong_rand_bytes", 1) => 0,
            ("hash", 2) => 1,
            ("mac", 4) => 2,
            ("exor", 2) => 3,
            ("pbkdf2_hmac", 5) => 4,
            ("hash_equals", 2) => 5,
            _ => return Err(format!("unsupported BIF crypto:{}/{}", name, args.len())),
        };
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        let callee = self.rt_fn("mana_rt_crypto", || {
            self.i64t.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        });
        let zero = self.i64t.const_zero();
        let arg = |i: usize| -> IntValue<'ctx> { argv.get(i).copied().unwrap_or(zero) };
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
                    arg(3).into(),
                    arg(4).into(),
                ],
                "cryp",
            )
            .map_err(be)?;
        let v = call_result(call)?.into_int_value();
        self.check_exc(f, v)
    }

    /// The gen_tcp/inet cut. Every call routes through mana_rt_tcp by opcode.
    /// recv, accept, connect, and send suspend the caller. They are GC points
    /// and raise points.
    pub(crate) fn compile_tcp_bif(
        &self,
        f: FunctionValue<'ctx>,
        module: &str,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        // A spec is (opcode, append infinity as the missing timeout argument).
        let spec: Option<(u64, bool)> = match (module, name, args.len()) {
            ("gen_tcp", "connect", 3) => Some((0, true)),
            ("gen_tcp", "connect", 4) => Some((0, false)),
            ("gen_tcp", "listen", 2) => Some((1, false)),
            ("gen_tcp", "accept", 1) => Some((2, true)),
            ("gen_tcp", "accept", 2) => Some((2, false)),
            ("gen_tcp", "recv", 2) => Some((3, true)),
            ("gen_tcp", "recv", 3) => Some((3, false)),
            ("gen_tcp", "send", 2) => Some((4, false)),
            ("gen_tcp", "close", 1) => Some((5, false)),
            ("gen_tcp", "shutdown", 2) => Some((6, false)),
            ("gen_tcp", "controlling_process", 2) => Some((11, false)),
            ("inet", "setopts", 2) => Some((7, false)),
            ("inet", "peername", 1) => Some((8, false)),
            ("inet", "sockname", 1) => Some((9, false)),
            ("inet", "port", 1) => Some((10, false)),
            ("inet", "getstat", 1) => Some((12, false)),
            ("inet", "getstat", 2) => Some((12, false)),
            ("inet", "getopts", 2) => Some((13, false)),
            _ => None,
        };
        let Some((op, pad_infinity)) = spec else {
            return Err(format!("unsupported BIF {}:{}/{}", module, name, args.len()));
        };
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        let callee = self.rt_fn("mana_rt_tcp", || {
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
        });
        let infinity = self.atom_term("infinity")?;
        let zero = self.i64t.const_zero();
        let mut slots: Vec<IntValue<'ctx>> = argv.clone();
        if pad_infinity {
            slots.push(infinity);
        }
        while slots.len() < 4 {
            slots.push(zero);
        }
        let call = self
            .builder
            .build_call(
                callee,
                &[
                    self.ctx_val().into(),
                    self.i64t.const_int(op, false).into(),
                    slots[0].into(),
                    slots[1].into(),
                    slots[2].into(),
                    slots[3].into(),
                ],
                "tcpop",
            )
            .map_err(be)?;
        let v = call_result(call)?.into_int_value();
        self.check_exc(f, v)
    }

    /// The native io cut: stdout only. It bypasses the group-leader io
    /// protocol of OTP. io.erl is never compiled.
    pub(crate) fn compile_io_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        match (name, argv.len()) {
            // Only stdout is supported. The device arg (for example
            // standard_io) is evaluated and ignored.
            ("put_chars", 1) | ("put_chars", 2) => {
                let data = *argv.last().unwrap();
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_io_put_chars"),
                        &[self.ctx_val().into(), data.into()],
                        "ioput",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("format", 2) | ("format", 3) => {
                // The first arg of format/3 is the device. It is ignored, as in
                // put_chars/2.
                let (fmt, fargs) = if argv.len() == 3 {
                    (argv[1], argv[2])
                } else {
                    (argv[0], argv[1])
                };
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_io_format"),
                        &[self.ctx_val().into(), fmt.into(), fargs.into()],
                        "iofmt",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("nl", 0) => {
                let nl = self.compile_binary_const_term(f, b"\n", scope)?;
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_io_put_chars"),
                        &[self.ctx_val().into(), nl.into()],
                        "ionl",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            _ => Err(format!("unsupported BIF io:{}/{}", name, argv.len())),
        }
    }

    /// The `timer` module. A static binary has no timer server.
    pub(crate) fn compile_timer_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        // A static binary has no timer server. start is a no-op and tc is
        // native. send_after and apply_after wait for the timers milestone.
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        return match (name, argv.len()) {
            ("start", 0) | ("start_link", 0) => self.atom_term("ok"),
            // The unit helpers compute N * 1000^k with small-int arithmetic.
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

    /// The `file` and `prim_file` modules: the native file cut.
    pub(crate) fn compile_file_bif(
        &self,
        f: FunctionValue<'ctx>,
        module: &str,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        if module == "file" && name == "sendfile" && args.len() == 5 {
            // The runtime runs a read-at and parking send loop. Plug.Static
            // uses this.
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
        // The native file cut. OTP's file.erl and prim_file are never
        // compiled. An implemented name dispatches to mana_rt_file by
        // opcode. Every other name returns {error, enotsup}. prim_file
        // shares the table because Plug.Static stats files through it
        // directly.
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
}
