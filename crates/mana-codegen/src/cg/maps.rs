use crate::*;

/// Erlang term order for the literal keys that the presorted-map-literal path
/// accepts: numbers < atoms < nil. Nil is the empty list, and lists sort after
/// maps. Atoms compare by name bytes. This is the same order as the atom_bytes
/// memcmp in mana_rt_compare in the runtime.
pub(crate) fn lit_key_ord(a: &Literal, b: &Literal) -> std::cmp::Ordering {
    fn rank(l: &Literal) -> u8 {
        match l {
            Literal::Int(_) => 0,
            Literal::Atom(_) => 1,
            Literal::Nil => 2,
            _ => unreachable!("non-immediate literal map key"),
        }
    }
    match (a, b) {
        (Literal::Int(x), Literal::Int(y)) => x.cmp(y),
        (Literal::Atom(x), Literal::Atom(y)) => x.as_bytes().cmp(y.as_bytes()),
        _ => rank(a).cmp(&rank(b)),
    }
}

impl<'ctx, 'p> Cg<'ctx, 'p> {
    /// Inline flatmap lookup for a key whose equality is bit identity
    /// (atoms, smalls, nil). The caller must already know that the subject is a map.
    /// A miss branches to `fail`. The hit path returns the value.
    pub(crate) fn inline_map_get(
        &self,
        f: FunctionValue<'ctx>,
        subject: IntValue<'ctx>,
        key: IntValue<'ctx>,
        fail: BasicBlock<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let p = self
            .builder
            .build_int_to_ptr(subject, self.ptrt, "map.ptr")
            .map_err(be)?;
        let header = self.load_word(p, 0)?;
        let n = self
            .builder
            .build_right_shift(header, self.i64t.const_int(8, false), false, "map.n")
            .map_err(be)?;
        let entry = self.builder.get_insert_block().unwrap();
        let head = self.ctx.append_basic_block(f, "mg.head");
        let body = self.ctx.append_basic_block(f, "mg.body");
        let next = self.ctx.append_basic_block(f, "mg.next");
        let hit = self.ctx.append_basic_block(f, "mg.hit");
        self.builder.build_unconditional_branch(head).map_err(be)?;

        self.builder.position_at_end(head);
        let i = self.builder.build_phi(self.i64t, "mg.i").map_err(be)?;
        i.add_incoming(&[(&self.i64t.const_zero(), entry)]);
        let iv = i.as_basic_value().into_int_value();
        let done = self
            .builder
            .build_int_compare(IntPredicate::UGE, iv, n, "mg.done")
            .map_err(be)?;
        self.builder
            .build_conditional_branch(done, fail, body)
            .map_err(be)?;

        self.builder.position_at_end(body);
        let one = self.i64t.const_int(1, false);
        let koff = self.builder.build_int_add(one, iv, "mg.ko").map_err(be)?;
        let kptr = unsafe {
            self.builder
                .build_in_bounds_gep(self.i64t, p, &[koff], "mg.kp")
                .map_err(be)?
        };
        let kw = self
            .builder
            .build_load(self.i64t, kptr, "mg.k")
            .map_err(be)?
            .into_int_value();
        let eq = self
            .builder
            .build_int_compare(IntPredicate::EQ, kw, key, "mg.eq")
            .map_err(be)?;
        self.builder
            .build_conditional_branch(eq, hit, next)
            .map_err(be)?;

        self.builder.position_at_end(next);
        let inext = self.builder.build_int_add(iv, one, "mg.inc").map_err(be)?;
        i.add_incoming(&[(&inext, next)]);
        self.builder.build_unconditional_branch(head).map_err(be)?;

        self.builder.position_at_end(hit);
        let voff = self
            .builder
            .build_int_add(self.builder.build_int_add(one, n, "mg.vb").map_err(be)?, iv, "mg.vo")
            .map_err(be)?;
        let vptr = unsafe {
            self.builder
                .build_in_bounds_gep(self.i64t, p, &[voff], "mg.vp")
                .map_err(be)?
        };
        Ok(self
            .builder
            .build_load(self.i64t, vptr, "mg.v")
            .map_err(be)?
            .into_int_value())
    }

    pub(crate) fn compile_maps_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        let ctxv: BasicMetadataValueEnum = self.ctx_val().into();
        match (name, argv.len()) {
            ("get", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_map_get"),
                        &[ctxv, argv[0].into(), argv[1].into()],
                        "mg",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("get", 3) => {
                // A miss or a non-map yields the default. TODO(badmap): a
                // non-map must raise.
                let call = self
                    .builder
                    .build_call(
                        self.rt_tt_i64("mana_rt_map_pat_get"),
                        &[argv[1].into(), argv[0].into()],
                        "mg3",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                let miss = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, v, self.sentinel(), "mg3.m")
                    .map_err(be)?;
                Ok(self
                    .builder
                    .build_select(miss, argv[2], v, "mg3.v")
                    .map_err(be)?
                    .into_int_value())
            }
            ("find", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_tt_i64("mana_rt_map_pat_get"),
                        &[argv[1].into(), argv[0].into()],
                        "mf",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                let miss = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, v, self.sentinel(), "mf.m")
                    .map_err(be)?;
                let hit_bb = self.ctx.append_basic_block(f, "mf.hit");
                let miss_bb = self.ctx.append_basic_block(f, "mf.miss");
                let merge = self.ctx.append_basic_block(f, "mf.merge");
                self.builder
                    .build_conditional_branch(miss, miss_bb, hit_bb)
                    .map_err(be)?;
                self.builder.position_at_end(hit_bb);
                // The {ok, V} tuple needs an allocation. Root v in a temporary slot first.
                let vslot = if self.framed() { Some(self.spill(v)?) } else { None };
                let p = self.alloc_words(3)?;
                self.store_word(p, 0, self.i64t.const_int((2 << 8) | KIND_TUPLE, false))?;
                let ok_atom = self.atom_term("ok")?;
                self.store_word(p, 1, ok_atom)?;
                let v2 = match vslot {
                    Some(s) => self.reload(s)?,
                    None => v,
                };
                self.store_word(p, 2, v2)?;
                let tup = self
                    .builder
                    .build_ptr_to_int(p, self.i64t, "mf.t")
                    .map_err(be)?;
                let hit_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(merge).map_err(be)?;
                self.builder.position_at_end(miss_bb);
                let err_atom = self.atom_term("error")?;
                self.builder.build_unconditional_branch(merge).map_err(be)?;
                self.builder.position_at_end(merge);
                let phi = self.builder.build_phi(self.i64t, "mf.v").map_err(be)?;
                phi.add_incoming(&[(&tup, hit_end), (&err_atom, miss_bb)]);
                Ok(phi.as_basic_value().into_int_value())
            }
            ("put", 3) => {
                let callee = self.rt_fn("mana_rt_map_put", || {
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
                        &[ctxv, argv[0].into(), argv[1].into(), argv[2].into()],
                        "mp",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("is_key", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_map_is_key"),
                        &[ctxv, argv[0].into(), argv[1].into()],
                        "mk",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("remove", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_map_remove"),
                        &[ctxv, argv[0].into(), argv[1].into()],
                        "mr",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("merge", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_map_merge"),
                        &[ctxv, argv[0].into(), argv[1].into()],
                        "mm",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("from_list", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_map_from_list"),
                        &[ctxv, argv[0].into()],
                        "mfl",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("to_list", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_map_to_list"),
                        &[ctxv, argv[0].into()],
                        "mtl",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("size", 1) => self.map_size_of(f, argv[0]),
            ("iterator", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_map_iterator"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "miter",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("next", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_map_next"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "mnext",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("keys", 1) | ("values", 1) => {
                let callee = self.rt_fn("mana_rt_map_keys", || {
                    self.i64t.fn_type(
                        &[
                            BasicMetadataTypeEnum::PointerType(self.ptrt),
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
                            self.i64t
                                .const_int((name == "values") as u64, false)
                                .into(),
                        ],
                        "mkeys",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("update", 3) => {
                // update(K, V, M): the key must exist. A missing key raises badkey.
                let callee = self.rt_fn("mana_rt_map_update_exact", || {
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
                        "mupd",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("take", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_map_take"),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "mtake",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("with", 2) | ("without", 2) => {
                let callee = self.rt_fn("mana_rt_maps_with", || {
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
                            self.i64t
                                .const_int((name == "with") as u64, false)
                                .into(),
                        ],
                        "mw",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("foreach", 2) => {
                let callee = self.rt_fn("mana_rt_maps_foreach", || {
                    self.i64t.fn_type(
                        &[
                            BasicMetadataTypeEnum::PointerType(self.ptrt),
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
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "mfe",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("update_with", 4) => {
                let callee = self.rt_fn("mana_rt_maps_update_with4", || {
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
                            argv[3].into(),
                        ],
                        "muw4",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("update_with", 3) => {
                let callee = self.rt_fn("mana_rt_maps_update_with", || {
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
                        "muw",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("merge_with", 3) => {
                let callee = self.rt_fn("mana_rt_maps_merge_with", || {
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
                        "mmw",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("fold", 3) => {
                // Argument order: fold(Fun, Acc, Map).
                let callee = self.rt_fn("mana_rt_maps_fold", || {
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
                        "mfold",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            _ => Err(format!("unsupported BIF maps:{}/{}", name, argv.len())),
        }
    }

    pub(crate) fn map_size_of(
        &self,
        f: FunctionValue<'ctx>,
        m: IntValue<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let is_map = self.kind_test(f, m, |s, header| {
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
        self.guard_badarg(f, is_map)?;
        let p = self
            .builder
            .build_int_to_ptr(m, self.ptrt, "ms.p")
            .map_err(be)?;
        let header = self.load_word(p, 0)?;
        let n = self
            .builder
            .build_right_shift(header, self.i64t.const_int(8, false), false, "ms.n")
            .map_err(be)?;
        self.retag_int(n)
    }
}
