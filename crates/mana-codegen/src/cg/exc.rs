use crate::*;

impl<'ctx, 'p> Cg<'ctx, 'p> {
    pub(crate) fn sentinel(&self) -> IntValue<'ctx> {
        self.i64t.const_int(EXC_SENTINEL, false)
    }

    /// The block where an unwinding exception goes: the innermost try
    /// handler, or the per-function propagate block. The propagate block
    /// unlinks the frame and returns the sentinel.
    pub(crate) fn unwind_target(&self, f: FunctionValue<'ctx>) -> CgResult<BasicBlock<'ctx>> {
        if let Some(h) = self.handlers.borrow().last() {
            return Ok(*h);
        }
        if let Some(bb) = self.propagate_bb.get() {
            return Ok(bb);
        }
        let saved = self.builder.get_insert_block();
        let bb = self.ctx.append_basic_block(f, "unwind");
        self.builder.position_at_end(bb);
        self.pop_frame()?;
        self.builder.build_return(Some(&self.sentinel())).map_err(be)?;
        if let Some(s) = saved {
            self.builder.position_at_end(s);
        }
        self.propagate_bb.set(Some(bb));
        Ok(bb)
    }

    /// Store the class and the reason into the ctx and jump to the unwind
    /// target. This leaves the builder in a fresh dead block.
    pub(crate) fn emit_raise(
        &self,
        f: FunctionValue<'ctx>,
        class: IntValue<'ctx>,
        reason: IntValue<'ctx>,
    ) -> CgResult<()> {
        // A minimal stacktrace substitute for raises (MANA_DEBUG_RAISE).
        let site = format!("{}:{}", self.module_name, f.get_name().to_string_lossy());
        let ptr = self.static_bytes(site.as_bytes())?;
        self.builder
            .build_call(
                self.rt_fn("mana_rt_note_raise", || {
                    self.ctx.void_type().fn_type(
                        &[
                            BasicMetadataTypeEnum::PointerType(self.ptrt),
                            BasicMetadataTypeEnum::IntType(self.i64t),
                            BasicMetadataTypeEnum::IntType(self.i64t),
                        ],
                        false,
                    )
                }),
                &[
                    ptr.into(),
                    self.i64t.const_int(site.len() as u64, false).into(),
                    reason.into(),
                ],
                "",
            )
            .map_err(be)?;
        let ctx = self.ctx_val();
        self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
        self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
        let target = self.unwind_target(f)?;
        self.builder.build_unconditional_branch(target).map_err(be)?;
        let dead = self.ctx.append_basic_block(f, "dead");
        self.builder.position_at_end(dead);
        Ok(())
    }

    /// After a call to a function that can raise: branch to the unwind
    /// target if the call returned the sentinel.
    pub(crate) fn check_exc(
        &self,
        f: FunctionValue<'ctx>,
        ret: IntValue<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let is_exc = self
            .builder
            .build_int_compare(IntPredicate::EQ, ret, self.sentinel(), "is.exc")
            .map_err(be)?;
        let target = self.unwind_target(f)?;
        let cont = self.ctx.append_basic_block(f, "call.ok");
        self.builder
            .build_conditional_branch(is_exc, target, cont)
            .map_err(be)?;
        self.builder.position_at_end(cont);
        Ok(ret)
    }

    /// Bind the try-catch variables: `<Class, Reason, Stk>` (3), `<Class,
    /// Reason>` (2) or `<Reason>` (1). The stacktrace slot carries the class
    /// atom, so `primop raise(Stk, Reason)` re-raises with the correct class.
    /// TODO(stacktraces): the slot does not hold a real stacktrace.
    pub(crate) fn bind_try_evars(
        &self,
        scope: &mut Scope<'ctx>,
        evars: &[String],
        class: IntValue<'ctx>,
        reason: IntValue<'ctx>,
    ) -> CgResult<()> {
        match evars.len() {
            1 => self.bind_var(scope, &evars[0], reason),
            2 => {
                self.bind_var(scope, &evars[0], class)?;
                self.bind_var(scope, &evars[1], reason)
            }
            3 => {
                self.bind_var(scope, &evars[0], class)?;
                self.bind_var(scope, &evars[1], reason)?;
                self.bind_var(scope, &evars[2], class)
            }
            n => Err(format!("try with {} catch variables is not supported", n)),
        }
    }

    /// If `ok` is false, branch to a fresh block that raises `error:badarg`.
    pub(crate) fn guard_badarg(
        &self,
        f: FunctionValue<'ctx>,
        ok: IntValue<'ctx>,
    ) -> CgResult<()> {
        let bad = self.ctx.append_basic_block(f, "badarg");
        let cont = self.ctx.append_basic_block(f, "ok");
        self.builder
            .build_conditional_branch(ok, cont, bad)
            .map_err(be)?;
        self.builder.position_at_end(bad);
        // A minimal stacktrace substitute: MANA_DEBUG_BADARG names the
        // function that raises. This is a cold path. The call costs nothing
        // unless the function raises.
        let site = format!(
            "{}:{}",
            self.module_name,
            f.get_name().to_string_lossy()
        );
        let ptr = self.static_bytes(site.as_bytes())?;
        self.builder
            .build_call(
                self.rt_fn("mana_rt_note_badarg", || {
                    self.ctx.void_type().fn_type(
                        &[
                            BasicMetadataTypeEnum::PointerType(self.ptrt),
                            BasicMetadataTypeEnum::IntType(self.i64t),
                        ],
                        false,
                    )
                }),
                &[
                    ptr.into(),
                    self.i64t.const_int(site.len() as u64, false).into(),
                ],
                "",
            )
            .map_err(be)?;
        let class = self.atom_term("error")?;
        let reason = self.atom_term("badarg")?;
        let ctx = self.ctx_val();
        self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
        self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
        let target = self.unwind_target(f)?;
        self.builder.build_unconditional_branch(target).map_err(be)?;
        self.builder.position_at_end(cont);
        Ok(())
    }

    pub(crate) fn compile_raise(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<()> {
        let was = self.eternal_alloc.replace(true);
        let result: CgResult<(IntValue<'ctx>, IntValue<'ctx>)> = (|| {
            let (class, reason) = match name {
                // primop raise(Stk, Reason) is a re-raise. The "stacktrace" slot
                // carries the class atom. TODO(stacktraces): the slot does not
                // hold a real stacktrace.
                "raise" if args.len() == 2 => {
                    let class = self.compile_value(f, &args[0], scope)?;
                    let reason = self.compile_value(f, &args[1], scope)?;
                    (class, reason)
                }
                "exit" => {
                    let reason = match args.first() {
                        Some(a) => self.compile_value(f, a, scope)?,
                        None => self.nil(),
                    };
                    (self.atom_term("exit")?, reason)
                }
                "throw" => {
                    let reason = match args.first() {
                        Some(a) => self.compile_value(f, a, scope)?,
                        None => self.nil(),
                    };
                    (self.atom_term("throw")?, reason)
                }
                // match_fail, error, and anything else: class error. BEAM
                // reports function_clause as a bare atom. The args go into the
                // stacktrace, which is not built yet.
                _ => {
                    let reason = match args.first() {
                        Some(Expr::Tuple(items))
                            if name == "match_fail"
                                && matches!(
                                    items.first(),
                                    Some(Expr::Lit(Literal::Atom(a))) if a == "function_clause"
                                ) =>
                        {
                            self.atom_term("function_clause")?
                        }
                        Some(a) => self.compile_value(f, a, scope)?,
                        None => self.nil(),
                    };
                    (self.atom_term("error")?, reason)
                }
            };
            Ok((class, reason))
        })();
        self.eternal_alloc.set(was);
        let (class, reason) = result?;
        self.emit_raise(f, class, reason)
    }
}
