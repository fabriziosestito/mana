//! Calling convention and runtime ABI helpers for the code generator.
//!
//! Contract: every compiled function is `tailcc` and has the uniform
//! prototype (see `NREG`). The runtime calls compiled code only through
//! C-ABI wrappers. This module also declares the runtime externs and
//! holds the tag, allocation, and memory access helpers.

use crate::*;

impl<'ctx, 'p> Cg<'ctx, 'p> {
    pub(crate) fn declare_compiled(&self, sym: &str, arity: usize) -> FunctionValue<'ctx> {
        let f = self
            .module
            .add_function(sym, self.term_fn_type(arity), None);
        f.set_call_conventions(Self::TAILCC);
        f
    }

    /// Emit a `tailcc` call to a named compiled function. `tail` means that
    /// the call is in tail position, directly before `ret`. If the caller is
    /// `tailcc` too, the call is `musttail` (LLVM requires matching
    /// conventions). Otherwise the call gets the `tail` hint (see
    /// TODO(lco-funs)).
    pub(crate) fn call_compiled(
        &self,
        callee: FunctionValue<'ctx>,
        args: &[BasicMetadataValueEnum<'ctx>],
        name: &str,
        tail: bool,
    ) -> CgResult<CallSiteValue<'ctx>> {
        let packed = self.pack_args(args)?;
        let call = self.builder.build_call(callee, &packed, name).map_err(be)?;
        call.set_call_convention(Self::TAILCC);
        if tail {
            self.mark_tail(call);
        }
        Ok(call)
    }

    /// Set `musttail` if the current function has the same convention as the
    /// callee. Otherwise set the best-effort `tail` hint.
    pub(crate) fn mark_tail(&self, call: CallSiteValue<'ctx>) {
        let caller_cc = self
            .builder
            .get_insert_block()
            .and_then(|b| b.get_parent())
            .map(|f| f.get_call_conventions())
            .unwrap_or(0);
        if caller_cc == call.get_call_convention() {
            call.set_tail_call_kind(LLVMTailCallKind::LLVMTailCallKindMustTail);
        } else {
            call.set_tail_call(true);
        }
    }

    /// A C-ABI entry for a `tailcc` function. The runtime calls compiled code
    /// through `extern "C"` function pointers (mana_exports, spawn, apply).
    /// The wrapper is the runtime's C-ABI view of a compiled function:
    /// `extern "C" fn(ctx, a0..a{arity-1})` with the natural C prototype.
    /// call_dynamic transmutes to exactly that prototype. The wrapper
    /// forwards into the uniform tailcc body.
    pub(crate) fn ccc_wrapper(
        &self,
        target: FunctionValue<'ctx>,
        arity: usize,
    ) -> FunctionValue<'ctx> {
        let sym = format!("{}.c", target.get_name().to_string_lossy());
        if let Some(w) = self.module.get_function(&sym) {
            return w;
        }
        let w = self.module.add_function(&sym, self.c_fn_type(arity), None);
        w.set_linkage(Linkage::LinkOnceODR);
        let saved = self.builder.get_insert_block();
        let bb = self.ctx.append_basic_block(w, "entry");
        self.builder.position_at_end(bb);
        let argv: Vec<BasicMetadataValueEnum> = (0..=arity)
            .map(|i| w.get_nth_param(i as u32).unwrap().into())
            .collect();
        let packed = self.pack_args(&argv).unwrap();
        let call = self.builder.build_call(target, &packed, "fwd").unwrap();
        call.set_call_convention(Self::TAILCC);
        let v = call_result(call).unwrap();
        self.builder.build_return(Some(&v)).unwrap();
        if let Some(bb) = saved {
            self.builder.position_at_end(bb);
        }
        w
    }

    /// The natural C prototype `i64 (ptr ctx, i64 x arity)`. Runtime BIFs
    /// and Mana.Native package symbols are `extern "C"` and keep this
    /// prototype.
    pub(crate) fn c_fn_type(&self, arity: usize) -> FunctionType<'ctx> {
        let mut params: Vec<BasicMetadataTypeEnum> =
            vec![BasicMetadataTypeEnum::PointerType(self.ptrt)];
        params.extend((0..arity).map(|_| BasicMetadataTypeEnum::IntType(self.i64t)));
        self.i64t.fn_type(&params, false)
    }

    /// The uniform prototype (see NREG). `_arity` documents the call site.
    /// The type does not depend on it.
    pub(crate) fn term_fn_type(&self, _arity: usize) -> FunctionType<'ctx> {
        let mut params: Vec<BasicMetadataTypeEnum> =
            vec![BasicMetadataTypeEnum::PointerType(self.ptrt)];
        params.extend((0..NREG).map(|_| BasicMetadataTypeEnum::IntType(self.i64t)));
        self.i64t.fn_type(&params, false)
    }

    /// Pack `ctx + args` into the uniform call vector. If there are NREG args
    /// or fewer, all of them ride in registers. If there are more, the first
    /// NREG-1 args ride in registers and the last register slot carries
    /// nothing. Args NREG-1.. then go to the ctx spill area. The spill area
    /// is a per-scheduler scratch. The callee prologue consumes it before
    /// any other code runs, so no GC point and no re-entrancy can intervene.
    pub(crate) fn pack_args(
        &self,
        argv: &[BasicMetadataValueEnum<'ctx>],
    ) -> CgResult<Vec<BasicMetadataValueEnum<'ctx>>> {
        let nargs = argv.len() - 1;
        let undef: BasicMetadataValueEnum = self.i64t.get_undef().into();
        let mut out: Vec<BasicMetadataValueEnum> = Vec::with_capacity(1 + NREG);
        out.push(argv[0]);
        if nargs <= NREG {
            out.extend_from_slice(&argv[1..]);
            while out.len() < 1 + NREG {
                out.push(undef);
            }
            return Ok(out);
        }
        out.extend_from_slice(&argv[1..NREG]); // args 0..NREG-2 ride in registers
        let ctx = argv[0].into_pointer_value();
        let spill = self.mem_load(ctx, CTX_ARGV_SPILL, MemKind::Ctx)?;
        let sp = self
            .builder
            .build_int_to_ptr(spill, self.ptrt, "spill")
            .map_err(be)?;
        for (i, a) in argv[NREG..].iter().enumerate() {
            let gep = unsafe {
                self.builder
                    .build_in_bounds_gep(
                        self.i64t,
                        sp,
                        &[self.i64t.const_int(i as u64, false)],
                        "spill.g",
                    )
                    .map_err(be)?
            };
            self.builder
                .build_store(gep, a.into_int_value())
                .map_err(be)?;
        }
        out.push(undef);
        Ok(out)
    }

    /// Prologue counterpart of `pack_args`: the value of the callee's `i`-th
    /// argument (0-based), given its total arg count. Call this function at
    /// function entry, before any call or allocation.
    pub(crate) fn param_at(
        &self,
        f: FunctionValue<'ctx>,
        i: usize,
        nargs: usize,
    ) -> CgResult<IntValue<'ctx>> {
        if nargs <= NREG || i < NREG - 1 {
            return Ok(f.get_nth_param(1 + i as u32).unwrap().into_int_value());
        }
        let ctx = f.get_nth_param(0).unwrap().into_pointer_value();
        let spill = self.mem_load(ctx, CTX_ARGV_SPILL, MemKind::Ctx)?;
        let sp = self
            .builder
            .build_int_to_ptr(spill, self.ptrt, "spill")
            .map_err(be)?;
        let k = (i - (NREG - 1)) as u64;
        let gep = unsafe {
            self.builder
                .build_in_bounds_gep(self.i64t, sp, &[self.i64t.const_int(k, false)], "spill.g")
                .map_err(be)?
        };
        Ok(self
            .builder
            .build_load(self.i64t, gep, "spill.arg")
            .map_err(be)?
            .into_int_value())
    }

    pub(crate) fn ctx_val(&self) -> PointerValue<'ctx> {
        self.cur_ctx.get().expect("ctx param not set")
    }

    pub(crate) fn framed(&self) -> bool {
        self.cur_frame.get().is_some()
    }

    pub(crate) fn expr_gc(&self, e: &Expr) -> bool {
        let mut letrec = HashSet::new();
        expr_may_gc(e, &self.module_name, self.gc_set, &mut letrec)
    }

    // Runtime externs

    pub(crate) fn rt_fn(
        &self,
        name: &str,
        mk: impl FnOnce() -> FunctionType<'ctx>,
    ) -> FunctionValue<'ctx> {
        self.module
            .get_function(name)
            .unwrap_or_else(|| self.module.add_function(name, mk(), None))
    }

    pub(crate) fn rt_init(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_init", || self.ptrt.fn_type(&[], false))
    }

    pub(crate) fn rt_display(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_display", || {
            self.ctx
                .void_type()
                .fn_type(&[BasicMetadataTypeEnum::IntType(self.i64t)], false)
        })
    }

    pub(crate) fn rt_alloc_slow(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_alloc_slow", || {
            self.ptrt.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    pub(crate) fn rt_alloc_eternal(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_alloc_eternal", || {
            self.ptrt.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    pub(crate) fn rt_p_i64(&self, name: &str) -> FunctionValue<'ctx> {
        self.rt_fn(name, || {
            self.i64t
                .fn_type(&[BasicMetadataTypeEnum::PointerType(self.ptrt)], false)
        })
    }

    pub(crate) fn rt_p_void(&self, name: &str) -> FunctionValue<'ctx> {
        self.rt_fn(name, || {
            self.ctx
                .void_type()
                .fn_type(&[BasicMetadataTypeEnum::PointerType(self.ptrt)], false)
        })
    }

    pub(crate) fn rt_register_atoms(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_register_atoms", || {
            let params: Vec<BasicMetadataTypeEnum> = (0..20)
                .map(|_| BasicMetadataTypeEnum::IntType(self.i64t))
                .collect();
            self.ctx.void_type().fn_type(&params, false)
        })
    }

    /// A runtime BIF helper with the prototype (ctx, term) -> term.
    pub(crate) fn rt_pt_i64(&self, name: &str) -> FunctionValue<'ctx> {
        self.rt_fn(name, || {
            self.i64t.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    pub(crate) fn rt_run(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_run", || {
            self.i64t.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                ],
                false,
            )
        })
    }

    pub(crate) fn rt_spawn(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_spawn", || {
            self.i64t.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    pub(crate) fn rt_send(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_send", || {
            self.ctx.void_type().fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    pub(crate) fn rt_recv_wait(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_recv_wait", || {
            self.i64t.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    pub(crate) fn rt_uncaught(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_uncaught", || {
            self.ctx
                .void_type()
                .fn_type(&[BasicMetadataTypeEnum::PointerType(self.ptrt)], false)
        })
    }

    /// A runtime helper with the prototype (term, term) -> i64.
    pub(crate) fn rt_tt_i64(&self, name: &str) -> FunctionValue<'ctx> {
        self.rt_fn(name, || {
            self.i64t.fn_type(
                &[
                    BasicMetadataTypeEnum::IntType(self.i64t),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    /// The arithmetic slow path, with the prototype (ctx, op, a, b) -> term.
    pub(crate) fn rt_arith(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_arith", || {
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
    }

    /// A runtime helper with the prototype (ctx, term, term) -> term. The
    /// raising helpers use this shape: primop match_fail/raise and
    /// erlang:error|exit|throw. Their reason terms use the eternal allocator.
    /// The GC never moves these terms, but it scans their fields.
    pub(crate) fn rt_ptt_i64(&self, name: &str) -> FunctionValue<'ctx> {
        self.rt_fn(name, || {
            self.i64t.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        })
    }

    // Helpers

    pub(crate) fn local_fn(&self, fname: &FunName) -> CgResult<FunctionValue<'ctx>> {
        self.fns
            .borrow()
            .get(fname)
            .copied()
            .ok_or_else(|| format!("undefined local function {}/{}", fname.name, fname.arity))
    }

    pub(crate) fn remote_fn(&self, module: &str, name: &str, arity: usize) -> FunctionValue<'ctx> {
        let sym = mangle(
            module,
            &FunName {
                name: name.to_string(),
                arity,
            },
        );
        self.module
            .get_function(&sym)
            .unwrap_or_else(|| self.declare_compiled(&sym, arity))
    }

    pub(crate) fn tag_of(&self, val: IntValue<'ctx>) -> CgResult<IntValue<'ctx>> {
        self.builder
            .build_and(val, self.i64t.const_int(TAG_MASK, false), "tag")
            .map_err(be)
    }

    pub(crate) fn untag_int(&self, val: IntValue<'ctx>) -> CgResult<IntValue<'ctx>> {
        self.builder
            .build_right_shift(val, self.i64t.const_int(3, false), true, "untag")
            .map_err(be)
    }

    pub(crate) fn retag_int(&self, val: IntValue<'ctx>) -> CgResult<IntValue<'ctx>> {
        let shifted = self
            .builder
            .build_left_shift(val, self.i64t.const_int(3, false), "shl")
            .map_err(be)?;
        self.builder
            .build_or(shifted, self.i64t.const_int(TAG_SMALL, false), "retag")
            .map_err(be)
    }

    /// Inline nursery bump allocation. The fast path loads top and end from
    /// ctx words 0 and 1, then bumps top. On overflow, the slow path calls
    /// `mana_rt_alloc_slow`, which collects. The slow path keeps this a GC
    /// point.
    pub(crate) fn alloc_words(&self, n: u64) -> CgResult<PointerValue<'ctx>> {
        self.alloc_words_kind(n, false)
    }

    pub(crate) fn alloc_words_kind(&self, n: u64, is_cons: bool) -> CgResult<PointerValue<'ctx>> {
        if self.eternal_alloc.get() {
            let call = self
                .builder
                .build_call(
                    self.rt_alloc_eternal(),
                    &[
                        self.ctx_val().into(),
                        self.i64t.const_int(n, false).into(),
                        self.i64t.const_int(is_cons as u64, false).into(),
                    ],
                    "alloc.eternal",
                )
                .map_err(be)?;
            return Ok(call_result(call)?.into_pointer_value());
        }
        let f = self
            .builder
            .get_insert_block()
            .unwrap()
            .get_parent()
            .unwrap();
        let ctx = self.ctx_val();
        let fast = self.ctx.append_basic_block(f, "alloc.fast");
        let slow = self.ctx.append_basic_block(f, "alloc.slow");
        let merge = self.ctx.append_basic_block(f, "alloc.done");

        let top = self.mem_load(ctx, 0, MemKind::Ctx)?;
        let new_top = self
            .builder
            .build_int_add(top, self.i64t.const_int(n * 8, false), "alloc.newtop")
            .map_err(be)?;
        let end = self.mem_load(ctx, 1, MemKind::Ctx)?;
        let fits = self
            .builder
            .build_int_compare(IntPredicate::ULE, new_top, end, "alloc.fits")
            .map_err(be)?;
        self.builder
            .build_conditional_branch(fits, fast, slow)
            .map_err(be)?;

        self.builder.position_at_end(fast);
        self.mem_store(ctx, 0, new_top, MemKind::Ctx)?;
        self.builder.build_unconditional_branch(merge).map_err(be)?;

        self.builder.position_at_end(slow);
        let call = self
            .builder
            .build_call(
                self.rt_alloc_slow(),
                &[ctx.into(), self.i64t.const_int(n, false).into()],
                "alloc.rt",
            )
            .map_err(be)?;
        let slow_ptr = call_result(call)?.into_pointer_value();
        let slow_addr = self
            .builder
            .build_ptr_to_int(slow_ptr, self.i64t, "alloc.slowaddr")
            .map_err(be)?;
        let slow_bb = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(merge).map_err(be)?;

        self.builder.position_at_end(merge);
        let phi = self
            .builder
            .build_phi(self.i64t, "alloc.addr")
            .map_err(be)?;
        phi.add_incoming(&[(&top, fast), (&slow_addr, slow_bb)]);
        self.builder
            .build_int_to_ptr(phi.as_basic_value().into_int_value(), self.ptrt, "alloc")
            .map_err(be)
    }

    pub(crate) fn tbaa_tag(&self, kind: MemKind) -> inkwell::values::MetadataValue<'ctx> {
        match kind {
            MemKind::Ctx => self.tbaa_ctx,
            MemKind::Frame => self.tbaa_frame,
            MemKind::Heap => self.tbaa_heap,
        }
    }

    pub(crate) fn mem_store(
        &self,
        p: PointerValue<'ctx>,
        index: u64,
        v: IntValue<'ctx>,
        kind: MemKind,
    ) -> CgResult<()> {
        let slot = unsafe {
            self.builder
                .build_in_bounds_gep(self.i64t, p, &[self.i64t.const_int(index, false)], "slot")
                .map_err(be)?
        };
        let inst = self.builder.build_store(slot, v).map_err(be)?;
        let _ = inst.set_metadata(self.tbaa_tag(kind), self.tbaa_kind);
        Ok(())
    }

    pub(crate) fn mem_load(
        &self,
        p: PointerValue<'ctx>,
        index: u64,
        kind: MemKind,
    ) -> CgResult<IntValue<'ctx>> {
        let slot = unsafe {
            self.builder
                .build_in_bounds_gep(self.i64t, p, &[self.i64t.const_int(index, false)], "slot")
                .map_err(be)?
        };
        let v = self
            .builder
            .build_load(self.i64t, slot, "word")
            .map_err(be)?;
        if let Some(inst) = v.as_instruction_value() {
            let _ = inst.set_metadata(self.tbaa_tag(kind), self.tbaa_kind);
        }
        Ok(v.into_int_value())
    }

    /// Heap object word access. This is the most common case.
    pub(crate) fn store_word(
        &self,
        p: PointerValue<'ctx>,
        index: u64,
        v: IntValue<'ctx>,
    ) -> CgResult<()> {
        self.mem_store(p, index, v, MemKind::Heap)
    }

    pub(crate) fn load_word(&self, p: PointerValue<'ctx>, index: u64) -> CgResult<IntValue<'ctx>> {
        self.mem_load(p, index, MemKind::Heap)
    }
}
