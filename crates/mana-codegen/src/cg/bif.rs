use crate::*;

impl<'ctx, 'p> Cg<'ctx, 'p> {
    /// Lower a call to a BIF module (`erlang`, `maps`, `file`, ...).
    ///
    /// A call into a module other than `erlang` goes to its own lowering
    /// method first. The `erlang` BIFs live in `bif_erlang.rs` as family
    /// methods. A family method returns `None` when it does not know the
    /// (name, arity) pair. No pair belongs to two families, so the chain
    /// order does not matter. The chain evaluates the arguments once,
    /// before the first family.
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
            return self.compile_timer_bif(f, name, args, scope);
        }
        if module == "ets" {
            return self.compile_ets_bif(f, name, args, scope);
        }
        if module == "application" {
            return self.compile_application_bif(f, name, args, scope);
        }
        if module == "net_kernel" && name == "monitor_nodes" {
            // There is one node, forever. A subscription to node events is a
            // no-op. The init of pg calls this. The rest of net_kernel still
            // raises.
            self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
            return self.atom_term("ok");
        }
        if module == "zlib" {
            if let Some(v) = self.compile_zlib_bif(f, name, args, scope)? {
                return Ok(v);
            }
            // An unhandled zlib name falls through to the raise arm below.
        }
        if matches!(
            module,
            "erts_internal"
                | "elixir_erl"
                | "erl_eval"
                | "beam_lib"
                | "global"
                | "global_group"
                | "net_kernel"
                | "zlib"
        ) {
            // These modules are BEAM, compiler, or distribution internals. The
            // call compiles to a runtime raise, so the whole caller stays
            // compilable. Reached code often touches these modules only on
            // branches that never run, for example the {global, Name} arm of
            // GenServer.whereis. The args are evaluated.
            self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
            let module_atom = self.atom_term(module)?;
            let reason = self.eternal_pair("unsupported", module_atom)?;
            let class = self.atom_term("error")?;
            let ctx = self.ctx_val();
            self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
            self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
            let target = self.unwind_target(f)?;
            self.builder
                .build_unconditional_branch(target)
                .map_err(be)?;
            let dead = self.ctx.append_basic_block(f, "unsup.dead");
            self.builder.position_at_end(dead);
            return Ok(self.i64t.get_undef());
        }
        if module == "file" || module == "prim_file" {
            return self.compile_file_bif(f, module, name, args, scope);
        }
        if module == "logger" {
            // Logging is disabled in mana binaries. allow/2 returns false, which
            // prunes every emit path. Every other name is an ok no-op. The args
            // are still evaluated. TODO(logger): write a real stderr handler.
            self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
            return match name {
                "allow" => self.atom_term("false"),
                // Logger.metadata matches on undefined | map.
                "get_process_metadata" => self.atom_term("undefined"),
                _ => self.atom_term("ok"),
            };
        }
        // Raising BIFs: the reason terms use the eternal allocator, so a raise
        // path is not a GC point.
        if matches!(
            (name, args.len()),
            ("error", 1) | ("error", 2) | ("exit", 1) | ("throw", 1)
        ) {
            self.compile_raise(f, name, args, scope)?;
            return Ok(self.i64t.get_undef());
        }
        if name == "error" && args.len() == 3 {
            // TODO(stacktraces): error/3 drops the error_info options. They only
            // affect stacktrace decoration.
            self.compile_raise(f, "error", &args[..1], scope)?;
            return Ok(self.i64t.get_undef());
        }
        if name == "nif_error" {
            // A nif stub without a native override raises like error/1.
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
