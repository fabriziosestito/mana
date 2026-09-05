use crate::*;

impl<'ctx, 'p> Cg<'ctx, 'p> {
    // ---- constants ----

    pub(crate) fn small_int(&self, n: i64) -> IntValue<'ctx> {
        // literals outside the small range arrive as Literal::Big (lexer
        // threshold is 2^60); internal callers pass trusted small values
        debug_assert!((-(1i64 << 60)..(1i64 << 60)).contains(&n));
        self.i64t.const_int(((n as u64) << 3) | TAG_SMALL, false)
    }

    pub(crate) fn nil(&self) -> IntValue<'ctx> {
        self.i64t.const_int(NIL, false)
    }

    /// The (deduped, linkonce_odr) atom struct global for `name`. Creating it
    /// also puts the atom into the program's closed-world atom table.
    pub(crate) fn atom_global(&self, name: &str) -> GlobalValue<'ctx> {
        let mut atoms = self.atoms.borrow_mut();
        match atoms.get(name) {
            Some(g) => *g,
            None => {
                let bytes = name.as_bytes();
                let data = self.ctx.const_string(bytes, false);
                let len = self.i64t.const_int(bytes.len() as u64, false);
                let init = self.ctx.const_struct(&[len.into(), data.into()], false);
                let g = self.module.add_global(
                    init.get_type(),
                    None,
                    &format!("mana_atom.{}", sanitize(name)),
                );
                g.set_initializer(&init);
                g.set_constant(true);
                g.set_alignment(8);
                // Same atom name → same symbol in every object; the linker
                // keeps exactly one, giving program-wide identity.
                g.set_linkage(Linkage::LinkOnceODR);
                atoms.insert(name.to_string(), g);
                g
            }
        }
    }

    pub(crate) fn atom_term(&self, name: &str) -> CgResult<IntValue<'ctx>> {
        let global = self.atom_global(name);
        let as_int = self
            .builder
            .build_ptr_to_int(global.as_pointer_value(), self.i64t, "atom.addr")
            .map_err(be)?;
        self.builder
            .build_or(as_int, self.i64t.const_int(TAG_ATOM, false), "atom")
            .map_err(be)
    }

    /// A fully-constant binary as a static term: [header | bytes], content-
    /// addressed linkonce_odr symbol (deduped program-wide by the linker).
    /// Never allocated, never copied — forward_major passes non-heap boxed
    /// terms through.
    pub(crate) fn static_binary(&self, bytes: &[u8]) -> CgResult<IntValue<'ctx>> {
        let sym = format!(
            "mana_bin.{}",
            &blake3::hash(bytes).to_hex().as_str()[..16]
        );
        let g = match self.module.get_global(&sym) {
            Some(g) => g,
            None => {
                let header = self
                    .i64t
                    .const_int(((bytes.len() as u64) << 8) | KIND_BIN, false);
                let data = self.ctx.const_string(bytes, false);
                let init = self.ctx.const_struct(&[header.into(), data.into()], false);
                let g = self.module.add_global(init.get_type(), None, &sym);
                g.set_initializer(&init);
                g.set_constant(true);
                g.set_alignment(8);
                g.set_linkage(Linkage::LinkOnceODR);
                g
            }
        };
        self.builder
            .build_ptr_to_int(g.as_pointer_value(), self.i64t, "bin.static")
            .map_err(be)
    }

    /// A fully-constant term (literal, or tuple/cons/binary whose parts are
    /// all constant) as an LLVM constant `i64`. Boxed constants become
    /// content-addressed linkonce_odr globals like `static_binary`: built
    /// once at link time, never allocated per evaluation, never copied by
    /// the GC (only nursery pointers are forwarded; constants hold only
    /// immediates and other constants, so majors have nothing to scan).
    /// Motivating shape: Elixir's `Base` reads `element(i, {4096 chars})`
    /// four times per 6 input bytes — allocating that tuple each time made
    /// url_encode64 150x slower than BEAM. None: not constant.
    pub(crate) fn const_term(&self, f: FunctionValue<'ctx>, e: &Expr) -> CgResult<Option<IntValue<'ctx>>> {
        Ok(Some(match e {
            Expr::Lit(Literal::Int(n)) => self.small_int(*n),
            Expr::Lit(Literal::Nil) => self.nil(),
            Expr::Lit(Literal::Atom(a)) => {
                let g = self.atom_global(a);
                g.as_pointer_value()
                    .const_to_int(self.i64t)
                    .const_add(self.i64t.const_int(TAG_ATOM, false)) // 8-aligned: add == or
            }
            Expr::Lit(Literal::Float(x)) => {
                let header = self.i64t.const_int((1 << 8) | KIND_FLOAT, false);
                let bits = self.i64t.const_int(x.to_bits(), false);
                self.const_boxed("mana_flt", &[header, bits], 0)
            }
            Expr::Binary(segs) if binary_all_const(segs) => {
                // compile_binary_construct returns the static term for an
                // all-constant binary (no builder instructions emitted)
                let mut scope = Scope::default();
                self.compile_binary_construct(f, segs, &mut scope)?
            }
            Expr::Tuple(items) => {
                let mut words = vec![self
                    .i64t
                    .const_int(((items.len() as u64) << 8) | KIND_TUPLE, false)];
                for it in items {
                    match self.const_term(f, it)? {
                        Some(v) => words.push(v),
                        None => return Ok(None),
                    }
                }
                self.const_boxed("mana_tup", &words, 0)
            }
            Expr::Cons(h, t) => {
                let (Some(hv), Some(tv)) = (self.const_term(f, h)?, self.const_term(f, t)?) else {
                    return Ok(None);
                };
                self.const_boxed("mana_cons", &[hv, tv], TAG_CONS)
            }
            _ => return Ok(None),
        }))
    }

    /// Emit `words` as a constant global and return its address (| tag).
    /// Keyed by the words' printed form so equal constants share a symbol
    /// within the module; linkonce_odr dedups across modules.
    pub(crate) fn const_boxed(&self, prefix: &str, words: &[IntValue<'ctx>], tag: u64) -> IntValue<'ctx> {
        let key: String = words
            .iter()
            .map(|w| inkwell::values::AnyValue::print_to_string(w).to_string())
            .collect::<Vec<_>>()
            .join(",");
        let sym = format!("{}.{}", prefix, &blake3::hash(key.as_bytes()).to_hex().as_str()[..16]);
        let g = match self.module.get_global(&sym) {
            Some(g) => g,
            None => {
                let init = self.i64t.const_array(words);
                let g = self.module.add_global(init.get_type(), None, &sym);
                g.set_initializer(&init);
                g.set_constant(true);
                g.set_alignment(8);
                g.set_linkage(Linkage::LinkOnceODR);
                g
            }
        };
        let addr = g.as_pointer_value().const_to_int(self.i64t);
        if tag == 0 {
            addr
        } else {
            addr.const_add(self.i64t.const_int(tag, false)) // 8-aligned: add == or
        }
    }

    /// An internal constant byte array; returns its pointer.
    pub(crate) fn static_bytes(&self, bytes: &[u8]) -> CgResult<PointerValue<'ctx>> {
        let data = self.ctx.const_string(bytes, false);
        let n = self.static_bytes_count.get();
        self.static_bytes_count.set(n + 1);
        let g = self
            .module
            .add_global(data.get_type(), None, &format!("mana_bytes.{}", n));
        g.set_initializer(&data);
        g.set_constant(true);
        g.set_linkage(Linkage::Internal);
        Ok(g.as_pointer_value())
    }

    // ---- output ----

    /// Closed-world atom table: one pointer per atom static in the
    /// `mana_atoms` ELF section (linkonce_odr → linker-deduped program-wide,
    /// like the atoms themselves). Pinned via llvm.used so O2 can't discard
    /// the otherwise-unreferenced globals. The runtime walks
    /// __start_mana_atoms..__stop_mana_atoms for binary_to_atom.
    pub(crate) fn emit_atom_table(&self) {
        let atoms = self.atoms.borrow();
        if atoms.is_empty() {
            return;
        }
        // behaviours table: (module_atom, behaviour_atom) raw-pointer pairs
        // in the `mana_behaviours` section, for module_info(:attributes)
        // the entry module anchors the section so its __start/__stop
        // symbols always exist (a zeroed pair the runtime skips)
        if self.is_entry_module.get() && self.behaviours.borrow().is_empty() {
            self.behaviours
                .borrow_mut()
                .push((self.module_name.clone(), self.module_name.clone()));
        }
        let behaviour_refs: Vec<PointerValue<'ctx>> = {
            let bs = self.behaviours.borrow();
            bs.iter()
                .enumerate()
                .map(|(i, (m, b))| {
                    let init = self.ctx.const_struct(
                        &[
                            atoms.get(m.as_str()).unwrap().as_pointer_value().into(),
                            atoms.get(b.as_str()).unwrap().as_pointer_value().into(),
                        ],
                        false,
                    );
                    let g = self.module.add_global(
                        init.get_type(),
                        None,
                        &format!("mana_behaviour.{}.{}", sanitize(m), i),
                    );
                    g.set_initializer(&init);
                    g.set_constant(true);
                    g.set_alignment(8);
                    g.set_section(Some("mana_behaviours"));
                    g.set_linkage(Linkage::Internal);
                    g.as_pointer_value()
                })
                .collect()
        };
        let mut used: Vec<PointerValue<'ctx>> = Vec::with_capacity(atoms.len());
        used.extend(behaviour_refs);
        // export table entries: {mod_atom, fun_atom, arity, code} in the
        // `mana_exports` section (raw pointers; the runtime tags them)
        let export_list: Vec<(FunName, FunctionValue<'ctx>)> = self.exports.borrow().clone();
        for (fname, code) in export_list.iter() {
            let c_code = self.ccc_wrapper(*code, fname.arity);
            // the closure-convention body make_fun/3 hands out (args ++ [fun])
            let fun_code = self.fun_shim(None, fname).expect("fun shim for an export");
            let m = atoms
                .get(self.module_name.as_str())
                .expect("module atom exists")
                .as_pointer_value();
            let fa = atoms
                .get(fname.name.as_str())
                .expect("function atom exists")
                .as_pointer_value();
            let init = self.ctx.const_struct(
                &[
                    m.into(),
                    fa.into(),
                    self.i64t.const_int(fname.arity as u64, false).into(),
                    c_code.as_global_value().as_pointer_value().into(),
                    fun_code.as_global_value().as_pointer_value().into(),
                ],
                false,
            );
            let g = self.module.add_global(
                init.get_type(),
                None,
                &format!(
                    "mana_export.{}.{}.{}",
                    sanitize(&self.module_name),
                    sanitize(&fname.name),
                    fname.arity
                ),
            );
            g.set_initializer(&init);
            g.set_constant(true);
            g.set_alignment(8);
            g.set_section(Some("mana_exports"));
            g.set_linkage(Linkage::Internal);
            used.push(g.as_pointer_value());
        }
        for (name, g) in atoms.iter() {
            let r = self.module.add_global(
                self.ptrt,
                None,
                &format!("mana_atomref.{}", sanitize(name)),
            );
            r.set_initializer(&g.as_pointer_value());
            r.set_constant(true);
            r.set_alignment(8);
            r.set_section(Some("mana_atoms"));
            r.set_linkage(Linkage::LinkOnceODR);
            used.push(r.as_pointer_value());
        }
        let arr = self.ptrt.const_array(&used);
        let lu = self.module.add_global(arr.get_type(), None, "llvm.used");
        lu.set_initializer(&arr);
        lu.set_linkage(Linkage::Appending);
        lu.set_section(Some("llvm.metadata"));
    }

    pub(crate) fn emit_object(&self, out: &Path) -> CgResult<()> {
        self.emit_atom_table();
        Target::initialize_native(&InitializationConfig::default())
            .map_err(|e| format!("target init: {}", e))?;
        let triple = TargetMachine::get_default_triple();
        let target = Target::from_triple(&triple).map_err(|e| e.to_string())?;
        let tm = target
            .create_target_machine(
                &triple,
                &TargetMachine::get_host_cpu_name().to_string(),
                &TargetMachine::get_host_cpu_features().to_string(),
                OptimizationLevel::Aggressive,
                RelocMode::PIC,
                CodeModel::Default,
            )
            .ok_or("failed to create target machine")?;
        self.module.set_triple(&triple);
        self.module
            .set_data_layout(&tm.get_target_data().get_data_layout());
        let opts = inkwell::passes::PassBuilderOptions::create();
        self.module
            .run_passes("default<O2>", &tm, opts)
            .map_err(|e| format!("optimization: {}", e))?;
        tm.write_to_file(&self.module, FileType::Object, out)
            .map_err(|e| format!("emit object: {}", e))
    }
}
