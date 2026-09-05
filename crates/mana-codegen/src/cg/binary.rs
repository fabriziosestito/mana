use crate::*;

pub(crate) fn atom_list(e: &Expr, out: &mut Vec<String>) {
    match e {
        Expr::Lit(Literal::Atom(a)) => out.push(a.clone()),
        Expr::Cons(h, t) => {
            atom_list(h, out);
            atom_list(t, out);
        }
        _ => {}
    }
}

/// Coalesce runs of constant sub-byte integer segments into single
/// byte-aligned synthetic segments (see compile_binary_construct).
pub(crate) fn coalesce_bit_runs(
    segs: &[mana_syntax::BinSegment<Box<Expr>>],
    specs: &[SegSpec],
) -> CgResult<Vec<mana_syntax::BinSegment<Box<Expr>>>> {
    let mask = |v: &Expr, bits: u64| -> Expr {
        Expr::Call {
            module: "erlang".to_string(),
            name: "band".to_string(),
            args: vec![v.clone(), Expr::Lit(Literal::Int(((1i64 << bits) - 1) as i64))],
        }
    };
    let mut out: Vec<mana_syntax::BinSegment<Box<Expr>>> = Vec::with_capacity(segs.len());
    let mut run: Vec<(&Expr, u64)> = Vec::new();
    let flush = |run: &mut Vec<(&Expr, u64)>,
                 out: &mut Vec<mana_syntax::BinSegment<Box<Expr>>>|
     -> CgResult<()> {
        if run.is_empty() {
            return Ok(());
        }
        let total: u64 = run.iter().map(|(_, b)| b).sum();
        if total % 8 != 0 {
            return Err(format!(
                "TODO(bitstring): sub-byte segments do not group to a whole byte ({} bits)",
                total
            ));
        }
        if total > 57 {
            return Err(format!(
                "TODO(bitstring): coalesced bit run exceeds small-int width ({} bits)",
                total
            ));
        }
        let mut it = run.drain(..);
        let (v0, b0) = it.next().unwrap();
        let mut acc = mask(v0, b0);
        for (v, b) in it {
            let shifted = Expr::Call {
                module: "erlang".to_string(),
                name: "bsl".to_string(),
                args: vec![acc, Expr::Lit(Literal::Int(b as i64))],
            };
            acc = Expr::Call {
                module: "erlang".to_string(),
                name: "bor".to_string(),
                args: vec![shifted, mask(v, b)],
            };
        }
        out.push(mana_syntax::BinSegment {
            value: Box::new(acc),
            spec: vec![
                Expr::Lit(Literal::Int((total / 8) as i64)),
                Expr::Lit(Literal::Int(8)),
                Expr::Lit(Literal::Atom("integer".to_string())),
                Expr::Lit(Literal::Nil),
            ],
        });
        Ok(())
    };
    for (seg, spec) in segs.iter().zip(specs) {
        match &spec.kind {
            SegKind::Int { size: SegSize::Bits(b) } => run.push((seg.value.as_ref(), *b)),
            _ => {
                flush(&mut run, &mut out)?;
                out.push(seg.clone());
            }
        }
    }
    flush(&mut run, &mut out)?;
    Ok(out)
}

pub(crate) fn parse_seg_spec(spec: &[Expr]) -> Result<SegSpec, String> {
    if spec.len() != 4 {
        return Err(format!("bitstring segment spec has {} args, want 4", spec.len()));
    }
    let ty = match &spec[2] {
        Expr::Lit(Literal::Atom(a)) => a.as_str(),
        other => return Err(format!("bitstring segment type is not an atom: {:?}", other)),
    };
    let unit = match &spec[1] {
        Expr::Lit(Literal::Int(u)) => *u,
        // utf8/utf16/utf32 segments carry 'undefined' size and unit
        _ if ty == "utf8" => 0,
        _ => return Err("bitstring segment unit is not a constant".into()),
    };
    let mut flags = Vec::new();
    atom_list(&spec[3], &mut flags);
    let little = flags.iter().any(|f| f == "little" || f == "native");
    let signed = flags.iter().any(|f| f == "signed");
    let const_bytes_of = |sz: i64| -> Result<u64, String> {
        let bits = sz * unit;
        if bits % 8 != 0 || bits < 0 {
            return Err(format!(
                "TODO(bitstring): only byte-aligned segments are supported (got {} bits)",
                bits
            ));
        }
        Ok((bits / 8) as u64)
    };
    let kind = match (ty, &spec[0]) {
        ("utf8", _) => SegKind::Utf8,
        ("integer", Expr::Lit(Literal::Int(sz))) => {
            let bits = sz * unit;
            if bits >= 0 && bits % 8 != 0 && bits <= 57 && !little && !signed {
                SegKind::Int { size: SegSize::Bits(bits as u64) }
            } else {
                SegKind::Int { size: SegSize::Bytes(const_bytes_of(*sz)?) }
            }
        }
        ("binary", Expr::Lit(Literal::Atom(a))) if a == "all" => {
            SegKind::Bin { size: SegSize::All }
        }
        ("binary", Expr::Lit(Literal::Int(sz))) => SegKind::Bin {
            size: SegSize::Bytes(const_bytes_of(*sz)?),
        },
        ("integer", e) => SegKind::Int {
            size: SegSize::Dyn { size: e.clone(), unit },
        },
        ("binary", e) => SegKind::Bin {
            size: SegSize::Dyn { size: e.clone(), unit },
        },
        ("float", _) => return Err("TODO: float bitstring segments".into()),
        (other, _) => return Err(format!("unsupported bitstring segment type '{}'", other)),
    };
    Ok(SegSpec { little, signed, kind })
}

/// Decimal digits → big-endian bytes, truncated (mod 2^(8n)) or left-padded
/// to exactly `nbytes` — BEAM's truncating construction semantics.
pub(crate) fn big_to_bytes(dec: &str, nbytes: usize, little: bool) -> Result<Vec<u8>, String> {
    let mut digits: Vec<u8> = Vec::with_capacity(dec.len());
    for c in dec.bytes() {
        if !c.is_ascii_digit() {
            return Err(format!("bad big-integer literal '{}'", dec));
        }
        digits.push(c - b'0');
    }
    // repeated long division by 256, remainders = little-endian bytes
    let mut le = Vec::new();
    while digits.iter().any(|&d| d != 0) {
        let mut rem: u32 = 0;
        let mut q = Vec::with_capacity(digits.len());
        for &d in &digits {
            let cur = rem * 10 + d as u32;
            q.push((cur / 256) as u8);
            rem = cur % 256;
        }
        le.push(rem as u8);
        while q.first() == Some(&0) {
            q.remove(0);
        }
        digits = q;
    }
    le.resize(nbytes, 0);
    le.truncate(nbytes);
    if !little {
        le.reverse();
    }
    Ok(le)
}

/// The constant bytes of an integer segment, when they can be computed at
/// compile time. `None` = dynamic value.
pub(crate) fn seg_const_bytes(value: &Expr, nbytes: u64, little: bool) -> Result<Option<Vec<u8>>, String> {
    match value {
        Expr::Lit(Literal::Int(n)) => {
            let mut out = Vec::with_capacity(nbytes as usize);
            let v = *n as u64;
            for i in 0..nbytes {
                let shift = 8 * if little { i } else { nbytes - 1 - i };
                out.push(if shift < 64 { (v >> shift) as u8 } else {
                    // sign-extension bytes beyond 64 bits
                    if *n < 0 { 0xff } else { 0 }
                });
            }
            Ok(Some(out))
        }
        Expr::Lit(Literal::Big(d)) => Ok(Some(big_to_bytes(d, nbytes as usize, little)?)),
        _ => Ok(None),
    }
}

/// Every segment's bytes are known at compile time (mirrors the const
/// extraction in compile_binary_construct) — such binaries compile to
/// static terms: no allocation, no raise.
pub(crate) fn binary_all_const(segs: &[mana_syntax::BinSegment<Box<Expr>>]) -> bool {
    segs.iter().all(|s| match parse_seg_spec(&s.spec) {
        Ok(spec) => match spec.kind {
            SegKind::Utf8 => matches!(
                s.value.as_ref(),
                Expr::Lit(Literal::Int(cp)) if char::from_u32(*cp as u32).is_some()
            ),
            SegKind::Int { size: SegSize::Bytes(n) } => {
                matches!(seg_const_bytes(s.value.as_ref(), n, spec.little), Ok(Some(_)))
            }
            _ => false,
        },
        Err(_) => false,
    })
}

impl<'ctx, 'p> Cg<'ctx, 'p> {
    /// A proper list from already-rooted child values. Nursery mode: one
    /// block of headerless cons cells (single GC point). Eternal (raise
    /// path) mode: per-cell allocs, chained in SSA (no GC there).
    pub(crate) fn build_list_from_rooted(&self, rooted: &[Rooted<'ctx>]) -> CgResult<IntValue<'ctx>> {
        if rooted.is_empty() {
            return Ok(self.nil());
        }
        if self.eternal_alloc.get() {
            let mut tail = self.nil();
            for r in rooted.iter().rev() {
                let p = self.alloc_words_kind(2, true)?;
                let v = self.rooted_get(r)?;
                self.store_word(p, 0, v)?;
                self.store_word(p, 1, tail)?;
                let addr = self
                    .builder
                    .build_ptr_to_int(p, self.i64t, "cons.addr")
                    .map_err(be)?;
                tail = self
                    .builder
                    .build_or(addr, self.i64t.const_int(TAG_CONS, false), "cons")
                    .map_err(be)?;
            }
            return Ok(tail);
        }
        let n = rooted.len() as u64;
        let p = self.alloc_words_kind(2 * n, true)?;
        let base = self
            .builder
            .build_ptr_to_int(p, self.i64t, "list.base")
            .map_err(be)?;
        let mut head = self.nil();
        for (i, r) in rooted.iter().enumerate().rev() {
            let v = self.rooted_get(r)?;
            self.store_word(p, 2 * i as u64, v)?;
            self.store_word(p, 2 * i as u64 + 1, head)?;
            let addr = self
                .builder
                .build_int_add(
                    base,
                    self.i64t.const_int(16 * i as u64, false),
                    "cell.addr",
                )
                .map_err(be)?;
            head = self
                .builder
                .build_or(addr, self.i64t.const_int(TAG_CONS, false), "cons")
                .map_err(be)?;
        }
        Ok(head)
    }

    /// Bitstring construction: evaluate all segment values and dynamic
    /// sizes (rooted), compute the total byte size, allocate once, then
    /// fill with non-allocating writers. Constant segments (integer
    /// literals incl. erlc's wide folded strings, constant utf8) become
    /// static byte arrays written with one memcpy.
    pub(crate) fn compile_binary_construct(
        &self,
        f: FunctionValue<'ctx>,
        segs: &[mana_syntax::BinSegment<Box<Expr>>],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let specs = segs
            .iter()
            .map(|s| parse_seg_spec(&s.spec))
            .collect::<Result<Vec<_>, _>>()?;
        // sub-byte integer segments (Base's <<acc/binary, a::4, b::4, ...>>
        // decode loops): coalesce each maximal run into ONE byte-aligned
        // synthetic segment whose value is bsl/bor/band arithmetic over the
        // original exprs (left-folded — original evaluation order; band =
        // BEAM's truncation-to-size). Runs must end byte-aligned: a true
        // sub-byte bitstring RESULT has no representation here.
        if specs
            .iter()
            .any(|s| matches!(s.kind, SegKind::Int { size: SegSize::Bits(_) }))
        {
            let rewritten = coalesce_bit_runs(segs, &specs)?;
            return self.compile_binary_construct(f, &rewritten, scope);
        }
        // compile-time-known segment bytes
        let mut const_bytes: Vec<Option<Vec<u8>>> = Vec::with_capacity(specs.len());
        for (spec, seg) in specs.iter().zip(segs) {
            const_bytes.push(match &spec.kind {
                SegKind::Utf8 => match seg.value.as_ref() {
                    Expr::Lit(Literal::Int(cp)) => {
                        let c = char::from_u32(*cp as u32)
                            .ok_or("invalid utf8 code point in bitstring")?;
                        let mut buf = [0u8; 4];
                        Some(c.encode_utf8(&mut buf).as_bytes().to_vec())
                    }
                    _ => None,
                },
                SegKind::Int { size: SegSize::Bytes(n) } => {
                    seg_const_bytes(seg.value.as_ref(), *n, spec.little)?
                }
                SegKind::Int { size: SegSize::Bits(_) } => {
                    return Err(
                        "TODO(bitstring): sub-byte segments in construction".into()
                    )
                }
                SegKind::Int { size: SegSize::Dyn { .. } } => None,
                SegKind::Int { size: SegSize::All } => {
                    return Err("bitstring: integer segment with size 'all'".into())
                }
                SegKind::Bin { .. } => None,
            });
        }
        // every segment constant (string literals, <<>>): a static term —
        // no allocation, no writes
        if const_bytes.iter().all(|c| c.is_some()) {
            let all: Vec<u8> = const_bytes
                .iter()
                .flat_map(|c| c.as_ref().unwrap().iter().copied())
                .collect();
            return self.static_binary(&all);
        }
        // evaluate values (skipping const segments) and dynamic sizes, all
        // rooted — sizes are small ints but their exprs may allocate
        let nil_expr = Expr::Lit(Literal::Nil);
        let mut children: Vec<&Expr> = Vec::new();
        for ((spec, seg), cb) in specs.iter().zip(segs).zip(&const_bytes) {
            children.push(if cb.is_some() { &nil_expr } else { seg.value.as_ref() });
            match &spec.kind {
                SegKind::Int { size: SegSize::Dyn { size, .. } }
                | SegKind::Bin { size: SegSize::Dyn { size, .. } } if cb.is_none() => {
                    children.push(size)
                }
                _ => children.push(&nil_expr),
            }
        }
        let rooted = self.eval_all_rooted(f, &children, scope)?;
        let value_of = |i: usize| &rooted[2 * i];
        // total byte size
        let mut const_total: u64 = 0;
        for (i, spec) in specs.iter().enumerate() {
            match (&const_bytes[i], &spec.kind) {
                (Some(bytes), _) => const_total += bytes.len() as u64,
                (None, SegKind::Int { size: SegSize::Bytes(n) }) => const_total += n,
                _ => {}
            }
        }
        let mut total = self.i64t.const_int(const_total, false);
        let mut dyn_sizes: Vec<Option<IntValue<'ctx>>> = vec![None; specs.len()];
        for (i, spec) in specs.iter().enumerate() {
            if const_bytes[i].is_some() {
                continue;
            }
            let add = match &spec.kind {
                SegKind::Bin { size: SegSize::All } => {
                    let v = self.rooted_get(value_of(i))?;
                    let call = self
                        .builder
                        .build_call(
                            self.rt_pt_i64("mana_rt_byte_size"),
                            &[self.ctx_val().into(), v.into()],
                            "bsz",
                        )
                        .map_err(be)?;
                    let szt = call_result(call)?.into_int_value();
                    let szt = self.check_exc(f, szt)?;
                    Some(
                        self.builder
                            .build_right_shift(szt, self.i64t.const_int(3, false), true, "bsz.raw")
                            .map_err(be)?,
                    )
                }
                SegKind::Bin { size: sz @ SegSize::Dyn { .. } }
                | SegKind::Int { size: sz @ SegSize::Dyn { .. } } => {
                    // the size expr was pre-evaluated; re-wrap as a literal
                    // read from its slot
                    let szv = self.rooted_get(&rooted[2 * i + 1])?;
                    Some(self.seg_bytes_from_value(f, szv, sz)?)
                }
                SegKind::Utf8 => {
                    let v = self.rooted_get(value_of(i))?;
                    let call = self
                        .builder
                        .build_call(
                            self.rt_fn("mana_rt_utf8_width", || {
                                self.i64t.fn_type(
                                    &[BasicMetadataTypeEnum::IntType(self.i64t)],
                                    false,
                                )
                            }),
                            &[v.into()],
                            "u8w",
                        )
                        .map_err(be)?;
                    let w = call_result(call)?.into_int_value();
                    let ok = self
                        .builder
                        .build_int_compare(IntPredicate::NE, w, self.i64t.const_zero(), "u8w.ok")
                        .map_err(be)?;
                    self.guard_badarg(f, ok)?;
                    Some(w)
                }
                _ => None,
            };
            if let Some(a) = add {
                dyn_sizes[i] = Some(a);
                total = self.builder.build_int_add(total, a, "btot").map_err(be)?;
            }
        }
        // single GC point: values rooted, sizes are raw ints in SSA
        let alloc_name = if self.eternal_alloc.get() {
            "mana_rt_bin_alloc_eternal"
        } else {
            "mana_rt_bin_alloc"
        };
        let alloc_fn = self.rt_fn(alloc_name, || {
            self.i64t.fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        });
        let call = self
            .builder
            .build_call(alloc_fn, &[self.ctx_val().into(), total.into()], "bin")
            .map_err(be)?;
        let bin = call_result(call)?.into_int_value();
        // fill (writers never allocate); consecutive constant segments
        // (erlc emits string literals byte-per-segment) coalesce into a
        // single write
        let mut off = self.i64t.const_zero();
        let mut i = 0usize;
        while i < specs.len() {
            let spec = &specs[i];
            if const_bytes[i].is_some() {
                let mut run: Vec<u8> = Vec::new();
                while i < specs.len() {
                    match &const_bytes[i] {
                        Some(bytes) => {
                            run.extend_from_slice(bytes);
                            i += 1;
                        }
                        None => break,
                    }
                }
                let ptr = self.static_bytes(&run)?;
                self.builder
                    .build_call(
                        self.rt_fn("mana_rt_bin_write_bytes", || {
                            self.ctx.void_type().fn_type(
                                &[
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                                    BasicMetadataTypeEnum::IntType(self.i64t),
                                ],
                                false,
                            )
                        }),
                        &[
                            bin.into(),
                            off.into(),
                            ptr.into(),
                            self.i64t.const_int(run.len() as u64, false).into(),
                        ],
                        "",
                    )
                    .map_err(be)?;
                off = self
                    .builder
                    .build_int_add(off, self.i64t.const_int(run.len() as u64, false), "boff")
                    .map_err(be)?;
                continue;
            }
            let v = self.rooted_get(value_of(i))?;
            match &spec.kind {
                SegKind::Int { size } => {
                    let nbytes = match size {
                        SegSize::Bytes(n) => self.i64t.const_int(*n, false),
                        _ => dyn_sizes[i].unwrap(),
                    };
                    let call = self
                        .builder
                        .build_call(
                            self.rt_fn("mana_rt_bin_write_int", || {
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
                                bin.into(),
                                off.into(),
                                v.into(),
                                nbytes.into(),
                                self.i64t.const_int(spec.little as u64, false).into(),
                            ],
                            "bwi",
                        )
                        .map_err(be)?;
                    let r = call_result(call)?.into_int_value();
                    self.check_exc(f, r)?;
                    off = self.builder.build_int_add(off, nbytes, "boff").map_err(be)?;
                }
                SegKind::Bin { size } => {
                    let (adv, len_arg) = match size {
                        SegSize::All => (
                            dyn_sizes[i].unwrap(),
                            self.i64t.const_int(u64::MAX, false), // -1: whole
                        ),
                        SegSize::Bits(_) => {
                            return Err(
                                "TODO(bitstring): sub-byte binary segment".into()
                            )
                        }
                        SegSize::Bytes(n) => {
                            let c = self.i64t.const_int(*n, false);
                            (c, c)
                        }
                        SegSize::Dyn { .. } => {
                            let d = dyn_sizes[i].unwrap();
                            (d, d)
                        }
                    };
                    let call = self
                        .builder
                        .build_call(
                            self.rt_fn("mana_rt_bin_write_bin", || {
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
                            }),
                            &[
                                self.ctx_val().into(),
                                bin.into(),
                                off.into(),
                                v.into(),
                                len_arg.into(),
                            ],
                            "bwb",
                        )
                        .map_err(be)?;
                    let r = call_result(call)?.into_int_value();
                    self.check_exc(f, r)?;
                    off = self.builder.build_int_add(off, adv, "boff").map_err(be)?;
                }
                SegKind::Utf8 => {
                    let call = self
                        .builder
                        .build_call(
                            self.rt_fn("mana_rt_bin_write_utf8", || {
                                self.i64t.fn_type(
                                    &[
                                        BasicMetadataTypeEnum::IntType(self.i64t),
                                        BasicMetadataTypeEnum::IntType(self.i64t),
                                        BasicMetadataTypeEnum::IntType(self.i64t),
                                    ],
                                    false,
                                )
                            }),
                            &[bin.into(), off.into(), v.into()],
                            "bwu",
                        )
                        .map_err(be)?;
                    let w = call_result(call)?.into_int_value();
                    off = self.builder.build_int_add(off, w, "boff").map_err(be)?;
                }
            }
            i += 1;
        }
        Ok(bin)
    }

    /// seg_bytes for a pre-evaluated size term (construction path).
    pub(crate) fn seg_bytes_from_value(
        &self,
        f: FunctionValue<'ctx>,
        szv: IntValue<'ctx>,
        size: &SegSize,
    ) -> CgResult<IntValue<'ctx>> {
        let SegSize::Dyn { unit, .. } = size else {
            return Err("internal: seg_bytes_from_value on const size".into());
        };
        let tag = self.tag_of(szv)?;
        let is_int = self
            .builder
            .build_int_compare(
                IntPredicate::EQ,
                tag,
                self.i64t.const_int(TAG_SMALL, false),
                "sz.int",
            )
            .map_err(be)?;
        self.guard_badarg(f, is_int)?;
        let raw = self
            .builder
            .build_right_shift(szv, self.i64t.const_int(3, false), true, "sz.raw")
            .map_err(be)?;
        let bits = self
            .builder
            .build_int_mul(raw, self.i64t.const_int(*unit as u64, false), "sz.bits")
            .map_err(be)?;
        let low = self
            .builder
            .build_and(bits, self.i64t.const_int(7, false), "sz.low")
            .map_err(be)?;
        let aligned = self
            .builder
            .build_int_compare(IntPredicate::EQ, low, self.i64t.const_zero(), "sz.al")
            .map_err(be)?;
        let nonneg = self
            .builder
            .build_int_compare(IntPredicate::SGE, bits, self.i64t.const_zero(), "sz.nn")
            .map_err(be)?;
        let ok = self.builder.build_and(aligned, nonneg, "sz.ok").map_err(be)?;
        self.guard_badarg(f, ok)?;
        self.builder
            .build_right_shift(bits, self.i64t.const_int(3, false), false, "sz.bytes")
            .map_err(be)
    }

    /// A small constant binary term (e.g. io:nl's newline).
    pub(crate) fn compile_binary_const_term(
        &self,
        f: FunctionValue<'ctx>,
        bytes: &[u8],
        _scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let _ = f;
        self.static_binary(bytes)
    }
}
