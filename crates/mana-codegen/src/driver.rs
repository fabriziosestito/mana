use crate::*;

/// The content-addressed object cache (content-hash build-cache model). The
/// key of an entry is the "action": every input that feeds the object of a
/// module. The inputs are:
/// - the compiler binary itself
/// - the target and the codegen config
/// - the core text of the module
/// - its include set
/// - the effect verdicts of its remote callees
/// - the missing modules that it references
/// - whether it emits main
///
/// If a new input influences codegen, you MUST add it to the key. A key
/// that omits a codegen input is the canonical cache-poisoning bug.
pub struct ObjCache {
    pub root: PathBuf,
    /// The blake3 hash of the current compiler binary (dev-branch tool identity).
    pub tool_hash: [u8; 32],
    pub debug: bool,
}

impl ObjCache {
    pub(crate) fn path_for(&self, key: &blake3::Hash) -> PathBuf {
        let hex = key.to_hex();
        self.root
            .join("obj")
            .join(&hex.as_str()[..2])
            .join(format!("{}.o", hex))
    }

    /// Cache lookup. It refreshes the mtime of the entry at most once per
    /// hour. The age-based trim keeps the entries with a recent mtime.
    pub(crate) fn get(&self, key: &blake3::Hash) -> Option<PathBuf> {
        let p = self.path_for(key);
        let meta = std::fs::metadata(&p).ok()?;
        if let Ok(age) = meta.modified().and_then(|m| {
            m.elapsed()
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))
        }) {
            if age.as_secs() > 3600 {
                let _ = filetime_touch(&p);
            }
        }
        Some(p)
    }

    /// Idempotent publish: write to a temp file, then an atomic rename.
    /// Concurrent manac processes can duplicate work, but they cannot corrupt
    /// an entry. File locking is unreliable on network filesystems. This
    /// scheme needs no locks.
    pub(crate) fn put(&self, key: &blake3::Hash, obj: &Path) -> CgResult<PathBuf> {
        let dst = self.path_for(key);
        if let Some(parent) = dst.parent() {
            std::fs::create_dir_all(parent).map_err(|e| format!("cache dir: {}", e))?;
        }
        let tmp = dst.with_extension(format!("o.tmp-{}", std::process::id()));
        std::fs::copy(obj, &tmp).map_err(|e| format!("cache write: {}", e))?;
        std::fs::rename(&tmp, &dst).map_err(|e| format!("cache publish: {}", e))?;
        Ok(dst)
    }

    /// Age-based trim. At most once per 24h, it removes the entries with an
    /// mtime older than 30 days. It is best-effort. It ignores errors.
    pub fn trim(&self) {
        let stamp = self.root.join("obj").join("trim.stamp");
        if let Ok(meta) = std::fs::metadata(&stamp) {
            if let Ok(age) = meta.modified().and_then(|m| {
                m.elapsed()
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))
            }) {
                if age.as_secs() < 24 * 3600 {
                    return;
                }
            }
        }
        let cutoff = std::time::SystemTime::now() - std::time::Duration::from_secs(30 * 24 * 3600);
        if let Ok(buckets) = std::fs::read_dir(self.root.join("obj")) {
            for bucket in buckets.flatten() {
                if !bucket.path().is_dir() {
                    continue;
                }
                if let Ok(entries) = std::fs::read_dir(bucket.path()) {
                    for e in entries.flatten() {
                        if let Ok(meta) = e.metadata() {
                            if meta.modified().map(|m| m < cutoff).unwrap_or(false) {
                                let _ = std::fs::remove_file(e.path());
                            }
                        }
                    }
                }
            }
        }
        self.trim_summaries(cutoff);
        let _ = std::fs::write(&stamp, b"");
    }
}

pub(crate) fn filetime_touch(p: &Path) -> std::io::Result<()> {
    // Portable mtime refresh. A set_len to the current size updates the mtime.
    let f = std::fs::OpenOptions::new().append(true).open(p)?;
    let len = f.metadata()?.len();
    f.set_len(len)
}

/// Phase timings for one compile_program run. key_s and codegen_s are sums
/// across the Rayon workers (CPU time, not wall time).
pub struct CompileStats {
    pub reach_s: f64,
    pub gc_s: f64,
    pub raise_s: f64,
    pub key_s: f64,
    pub codegen_s: f64,
    pub hits: usize,
    pub misses: usize,
}

/// Compile a program to one object file per module in `out_dir`. Returns
/// the object paths. The compiler compiles only the functions that are
/// reachable from `entry` (closed world). A C `main` (init ctx, call entry)
/// lands in the object of the entry module. `poisoned` maps the names of
/// unparseable modules to their errors. These errors surface if reachability
/// needs them.
pub fn compile_program(
    units: &[ModuleUnit],
    entry_mod: &str,
    entry: &FunName,
    out_dir: &Path,
    dump_ir: bool,
    poisoned: &HashMap<String, String>,
    cache: Option<&ObjCache>,
    seed_exports: &[String],
) -> CgResult<(Vec<PathBuf>, CompileStats)> {
    if entry.arity != 0 {
        return Err(format!(
            "entry function {}/{} must have arity 0",
            entry.name, entry.arity
        ));
    }
    {
        let mut names = HashSet::new();
        for u in units {
            if !names.insert(&u.summary.name) {
                return Err(format!(
                    "module '{}' provided more than once",
                    u.summary.name
                ));
            }
        }
    }
    let t = std::time::Instant::now();
    let (reachable, missing_mods) =
        reachable_funs(units, entry_mod, entry, poisoned, seed_exports)?;
    let reach_s = t.elapsed().as_secs_f64();
    if std::env::var_os("MANA_DEBUG_REACH").is_some() {
        let mut v: Vec<String> = reachable
            .iter()
            .map(|(m, f)| format!("{}:{}/{}", m, f.name, f.arity))
            .collect();
        v.sort();
        for l in &v {
            eprintln!("manac: reach {}", l);
        }
    }
    let t = std::time::Instant::now();
    let gc_set = compute_may_gc(units, &reachable);
    let gc_s = t.elapsed().as_secs_f64();
    let t = std::time::Instant::now();
    let raise_set = compute_may_raise(units, &reachable);
    let raise_s = t.elapsed().as_secs_f64();
    // This builds the per-module include sets once. reachable has tens of
    // thousands of entries. A filter scan per module is quadratic.
    let mut includes: HashMap<&str, HashSet<FunName>> = HashMap::new();
    for (module, f) in &reachable {
        includes
            .entry(module.as_str())
            .or_default()
            .insert(f.clone());
    }

    std::fs::create_dir_all(out_dir)
        .map_err(|e| format!("creating {}: {}", out_dir.display(), e))?;
    // One LLVM Context per module, so the modules compile in parallel. Target
    // init is not thread-safe. It runs once, before the pool starts. The
    // workers get deep stacks because the AST walkers recurse per list element.
    Target::initialize_native(&InitializationConfig::default())
        .map_err(|e| format!("target init: {}", e))?;
    use rayon::prelude::*;
    let pool = rayon::ThreadPoolBuilder::new()
        .stack_size(256 * 1024 * 1024)
        .build()
        .map_err(|e| format!("thread pool: {}", e))?;
    let hits = std::sync::atomic::AtomicUsize::new(0);
    let misses = std::sync::atomic::AtomicUsize::new(0);
    let key_ns = std::sync::atomic::AtomicU64::new(0);
    let codegen_ns = std::sync::atomic::AtomicU64::new(0);
    let objs: Vec<PathBuf> = pool
        .install(|| {
            units
                .par_iter()
                .map(|u| -> CgResult<Option<PathBuf>> {
                    let mname = u.summary.name.as_str();
                    let Some(include) = includes.get(mname) else {
                        return Ok(None);
                    };
                    let entry_here = (mname == entry_mod).then_some(entry);
                    let tk = std::time::Instant::now();
                    let key = cache.map(|c| {
                        action_key(
                            c,
                            &u.summary,
                            &u.source_hash,
                            include,
                            entry_here,
                            &gc_set,
                            &raise_set,
                            &missing_mods,
                        )
                    });
                    key_ns.fetch_add(
                        tk.elapsed().as_nanos() as u64,
                        std::sync::atomic::Ordering::Relaxed,
                    );
                    if let (Some(c), Some(key)) = (cache, key.as_ref()) {
                        if let Some(cached) = c.get(key) {
                            hits.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            return Ok(Some(cached));
                        }
                    }
                    let tc = std::time::Instant::now();
                    // Object-cache miss. Only a miss needs the AST. If this run did not
                    // parse the module, the code reads the file again, checks its hash,
                    // and parses it here.
                    let reparsed: Module;
                    let m: &Module = match &u.ast {
                        Some(m) => m,
                        None => {
                            let src = std::fs::read_to_string(&u.path)
                                .map_err(|e| format!("re-reading {}: {}", u.path.display(), e))?;
                            if blake3::hash(src.as_bytes()).as_bytes() != &u.source_hash {
                                return Err(format!(
                                    "{}: file content changed during the build",
                                    u.path.display()
                                ));
                            }
                            reparsed = mana_syntax::parse_module(&src)
                                .map_err(|e| format!("re-parsing {}: {}", u.path.display(), e))?;
                            &reparsed
                        }
                    };
                    let context = Context::create();
                    let cg = Cg::new(&context, &m.name, &gc_set, &raise_set);
                    *cg.missing_modules.borrow_mut() = missing_mods.clone();
                    cg.is_entry_module.set(entry_here.is_some());
                    cg.compile(m, include, entry_here)?;
                    if dump_ir {
                        eprintln!("{}", cg.module.print_to_string().to_string());
                    }
                    cg.module
                        .verify()
                        .map_err(|e| format!("LLVM verifier ({}): {}", m.name, e))?;
                    let obj = out_dir.join(format!("{}.o", sanitize(&m.name)));
                    cg.emit_object(&obj)?;
                    codegen_ns.fetch_add(
                        tc.elapsed().as_nanos() as u64,
                        std::sync::atomic::Ordering::Relaxed,
                    );
                    misses.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if cache.map(|c| c.debug).unwrap_or(false) {
                        eprintln!("manac: cache miss: {}", m.name);
                    }
                    if let (Some(c), Some(key)) = (cache, key.as_ref()) {
                        return Ok(Some(c.put(key, &obj)?));
                    }
                    Ok(Some(obj))
                })
                .collect::<CgResult<Vec<_>>>()
        })?
        .into_iter()
        .flatten()
        .collect();
    let hits = hits.load(std::sync::atomic::Ordering::Relaxed);
    let misses = misses.load(std::sync::atomic::Ordering::Relaxed);
    if let Some(c) = cache {
        if c.debug {
            eprintln!("manac: cache: {} hits, {} misses", hits, misses);
        }
        c.trim();
    }
    Ok((
        objs,
        CompileStats {
            reach_s,
            gc_s,
            raise_s,
            key_s: key_ns.load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e9,
            codegen_s: codegen_ns.load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e9,
            hits,
            misses,
        },
    ))
}

/// The action key for the object of one module: a blake3 hash over every
/// input that can influence the emitted code. The encoding is deterministic.
/// The function sorts all sets before it hashes them.
pub(crate) fn action_key(
    cache: &ObjCache,
    m: &ModuleSummary,
    source_hash: &[u8; 32],
    include: &HashSet<FunName>,
    entry_here: Option<&FunName>,
    gc_set: &GcSet,
    raise_set: &GcSet,
    missing: &HashSet<String>,
) -> blake3::Hash {
    let debug_key = std::env::var("MANA_DEBUG_KEY")
        .ok()
        .filter(|d| d == &m.name);
    let mut h = blake3::Hasher::new();
    h.update(b"mana-action-v2\0");
    h.update(&cache.tool_hash);
    // Target and codegen config. They are constants today. They are in the
    // key for the day they change.
    h.update(TargetMachine::get_default_triple().as_str().to_bytes());
    h.update(b"O2/PIC\0");
    // Given tool_hash, the AST is a pure function of the source text, because
    // the parser lives in the manac binary. So the source hash keys the AST.
    h.update(source_hash);
    h.update(b"\0include\0");
    let mut inc: Vec<String> = include
        .iter()
        .map(|f| format!("{}/{}", f.name, f.arity))
        .collect();
    inc.sort();
    for f in &inc {
        h.update(f.as_bytes());
        h.update(b"\0");
    }
    match entry_here {
        Some(e) => {
            h.update(b"entry\0");
            h.update(e.name.as_bytes());
            h.update(b"\0");
        }
        None => {
            h.update(b"noentry\0");
        }
    }
    // Cross-unit deps: the (module, fun, arity, gc, raise) verdict of every
    // remote callee, plus the referenced modules that are missing. Callers of
    // a missing module compile as stubs.
    let mut dep_lines: Vec<String> = Vec::new();
    for fname in include {
        if let Some(fun) = m.funs.iter().find(|f| &f.name == fname) {
            for e in &fun.edges {
                if let Edge::Remote(tm, tf) = e {
                    if is_bif_module(tm) || is_native_module(tm) {
                        continue;
                    }
                    let key = (tm.clone(), tf.clone());
                    let gc = gc_set.contains(&key);
                    let rs = raise_set.contains(&key);
                    dep_lines.push(format!(
                        "{}:{}/{} {} {}",
                        tm, tf.name, tf.arity, gc as u8, rs as u8
                    ));
                }
            }
        }
    }
    dep_lines.sort();
    dep_lines.dedup();
    h.update(b"deps\0");
    for d in &dep_lines {
        h.update(d.as_bytes());
        h.update(b"\0");
    }
    let mut missing_hit: Vec<&String> = missing
        .iter()
        .filter(|mm| dep_lines.iter().any(|d| d.starts_with(&format!("{}:", mm))))
        .collect();
    missing_hit.sort();
    h.update(b"missing\0");
    for mm in &missing_hit {
        h.update(mm.as_bytes());
        h.update(b"\0");
    }
    if debug_key.is_some() {
        let mut inc2 = inc.clone();
        inc2.sort();
        eprintln!(
            "manac: key[{}]: include({})={:?} deps({})={:?} missing={:?}",
            m.name,
            inc2.len(),
            inc2,
            dep_lines.len(),
            dep_lines,
            missing_hit
        );
    }
    h.finalize()
}
