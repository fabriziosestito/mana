//! LLVM codegen for the sequential Core Erlang subset.
//!
//! Term representation matches mana-rt (see its crate docs): i64 words,
//! 3-bit tags — 001 small int, 010 atom ptr, 011 nil, 100 cons ptr,
//! 000 boxed ptr (kinds: 0 tuple, 1 float, 2 fun). Tag 111 is the GC
//! forwarding marker, never visible here.
//!
//! # Process-context ABI
//!
//! Every compiled function takes `ctx: ptr` (mana-rt's `ProcCtx`) as its
//! first argument. Codegen touches ctx only at word offset 2 (`roots_head`)
//! for the root-frame chain; allocation goes through `mana_rt_alloc(ctx, n)`
//! which may run a moving collection.
//!
//! # GC roots — effect analysis + frames + spills
//!
//! A term held in an SSA register is invalid after any *GC point* (a call
//! into compiled code that may allocate, or an allocation). Three layers
//! keep this sound without paying where it doesn't matter:
//!
//! 1. Whole-program **may-GC analysis** (fixpoint over the call graph):
//!    functions whose bodies can't reach an allocation get **no frame and
//!    no spills** — pure register code (fib stays fast).
//! 2. Framed functions alloca a root frame `[prev, len, slots...]`, link it
//!    into `ctx.roots_head` on entry and unlink before every return
//!    (including before tail calls). Slots are NIL-initialized; all named
//!    variables live in slots; reads load, binds store.
//! 3. Intermediates are spilled **structurally**: a sibling value is rooted
//!    only if a later sibling's evaluation contains a GC point; children of
//!    an allocation (tuple/cons/closure) are always rooted because the
//!    allocation itself is a GC point. Call arguments consumed by a callee
//!    need no rooting across that call (the callee roots its own params).
//!    TODO(liveness): per-variable liveness to shrink frames further.
//!
//! A program is one or more Core Erlang modules compiled to one object file
//! per module. Atoms are `linkonce_odr` globals (linker-deduplicated,
//! static, never collected). Closures are lambda-lifted in closure-passing
//! style: lifted signature `(ctx, args..., closure)`.
//!
//! TODO(lco): tailcc + musttail for guaranteed cross-function tail calls.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::{Path, PathBuf};

use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module as LlvmModule};
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine,
};
use inkwell::types::{BasicMetadataTypeEnum, FunctionType, IntType, PointerType};
use inkwell::values::{
    BasicMetadataValueEnum, BasicValue, CallSiteValue, FunctionValue, GlobalValue,
    InstructionValue, IntValue, PointerValue, ValueKind,
};
use inkwell::AddressSpace;
use inkwell::IntPredicate;
use inkwell::OptimizationLevel;

use mana_syntax::{ApplyTarget, Clause, Expr, Fun, FunName, Literal, MapAssoc, Module, Pattern};

const TAG_SMALL: u64 = 0b001;
const TAG_ATOM: u64 = 0b010;
const NIL: u64 = 0b011;
const TAG_CONS: u64 = 0b100;
const TAG_MASK: u64 = 0b111;
const KIND_TUPLE: u64 = 0;
const KIND_FLOAT: u64 = 1;
const KIND_FUN: u64 = 2;
const KIND_MAP: u64 = 4;
const KIND_BIN: u64 = 5;

/// ctx word offsets (ProcCtx contract).
const CTX_ROOTS: u64 = 2;
const CTX_EXC_CLASS: u64 = 3;
const CTX_EXC_REASON: u64 = 4;
const CTX_REDUCTIONS: u64 = 5;
/// Reserved non-term word (tag 0b101): "an exception is unwinding".
const EXC_SENTINEL: u64 = 0b101;

type CgResult<T> = Result<T, String>;
type GcSet = HashSet<(String, FunName)>;

/// Disjoint memory classes for TBAA (never alias each other).
#[derive(Clone, Copy)]
enum MemKind {
    Ctx,
    Frame,
    Heap,
}

/// Where a variable's current value lives.
#[derive(Clone, Copy)]
enum Binding<'ctx> {
    /// Frame slot index (framed functions — survives GC).
    Slot(u64),
    /// SSA value (frameless functions — no GC can occur).
    Reg(IntValue<'ctx>),
}

#[derive(Clone, Default)]
struct Scope<'ctx> {
    vars: HashMap<String, Binding<'ctx>>,
    /// letrec-bound funs: lifted function + frame slot of the shared closure.
    funs: HashMap<FunName, (FunctionValue<'ctx>, u64)>,
}

/// A lambda-lifted function whose body still needs compiling.
struct Lift {
    f_index: usize,
    params: Vec<String>,
    captures: Vec<String>,
    sibs: Vec<(FunName, usize)>,
    body: Expr,
}

/// Compile a program to one object file per module in `out_dir`; returns
/// the object paths. Only functions reachable from `entry` are compiled
/// (closed world). A C `main` (init ctx, call entry) lands in the entry
/// module's object. `poisoned` maps unparseable module names to their
/// errors, surfaced if reachability needs them.
/// The content-addressed object cache (Go's build-cache model). An entry
/// is keyed by the "action": everything that feeds a module's object —
/// the compiler binary itself, the target/config, the module's core text,
/// its include set, the effect verdicts of its remote callees, the missing
/// modules it references, and whether it emits main. Anything new that
/// influences codegen MUST be added to the key (Go's cgo caching bug is
/// the canonical omission).
pub struct ObjCache {
    pub root: PathBuf,
    /// blake3 of the running compiler binary (dev-branch tool identity)
    pub tool_hash: [u8; 32],
    pub debug: bool,
}

impl ObjCache {
    fn path_for(&self, key: &blake3::Hash) -> PathBuf {
        let hex = key.to_hex();
        self.root
            .join("obj")
            .join(&hex.as_str()[..2])
            .join(format!("{}.o", hex))
    }

    /// Cache lookup; refreshes the entry's mtime (age-based trim keeps
    /// recently-used entries) at most ~hourly.
    fn get(&self, key: &blake3::Hash) -> Option<PathBuf> {
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

    /// Idempotent publish: write-to-temp + atomic rename. Concurrent manac
    /// processes may duplicate effort but cannot corrupt entries. (File
    /// locking is notoriously unreliable on network filesystems — this
    /// scheme needs none.)
    fn put(&self, key: &blake3::Hash, obj: &Path) -> CgResult<PathBuf> {
        let dst = self.path_for(key);
        if let Some(parent) = dst.parent() {
            std::fs::create_dir_all(parent).map_err(|e| format!("cache dir: {}", e))?;
        }
        let tmp = dst.with_extension(format!("o.tmp-{}", std::process::id()));
        std::fs::copy(obj, &tmp).map_err(|e| format!("cache write: {}", e))?;
        std::fs::rename(&tmp, &dst).map_err(|e| format!("cache publish: {}", e))?;
        Ok(dst)
    }

    /// Age-based trim, Go-style: at most once per 24h, drop entries not
    /// used (mtime) for 30 days. Best-effort — errors are ignored.
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
        let _ = std::fs::write(&stamp, b"");
    }
}

fn filetime_touch(p: &Path) -> std::io::Result<()> {
    // portable mtime refresh: open for append and set_len to current size
    let f = std::fs::OpenOptions::new().append(true).open(p)?;
    let len = f.metadata()?.len();
    f.set_len(len)
}

/// Phase timings for one compile_program run. key/codegen are summed across
/// Rayon workers (CPU time, not wall).
pub struct CompileStats {
    pub reach_s: f64,
    pub gc_s: f64,
    pub raise_s: f64,
    pub key_s: f64,
    pub codegen_s: f64,
    pub hits: usize,
    pub misses: usize,
}

pub fn compile_program(
    mods: &[Module],
    source_hashes: &[[u8; 32]],
    entry_mod: &str,
    entry: &FunName,
    out_dir: &Path,
    dump_ir: bool,
    poisoned: &HashMap<String, String>,
    cache: Option<&ObjCache>,
    seed_exports: &[String],
) -> CgResult<(Vec<PathBuf>, CompileStats)> {
    assert_eq!(mods.len(), source_hashes.len());
    if entry.arity != 0 {
        return Err(format!(
            "entry function {}/{} must have arity 0",
            entry.name, entry.arity
        ));
    }
    {
        let mut names = HashSet::new();
        for m in mods {
            if !names.insert(&m.name) {
                return Err(format!("module '{}' provided more than once", m.name));
            }
        }
    }
    let t = std::time::Instant::now();
    let (reachable, missing_mods) =
        reachable_funs(mods, entry_mod, entry, poisoned, seed_exports)?;
    let reach_s = t.elapsed().as_secs_f64();
    let t = std::time::Instant::now();
    let gc_set = compute_may_gc(mods, &reachable);
    let gc_s = t.elapsed().as_secs_f64();
    let t = std::time::Instant::now();
    let raise_set = compute_may_raise(mods, &reachable);
    let raise_s = t.elapsed().as_secs_f64();
    // per-module include sets, built once (reachable is tens of thousands
    // of entries — a per-module filter scan is quadratic)
    let mut includes: HashMap<&str, HashSet<FunName>> = HashMap::new();
    for (module, f) in &reachable {
        includes
            .entry(module.as_str())
            .or_default()
            .insert(f.clone());
    }

    std::fs::create_dir_all(out_dir)
        .map_err(|e| format!("creating {}: {}", out_dir.display(), e))?;
    // one LLVM Context per module → modules compile in parallel. Target
    // init is not thread-safe — do it once, up front; workers get deep
    // stacks (AST walkers recurse per list element).
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
    let objs: Vec<PathBuf> = pool.install(|| mods
        .par_iter()
        .enumerate()
        .map(|(mi, m)| -> CgResult<Option<PathBuf>> {
            let Some(include) = includes.get(m.name.as_str()) else {
                return Ok(None);
            };
            let entry_here = (m.name == entry_mod).then_some(entry);
            let tk = std::time::Instant::now();
            let key = cache.map(|c| {
                action_key(
                    c,
                    m,
                    &source_hashes[mi],
                    &include,
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
            let context = Context::create();
            let cg = Cg::new(&context, &m.name, &gc_set, &raise_set);
            *cg.missing_modules.borrow_mut() = missing_mods.clone();
            cg.is_entry_module.set(entry_here.is_some());
            cg.compile(m, &include, entry_here)?;
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
        .collect::<CgResult<Vec<_>>>())?
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

/// The action key for one module's object: a blake3 hash over every input
/// that can influence the emitted code. Deterministic encoding — all sets
/// are sorted before hashing.
fn action_key(
    cache: &ObjCache,
    m: &Module,
    source_hash: &[u8; 32],
    include: &HashSet<FunName>,
    entry_here: Option<&FunName>,
    gc_set: &GcSet,
    raise_set: &GcSet,
    missing: &HashSet<String>,
) -> blake3::Hash {
    let debug_key = std::env::var("MANA_DEBUG_KEY").ok().filter(|d| d == &m.name);
    let mut h = blake3::Hasher::new();
    h.update(b"mana-action-v2\0");
    h.update(&cache.tool_hash);
    // target + codegen config (constants today; keyed for the day they move)
    h.update(TargetMachine::get_default_triple().as_str().to_bytes());
    h.update(b"O2/PIC\0");
    // the AST is a pure function of the source text given tool_hash (the
    // parser lives in the manac binary), so the source hash keys it
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
    // cross-unit deps: the (module, fun, arity, gc, raise) verdict of every
    // remote callee, plus referenced-but-missing modules (callers of those
    // compile as stubs)
    let mut dep_lines: Vec<String> = Vec::new();
    for fname in include {
        if let Some((_, fun)) = m.definitions.iter().find(|(f, _)| f == fname) {
            let mut edges = Vec::new();
            let mut lb = HashSet::new();
            collect_edges(&fun.body, &mut edges, &mut lb);
            for e in edges {
                if let Edge::Remote(tm, tf) = e {
                    if is_bif_module(&tm) {
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

struct Cg<'ctx, 'p> {
    ctx: &'ctx Context,
    module: LlvmModule<'ctx>,
    builder: Builder<'ctx>,
    i64t: IntType<'ctx>,
    ptrt: PointerType<'ctx>,
    fns: RefCell<HashMap<FunName, FunctionValue<'ctx>>>,
    atoms: RefCell<HashMap<String, GlobalValue<'ctx>>>,
    lifted: RefCell<Vec<FunctionValue<'ctx>>>,
    pending: RefCell<Vec<Lift>>,
    lift_counter: Cell<u32>,
    module_name: String,
    gc_set: &'p GcSet,
    raise_set: &'p GcSet,
    // TBAA: ctx words / frame slots / heap objects never alias
    tbaa_kind: u32,
    tbaa_ctx: inkwell::values::MetadataValue<'ctx>,
    tbaa_frame: inkwell::values::MetadataValue<'ctx>,
    tbaa_heap: inkwell::values::MetadataValue<'ctx>,
    // per-function state
    cur_ctx: Cell<Option<PointerValue<'ctx>>>,
    cur_frame: Cell<Option<PointerValue<'ctx>>>,
    /// raise-path compilation: allocations go to the eternal allocator
    eternal_alloc: Cell<bool>,
    /// unique-name counter for static byte arrays (wide segment constants)
    static_bytes_count: Cell<usize>,
    /// exported functions compiled in this module → mana_exports entries
    exports: RefCell<Vec<(FunName, FunctionValue<'ctx>)>>,
    /// modules the program references but that are not compiled: calls to
    /// them poison the calling function (stub) instead of failing the build
    missing_modules: RefCell<HashSet<String>>,
    /// (module, behaviour) pairs for the mana_behaviours section
    behaviours: RefCell<Vec<(String, String)>>,
    is_entry_module: Cell<bool>,
    /// innermost enclosing try handler blocks (current function)
    handlers: RefCell<Vec<BasicBlock<'ctx>>>,
    /// lazily created per-function "pop frame; return sentinel" block
    propagate_bb: Cell<Option<BasicBlock<'ctx>>>,
    var_slots: RefCell<HashMap<String, u64>>,
    next_slot: Cell<u64>,
    slot_cap: Cell<u64>,
    /// slot high-water mark: frame len + memset are patched down to this
    /// once the body is compiled (the prepass cap is an over-approximation)
    peak_slot: Cell<u64>,
    frame_memset: Cell<Option<InstructionValue<'ctx>>>,
    frame_len_store: Cell<Option<InstructionValue<'ctx>>>,
    /// leading slots holding params/captures — written before the first GC
    /// point, so the entry memset skips them
    frame_skip: Cell<u64>,
}

impl<'ctx, 'p> Cg<'ctx, 'p> {
    fn new(
        ctx: &'ctx Context,
        module_name: &str,
        gc_set: &'p GcSet,
        raise_set: &'p GcSet,
    ) -> Self {
        let module = ctx.create_module(module_name);
        // TBAA tree: three disjoint scalar classes under one root. Lets LLVM
        // keep heap_top/frame slots in registers across heap stores.
        let i64t = ctx.i64_type();
        let root = ctx.metadata_node(&[ctx.metadata_string("mana-tbaa").into()]);
        let mk_tag = |name: &str| {
            let ty = ctx.metadata_node(&[
                ctx.metadata_string(name).into(),
                root.into(),
                i64t.const_zero().into(),
            ]);
            ctx.metadata_node(&[ty.into(), ty.into(), i64t.const_zero().into()])
        };
        let tbaa_ctx = mk_tag("procctx");
        let tbaa_frame = mk_tag("gcframe");
        let tbaa_heap = mk_tag("heap");
        Cg {
            ctx,
            module,
            builder: ctx.create_builder(),
            i64t: ctx.i64_type(),
            ptrt: ctx.ptr_type(AddressSpace::default()),
            fns: Default::default(),
            atoms: Default::default(),
            lifted: Default::default(),
            pending: Default::default(),
            lift_counter: Cell::new(0),
            module_name: module_name.to_string(),
            gc_set,
            raise_set,
            tbaa_kind: ctx.get_kind_id("tbaa"),
            tbaa_ctx,
            tbaa_frame,
            tbaa_heap,
            cur_ctx: Cell::new(None),
            cur_frame: Cell::new(None),
            eternal_alloc: Cell::new(false),
            static_bytes_count: Cell::new(0),
            exports: RefCell::new(Vec::new()),
            missing_modules: RefCell::new(HashSet::new()),
            behaviours: RefCell::new(Vec::new()),
            is_entry_module: Cell::new(false),
            handlers: RefCell::new(Vec::new()),
            propagate_bb: Cell::new(None),
            var_slots: Default::default(),
            next_slot: Cell::new(0),
            slot_cap: Cell::new(0),
            peak_slot: Cell::new(0),
            frame_memset: Cell::new(None),
            frame_len_store: Cell::new(None),
            frame_skip: Cell::new(0),
        }
    }

    /// `(ctx, term × arity) -> term`
    fn term_fn_type(&self, arity: usize) -> FunctionType<'ctx> {
        let mut params: Vec<BasicMetadataTypeEnum> =
            vec![BasicMetadataTypeEnum::PointerType(self.ptrt)];
        params.extend((0..arity).map(|_| BasicMetadataTypeEnum::IntType(self.i64t)));
        self.i64t.fn_type(&params, false)
    }

    fn ctx_val(&self) -> PointerValue<'ctx> {
        self.cur_ctx.get().expect("ctx param not set")
    }

    fn framed(&self) -> bool {
        self.cur_frame.get().is_some()
    }

    fn expr_gc(&self, e: &Expr) -> bool {
        let mut letrec = HashSet::new();
        expr_may_gc(e, &self.module_name, self.gc_set, &mut letrec)
    }

    // ---- runtime externs ----

    fn rt_fn(
        &self,
        name: &str,
        mk: impl FnOnce() -> FunctionType<'ctx>,
    ) -> FunctionValue<'ctx> {
        self.module
            .get_function(name)
            .unwrap_or_else(|| self.module.add_function(name, mk(), None))
    }

    fn rt_init(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_init", || self.ptrt.fn_type(&[], false))
    }

    fn rt_display(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_display", || {
            self.ctx
                .void_type()
                .fn_type(&[BasicMetadataTypeEnum::IntType(self.i64t)], false)
        })
    }

    fn rt_alloc_slow(&self) -> FunctionValue<'ctx> {
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

    fn rt_alloc_eternal(&self) -> FunctionValue<'ctx> {
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

    fn rt_p_i64(&self, name: &str) -> FunctionValue<'ctx> {
        self.rt_fn(name, || {
            self.i64t
                .fn_type(&[BasicMetadataTypeEnum::PointerType(self.ptrt)], false)
        })
    }

    fn rt_p_void(&self, name: &str) -> FunctionValue<'ctx> {
        self.rt_fn(name, || {
            self.ctx
                .void_type()
                .fn_type(&[BasicMetadataTypeEnum::PointerType(self.ptrt)], false)
        })
    }

    fn rt_register_atoms(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_register_atoms", || {
            let params: Vec<BasicMetadataTypeEnum> =
                (0..20).map(|_| BasicMetadataTypeEnum::IntType(self.i64t)).collect();
            self.ctx.void_type().fn_type(&params, false)
        })
    }

    /// (ctx, term) -> term runtime BIF helper.
    fn rt_pt_i64(&self, name: &str) -> FunctionValue<'ctx> {
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

    fn rt_run(&self) -> FunctionValue<'ctx> {
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

    fn rt_spawn(&self) -> FunctionValue<'ctx> {
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

    fn rt_send(&self) -> FunctionValue<'ctx> {
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

    fn rt_recv_wait(&self) -> FunctionValue<'ctx> {
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

    fn rt_uncaught(&self) -> FunctionValue<'ctx> {
        self.rt_fn("mana_rt_uncaught", || {
            self.ctx
                .void_type()
                .fn_type(&[BasicMetadataTypeEnum::PointerType(self.ptrt)], false)
        })
    }

    // ---- constants ----

    fn small_int(&self, n: i64) -> IntValue<'ctx> {
        // TODO(bignum): values outside the small range wrap silently.
        self.i64t.const_int(((n as u64) << 3) | TAG_SMALL, false)
    }

    fn nil(&self) -> IntValue<'ctx> {
        self.i64t.const_int(NIL, false)
    }

    /// The (deduped, linkonce_odr) atom struct global for `name`. Creating it
    /// also puts the atom into the program's closed-world atom table.
    fn atom_global(&self, name: &str) -> GlobalValue<'ctx> {
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

    fn atom_term(&self, name: &str) -> CgResult<IntValue<'ctx>> {
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
    fn static_binary(&self, bytes: &[u8]) -> CgResult<IntValue<'ctx>> {
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

    // ---- frames & slots ----

    /// Set up the root frame for the function whose entry block the builder
    /// is positioned in. `body` decides framedness; `var_names` are all
    /// names that may be bound (params, captures, body binds).
    fn setup_frame(
        &self,
        body: &Expr,
        var_names: &[String],
        letrec_sibs: &[FunName],
    ) -> CgResult<()> {
        self.var_slots.borrow_mut().clear();
        self.frame_memset.set(None);
        self.frame_len_store.set(None);
        self.frame_skip.set(0);
        let mut letrec: HashSet<FunName> = letrec_sibs.iter().cloned().collect();
        if !expr_may_gc(body, &self.module_name, self.gc_set, &mut letrec) {
            self.cur_frame.set(None);
            return Ok(());
        }

        let mut vars: BTreeSet<String> = var_names.iter().cloned().collect();
        let mut nodes = 0usize;
        frame_prepass(body, &mut vars, &mut nodes);
        let nvars = vars.len() as u64;
        let cap = nvars + nodes as u64 + 8;

        // var_names (params/captures) take the leading slots: every caller
        // stores them right after this returns, before the first GC point,
        // so the zeroing memset can skip them
        let skip;
        {
            let mut slots = self.var_slots.borrow_mut();
            for v in var_names {
                if !slots.contains_key(v) {
                    let i = slots.len() as u64;
                    slots.insert(v.clone(), i);
                }
            }
            skip = slots.len() as u64;
            for v in vars.iter() {
                if !slots.contains_key(v.as_str()) {
                    let i = slots.len() as u64;
                    slots.insert(v.clone(), i);
                }
            }
        }
        self.next_slot.set(nvars);
        self.slot_cap.set(cap);
        self.peak_slot.set(nvars);
        self.frame_skip.set(skip);

        let frame_ty = self.i64t.array_type((cap + 2) as u32);
        let frame = self
            .builder
            .build_alloca(frame_ty, "gc.frame")
            .map_err(be)?;
        let ctx = self.ctx_val();
        let prev = self.mem_load(ctx, CTX_ROOTS, MemKind::Ctx)?;
        self.mem_store(frame, 0, prev, MemKind::Frame)?;
        // len: placeholder — patched down to the slot high-water mark once
        // the body is compiled (see patch_frame)
        let len_slot = unsafe {
            self.builder
                .build_in_bounds_gep(
                    self.i64t,
                    frame,
                    &[self.i64t.const_int(1, false)],
                    "len",
                )
                .map_err(be)?
        };
        let len_store = self
            .builder
            .build_store(len_slot, self.i64t.const_int(cap, false))
            .map_err(be)?;
        let _ = len_store.set_metadata(self.tbaa_frame, self.tbaa_kind);
        self.frame_len_store.set(Some(len_store));
        // zero-init the non-prebound slots with one memset — 0 marks an
        // empty slot the collector skips (cheaper than storing NIL per
        // slot). Size is a placeholder patched in patch_frame.
        let slots = unsafe {
            self.builder
                .build_in_bounds_gep(
                    self.i64t,
                    frame,
                    &[self.i64t.const_int(2 + skip, false)],
                    "slots",
                )
                .map_err(be)?
        };
        let ms = self
            .builder
            .build_memset(
                slots,
                8,
                self.ctx.i8_type().const_zero(),
                self.i64t.const_int((cap - skip) * 8, false),
            )
            .map_err(be)?;
        self.frame_memset.set(ms.as_instruction());
        let frame_int = self
            .builder
            .build_ptr_to_int(frame, self.i64t, "frame.addr")
            .map_err(be)?;
        self.mem_store(ctx, CTX_ROOTS, frame_int, MemKind::Ctx)?;
        self.cur_frame.set(Some(frame));
        Ok(())
    }

    /// After the body is compiled the true slot high-water mark is known:
    /// shrink the frame len and the entry memset from the prepass cap
    /// (an over-approximation) down to it. The alloca keeps the padded
    /// size — untouched stack costs nothing.
    fn patch_frame(&self) {
        let peak = self.peak_slot.get();
        if let Some(ls) = self.frame_len_store.take() {
            let ok = ls.set_operand(0, self.i64t.const_int(peak, false));
            debug_assert!(ok, "frame len store operand patch failed");
        }
        if let Some(ms) = self.frame_memset.take() {
            let skip = self.frame_skip.get();
            let ok = ms.set_operand(2, self.i64t.const_int((peak - skip) * 8, false));
            debug_assert!(ok, "frame memset size operand patch failed");
        }
    }

    /// Unlink the frame (before any return or tail call).
    fn pop_frame(&self) -> CgResult<()> {
        if let Some(frame) = self.cur_frame.get() {
            let prev = self.mem_load(frame, 0, MemKind::Frame)?;
            self.mem_store(self.ctx_val(), CTX_ROOTS, prev, MemKind::Ctx)?;
        }
        Ok(())
    }

    fn emit_ret(&self, v: IntValue<'ctx>) -> CgResult<()> {
        self.pop_frame()?;
        self.builder.build_return(Some(&v)).map_err(be)?;
        Ok(())
    }

    fn sentinel(&self) -> IntValue<'ctx> {
        self.i64t.const_int(EXC_SENTINEL, false)
    }

    /// Where an unwinding exception goes: the innermost try handler, or the
    /// per-function propagate block (unlink frame, return the sentinel).
    fn unwind_target(&self, f: FunctionValue<'ctx>) -> CgResult<BasicBlock<'ctx>> {
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

    /// Store class/reason into the ctx and jump to the unwind target.
    /// Leaves the builder in a fresh dead block.
    fn emit_raise(
        &self,
        f: FunctionValue<'ctx>,
        class: IntValue<'ctx>,
        reason: IntValue<'ctx>,
    ) -> CgResult<()> {
        // poor man's stacktrace, raise flavor (MANA_DEBUG_RAISE)
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

    /// After a call to a may-raise function: branch to the unwind target if
    /// the sentinel came back.
    fn check_exc(
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

    /// Build an eternal (non-moving) 2-tuple for an exception reason.
    fn eternal_pair(
        &self,
        tag: &str,
        v: IntValue<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let call = self
            .builder
            .build_call(
                self.rt_alloc_eternal(),
                &[
                    self.ctx_val().into(),
                    self.i64t.const_int(3, false).into(),
                    self.i64t.const_zero().into(),
                ],
                "exc.reason",
            )
            .map_err(be)?;
        let p = call_result(call)?.into_pointer_value();
        self.store_word(p, 0, self.i64t.const_int((2 << 8) | KIND_TUPLE, false))?;
        let tag_atom = self.atom_term(tag)?;
        self.store_word(p, 1, tag_atom)?;
        self.store_word(p, 2, v)?;
        self.builder.build_ptr_to_int(p, self.i64t, "reason").map_err(be)
    }

    /// Inline flatmap lookup for a key whose equality is bit-identity
    /// (atoms, smalls, nil). The subject must already be known to be a map.
    /// Misses branch to `fail`; returns the value on the hit path.
    fn inline_map_get(
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

    fn slot_ptr(&self, idx: u64) -> CgResult<PointerValue<'ctx>> {
        let frame = self.cur_frame.get().expect("slot in frameless function");
        unsafe {
            self.builder
                .build_in_bounds_gep(
                    self.i64t,
                    frame,
                    &[self.i64t.const_int(2 + idx, false)],
                    "slot",
                )
                .map_err(be)
        }
    }

    fn alloc_temp(&self) -> u64 {
        let n = self.next_slot.get();
        assert!(n < self.slot_cap.get(), "frame slot capacity exceeded");
        self.next_slot.set(n + 1);
        if n + 1 > self.peak_slot.get() {
            self.peak_slot.set(n + 1);
        }
        n
    }

    fn spill(&self, v: IntValue<'ctx>) -> CgResult<u64> {
        let idx = self.alloc_temp();
        let p = self.slot_ptr(idx)?;
        let inst = self.builder.build_store(p, v).map_err(be)?;
        let _ = inst.set_metadata(self.tbaa_frame, self.tbaa_kind);
        Ok(idx)
    }

    fn reload(&self, idx: u64) -> CgResult<IntValue<'ctx>> {
        let p = self.slot_ptr(idx)?;
        let v = self.builder.build_load(self.i64t, p, "reload").map_err(be)?;
        if let Some(inst) = v.as_instruction_value() {
            let _ = inst.set_metadata(self.tbaa_frame, self.tbaa_kind);
        }
        Ok(v.into_int_value())
    }

    fn bind_var(&self, scope: &mut Scope<'ctx>, name: &str, v: IntValue<'ctx>) -> CgResult<()> {
        if self.framed() {
            let idx = *self
                .var_slots
                .borrow()
                .get(name)
                .unwrap_or_else(|| panic!("no slot preassigned for variable {}", name));
            let p = self.slot_ptr(idx)?;
            let inst = self.builder.build_store(p, v).map_err(be)?;
            let _ = inst.set_metadata(self.tbaa_frame, self.tbaa_kind);
            scope.vars.insert(name.to_string(), Binding::Slot(idx));
        } else {
            scope.vars.insert(name.to_string(), Binding::Reg(v));
        }
        Ok(())
    }

    fn read_var(&self, scope: &Scope<'ctx>, name: &str) -> CgResult<IntValue<'ctx>> {
        match scope.vars.get(name) {
            Some(Binding::Reg(v)) => Ok(*v),
            Some(Binding::Slot(idx)) => self.reload(*idx),
            None => Err(format!("unbound variable {}", name)),
        }
    }

    // ---- module compilation ----

    fn compile(
        &self,
        ast: &Module,
        include: &HashSet<FunName>,
        entry: Option<&FunName>,
    ) -> CgResult<()> {
        // module and function names are atoms on BEAM (so they satisfy
        // binary_to_existing_atom, and S4's export table will need them)
        self.atom_global(&ast.name);
        for b in &ast.behaviours {
            self.atom_global(b);
            self.behaviours
                .borrow_mut()
                .push((ast.name.clone(), b.clone()));
        }
        for (fname, _) in &ast.definitions {
            if include.contains(fname) {
                self.atom_global(&fname.name);
            }
        }
        let exported: HashSet<&FunName> = ast.exports.iter().collect();
        for (fname, fun) in &ast.definitions {
            if !include.contains(fname) {
                continue;
            }
            let f = self.module.add_function(
                &mangle(&self.module_name, fname),
                self.term_fn_type(fun.params.len()),
                None,
            );
            self.fns.borrow_mut().insert(fname.clone(), f);
            if exported.contains(fname) && fname.name != "module_info" {
                self.exports.borrow_mut().push((fname.clone(), f));
            }
        }

        for (fname, fun) in &ast.definitions {
            if !include.contains(fname) {
                continue;
            }
            if self.emit_native_override(fname)? {
                continue;
            }
            if let Err(e) = self.compile_fn(fname, fun) {
                // Function-granular poisoning: stdlib modules contain
                // corners we don't compile yet (sub-byte bitstrings, ...).
                // The function becomes a stub that reports and exits if a
                // program ever actually reaches it. Lifts it had already
                // queued get stubbed too (they were declared).
                eprintln!(
                    "manac: warning: {}:{}/{} stubbed (unsupported: {})",
                    self.module_name, fname.name, fname.arity, e
                );
                let msg =
                    format!("{}:{}/{}: {}", self.module_name, fname.name, fname.arity, e);
                let fv = self.fns.borrow()[fname];
                self.emit_unsupported_stub(fv, &msg)?;
                loop {
                    let next = self.pending.borrow_mut().pop();
                    let Some(l) = next else { break };
                    let lf = self.lifted.borrow()[l.f_index];
                    self.emit_unsupported_stub(lf, &msg)?;
                }
            }
            self.drain_lifts()?;
        }

        match entry {
            Some(e) => self.emit_main(e),
            None => Ok(()),
        }
    }

    /// Wipe a half-compiled function and replace its body with a loud
    /// runtime failure (print + exit). Aborting rather than raising keeps
    /// the may-raise analysis consistent (callers may not check).
    fn emit_unsupported_stub(&self, f: FunctionValue<'ctx>, msg: &str) -> CgResult<()> {
        // Never delete half-built blocks: erasing a block that another
        // block still branches to corrupts the module (LLVM erase does not
        // fix up uses — this manifested as glibc heap corruption). Instead,
        // terminate every unterminated block and prepend a fresh entry;
        // the old body becomes unreachable garbage that O2 removes.
        for bb in f.get_basic_blocks() {
            if bb.get_terminator().is_none() {
                self.builder.position_at_end(bb);
                self.builder.build_unreachable().map_err(be)?;
            }
        }
        let entry = match f.get_first_basic_block() {
            Some(first) => self
                .ctx
                .prepend_basic_block(first, "stub.entry"),
            None => self.ctx.append_basic_block(f, "entry"),
        };
        self.builder.position_at_end(entry);
        let ptr = self.static_bytes(msg.as_bytes())?;
        let callee = self.rt_fn("mana_rt_unsupported", || {
            self.ctx.void_type().fn_type(
                &[
                    BasicMetadataTypeEnum::PointerType(self.ptrt),
                    BasicMetadataTypeEnum::IntType(self.i64t),
                ],
                false,
            )
        });
        self.builder
            .build_call(
                callee,
                &[
                    ptr.into(),
                    self.i64t.const_int(msg.len() as u64, false).into(),
                ],
                "",
            )
            .map_err(be)?;
        self.builder.build_unreachable().map_err(be)?;
        Ok(())
    }

    /// Functions BEAM implements in C (nif_error stubs in lists.erl and
    /// binary.erl) get native bodies; true if this definition was handled.
    /// Plans: (helper, drop_trailing_args, extra_const_args); helper ""
    /// means the identity function (compile_pattern).
    fn emit_native_override(&self, fname: &FunName) -> CgResult<bool> {
        const NIL_C: u64 = 0b011;
        const SMALL0: u64 = 0b001;
        const SMALL1: u64 = (1 << 3) | 0b001;
        let plan: (&str, usize, &[u64]) =
            match (self.module_name.as_str(), fname.name.as_str(), fname.arity) {
                ("lists", "reverse", 2) => ("mana_rt_lists_reverse", 0, &[]),
                ("lists", "member", 2) => ("mana_rt_lists_member", 0, &[]),
                ("lists", "keyfind", 3) => ("mana_rt_lists_keyfind", 0, &[0]),
                ("lists", "keymember", 3) => ("mana_rt_lists_keyfind", 0, &[1]),
                ("lists", "keysearch", 3) => ("mana_rt_lists_keyfind", 0, &[2]),
                ("binary", "split", 2) => ("mana_rt_binary_split", 0, &[NIL_C]),
                ("binary", "split", 3) => ("mana_rt_binary_split", 0, &[]),
                ("binary", "match", 2) => ("mana_rt_binary_match", 0, &[0]),
                ("binary", "match", 3) => ("mana_rt_binary_match", 1, &[0]),
                ("binary", "matches", 2) => ("mana_rt_binary_match", 0, &[1]),
                ("binary", "matches", 3) => ("mana_rt_binary_match", 1, &[1]),
                ("binary", "part", 3) => ("mana_rt_binary_part", 0, &[]),
                ("binary", "copy", 1) => ("mana_rt_binary_copy", 0, &[SMALL1]),
                ("binary", "copy", 2) => ("mana_rt_binary_copy", 0, &[]),
                ("binary", "at", 2) => ("mana_rt_binary_at", 0, &[0]),
                ("binary", "first", 1) => ("mana_rt_binary_at", 0, &[SMALL0, 0]),
                ("binary", "last", 1) => ("mana_rt_binary_at", 0, &[SMALL0, 1]),
                ("binary", "encode_unsigned", 1) => ("mana_rt_binary_encode_unsigned", 0, &[0]),
                ("binary", "decode_unsigned", 1) => ("mana_rt_binary_decode_unsigned", 0, &[0]),
                ("binary", "longest_common_prefix", 1) => ("mana_rt_binary_lcp", 0, &[0]),
                ("binary", "longest_common_suffix", 1) => ("mana_rt_binary_lcp", 0, &[1]),
                ("binary", "list_to_bin", 1) => ("mana_rt_list_to_binary", 0, &[]),
                ("binary", "referenced_byte_size", 1) => ("mana_rt_byte_size", 0, &[]),
                ("binary", "compile_pattern", 1) => ("", 0, &[]),
                // Elixir.Float decomposes IEEE bits with sub-bit segments
                // (TODO(bitstring)); precision ops go native instead
                // os.erl's time functions are nif_error stubs (real BIFs
                // on BEAM); 2^30... the /0 const is 1_000_000_000 Hz =
                // our native unit (nanoseconds)
                ("os", "system_time", 0) => {
                    ("mana_rt_system_time", 0, &[(1_000_000_000u64 << 3) | 0b001])
                }
                ("os", "system_time", 1) => ("mana_rt_system_time", 0, &[]),
                ("os", "getenv", 1) => ("mana_rt_os_getenv", 0, &[]),
                ("Elixir.System", "cmd", 2) => ("mana_rt_system_cmd", 0, &[NIL_C]),
                ("Elixir.System", "cmd", 3) => ("mana_rt_system_cmd", 0, &[]),
                ("Elixir.Float", "round", 2) => ("mana_rt_float_prec", 0, &[0]),
                ("Elixir.Float", "ceil", 2) => ("mana_rt_float_prec", 0, &[1]),
                ("Elixir.Float", "floor", 2) => ("mana_rt_float_prec", 0, &[2]),
                _ => return Ok(false),
            };
        let f = self.fns.borrow()[fname];
        let entry = self.ctx.append_basic_block(f, "entry");
        self.builder.position_at_end(entry);
        self.cur_ctx
            .set(Some(f.get_nth_param(0).unwrap().into_pointer_value()));
        self.handlers.borrow_mut().clear();
        self.propagate_bb.set(None);
        self.cur_frame.set(None); // frameless: single forwarding call
        if plan.0.is_empty() {
            // identity (compile_pattern: patterns are plain binaries here)
            let v = f.get_nth_param(1).unwrap().into_int_value();
            self.builder.build_return(Some(&v)).map_err(be)?;
            return Ok(true);
        }
        let mut cargs: Vec<BasicMetadataValueEnum> = vec![self.ctx_val().into()];
        for i in 0..fname.arity - plan.1 {
            cargs.push(f.get_nth_param(1 + i as u32).unwrap().into_int_value().into());
        }
        for &c in plan.2 {
            cargs.push(self.i64t.const_int(c, false).into());
        }
        let nparams = cargs.len() - 1;
        let callee = self.rt_fn(plan.0, || {
            let mut ps: Vec<BasicMetadataTypeEnum> =
                vec![BasicMetadataTypeEnum::PointerType(self.ptrt)];
            ps.extend((0..nparams).map(|_| BasicMetadataTypeEnum::IntType(self.i64t)));
            self.i64t.fn_type(&ps, false)
        });
        let call = self.builder.build_call(callee, &cargs, "natbif").map_err(be)?;
        // raising convention: the sentinel propagates through our return
        let v = call_result(call)?;
        self.builder.build_return(Some(&v)).map_err(be)?;
        Ok(true)
    }

    fn compile_fn(&self, fname: &FunName, fun: &Fun) -> CgResult<()> {
        let f = self.fns.borrow()[fname];
        let entry = self.ctx.append_basic_block(f, "entry");
        self.builder.position_at_end(entry);
        self.cur_ctx
            .set(Some(f.get_nth_param(0).unwrap().into_pointer_value()));
        self.handlers.borrow_mut().clear();
        self.propagate_bb.set(None);
        self.setup_frame(&fun.body, &fun.params, &[])?;
        let mut scope = Scope::default();
        for (i, p) in fun.params.iter().enumerate() {
            let v = f.get_nth_param(1 + i as u32).unwrap().into_int_value();
            v.set_name(p);
            self.bind_var(&mut scope, p, v)?;
        }
        self.emit_reduction_check(f)?;
        let r = self.compile_tail(f, &fun.body, &mut scope);
        self.patch_frame();
        r
    }

    /// Preemption point: decrement the reduction budget, yield to the
    /// scheduler on exhaustion. Only in framed functions AFTER params are
    /// rooted — yield points are GC points, and everything live is already
    /// in frame slots here, so preemption costs no extra spills.
    fn emit_reduction_check(&self, f: FunctionValue<'ctx>) -> CgResult<()> {
        if !self.framed() {
            return Ok(());
        }
        let ctx = self.ctx_val();
        let red = self.mem_load(ctx, CTX_REDUCTIONS, MemKind::Ctx)?;
        let dec = self
            .builder
            .build_int_sub(red, self.i64t.const_int(1, false), "red.dec")
            .map_err(be)?;
        self.mem_store(ctx, CTX_REDUCTIONS, dec, MemKind::Ctx)?;
        let out = self
            .builder
            .build_int_compare(
                IntPredicate::SLT,
                dec,
                self.i64t.const_zero(),
                "red.out",
            )
            .map_err(be)?;
        let yield_bb = self.ctx.append_basic_block(f, "yield");
        let cont = self.ctx.append_basic_block(f, "red.cont");
        self.builder
            .build_conditional_branch(out, yield_bb, cont)
            .map_err(be)?;
        self.builder.position_at_end(yield_bb);
        self.builder
            .build_call(self.rt_p_void("mana_rt_yield"), &[ctx.into()], "")
            .map_err(be)?;
        self.builder.build_unconditional_branch(cont).map_err(be)?;
        self.builder.position_at_end(cont);
        Ok(())
    }

    /// Compile bodies of lambda-lifted funs queued during compilation.
    fn drain_lifts(&self) -> CgResult<()> {
        loop {
            // NB: pop in its own statement — a `while let` scrutinee would
            // hold the RefMut across the body, and bodies push new lifts.
            let next = self.pending.borrow_mut().pop();
            let Some(l) = next else { break };
            let f = self.lifted.borrow()[l.f_index];
            if let Err(e) = self.compile_lift(f, &l) {
                // function-granular poisoning, same as named functions
                eprintln!(
                    "manac: warning: {} lifted fun stubbed (unsupported: {})",
                    self.module_name, e
                );
                let msg = format!("{}: anonymous fun: {}", self.module_name, e);
                self.emit_unsupported_stub(f, &msg)?;
            }
        }
        Ok(())
    }

    fn compile_lift(&self, f: FunctionValue<'ctx>, l: &Lift) -> CgResult<()> {
        {
            let entry = self.ctx.append_basic_block(f, "entry");
            self.builder.position_at_end(entry);
            self.cur_ctx
                .set(Some(f.get_nth_param(0).unwrap().into_pointer_value()));
            self.handlers.borrow_mut().clear();
            self.propagate_bb.set(None);

            let closure_slot_name = "closure$".to_string();
            let mut var_names: Vec<String> = l.params.clone();
            var_names.extend(l.captures.iter().cloned());
            if !l.sibs.is_empty() {
                var_names.push(closure_slot_name.clone());
            }
            let sib_names: Vec<FunName> = l.sibs.iter().map(|(n, _)| n.clone()).collect();
            self.setup_frame(&l.body, &var_names, &sib_names)?;

            let mut scope = Scope::default();
            for (i, p) in l.params.iter().enumerate() {
                let v = f.get_nth_param(1 + i as u32).unwrap().into_int_value();
                v.set_name(p);
                self.bind_var(&mut scope, p, v)?;
            }
            let closure = f
                .get_nth_param(1 + l.params.len() as u32)
                .unwrap()
                .into_int_value();
            closure.set_name("closure");
            if !l.captures.is_empty() {
                // loads happen before any GC point (entry, no allocs yet)
                let p = self
                    .builder
                    .build_int_to_ptr(closure, self.ptrt, "env.ptr")
                    .map_err(be)?;
                for (i, cap) in l.captures.iter().enumerate() {
                    let v = self.load_word(p, 2 + i as u64)?;
                    v.set_name(cap);
                    self.bind_var(&mut scope, cap, v)?;
                }
            }
            if !l.sibs.is_empty() && self.framed() {
                // the closure term itself must be rooted for sibling calls;
                // a member that never calls siblings can be frameless, in
                // which case no sibling binding is ever consulted.
                self.bind_var(&mut scope, &closure_slot_name, closure)?;
                let Binding::Slot(cl_slot) = scope.vars[&closure_slot_name] else {
                    unreachable!("framed bind produced a register");
                };
                for (fname, idx) in &l.sibs {
                    let sib = self.lifted.borrow()[*idx];
                    scope.funs.insert(fname.clone(), (sib, cl_slot));
                }
            }
            self.emit_reduction_check(f)?;
            let r = self.compile_tail(f, &l.body, &mut scope);
            self.patch_frame();
            r?;
        }
        Ok(())
    }

    fn emit_main(&self, entry: &FunName) -> CgResult<()> {
        let i32t = self.ctx.i32_type();
        let main = self
            .module
            .add_function("main", i32t.fn_type(&[], false), None);
        let bb = self.ctx.append_basic_block(main, "entry");
        self.builder.position_at_end(bb);
        let init = self
            .builder
            .build_call(self.rt_init(), &[], "ctx")
            .map_err(be)?;
        let ctx = call_result(init)?.into_pointer_value();
        // the runtime builds exit/monitor messages: hand it the well-known
        // atom terms (atoms are compiler statics)
        let names = [
            "normal", "killed", "kill", "EXIT", "DOWN", "process", "noproc", "true", "false",
            "badarg", "error", "badmap", "badkey", "undef", "ok", "module", "nofile",
            "value", "undefined", "badarith",
        ];
        let mut atom_args: Vec<BasicMetadataValueEnum> = Vec::new();
        for n in names {
            atom_args.push(self.atom_term(n)?.into());
        }
        self.builder
            .build_call(self.rt_register_atoms(), &atom_args, "")
            .map_err(be)?;

        let target = self.fns.borrow()[entry];
        let entry_ptr = target.as_global_value().as_pointer_value();
        let call = self
            .builder
            .build_call(self.rt_run(), &[ctx.into(), entry_ptr.into()], "ret")
            .map_err(be)?;
        let ret = call_result(call)?.into_int_value();
        let is_exc = self
            .builder
            .build_int_compare(IntPredicate::EQ, ret, self.sentinel(), "is.exc")
            .map_err(be)?;
        let bad = self.ctx.append_basic_block(main, "uncaught");
        let ok = self.ctx.append_basic_block(main, "ok");
        self.builder
            .build_conditional_branch(is_exc, bad, ok)
            .map_err(be)?;
        self.builder.position_at_end(bad);
        self.builder
            .build_call(self.rt_uncaught(), &[ctx.into()], "")
            .map_err(be)?;
        self.builder.build_unreachable().map_err(be)?;
        self.builder.position_at_end(ok);
        self.builder
            .build_return(Some(&i32t.const_zero()))
            .map_err(be)?;
        Ok(())
    }

    // ---- expression compilation ----

    fn compile_tail(
        &self,
        f: FunctionValue<'ctx>,
        e: &Expr,
        scope: &mut Scope<'ctx>,
    ) -> CgResult<()> {
        match e {
            Expr::Let { vars, arg, body } => {
                self.bind_let(f, vars, arg, scope)?;
                self.compile_tail(f, body, scope)
            }
            Expr::LetRec { defs, body } => {
                let mut inner = self.bind_letrec(f, defs, scope)?;
                self.compile_tail(f, body, &mut inner)
            }
            Expr::Do(first, then) => {
                let wm = self.next_slot.get();
                self.compile_value(f, first, scope)?;
                self.next_slot.set(wm);
                self.compile_tail(f, then, scope)
            }
            Expr::Case { arg, clauses } => {
                let vals = self.compile_case_arg(f, arg, clauses, scope)?;
                self.compile_case(f, &vals, clauses, scope, None)
            }
            Expr::Try {
                arg,
                vars,
                body,
                evars,
                handler,
            } => {
                if vars.len() != 1 {
                    return Err("multi-value try is not supported".into());
                }
                let hbb = self.ctx.append_basic_block(f, "catch");
                self.handlers.borrow_mut().push(hbb);
                let v = self.compile_value(f, arg, scope);
                self.handlers.borrow_mut().pop();
                let v = v?;
                self.bind_var(scope, &vars[0], v)?;
                self.compile_tail(f, body, scope)?;

                self.builder.position_at_end(hbb);
                let ctx = self.ctx_val();
                let class = self.mem_load(ctx, CTX_EXC_CLASS, MemKind::Ctx)?;
                let reason = self.mem_load(ctx, CTX_EXC_REASON, MemKind::Ctx)?;
                let mut hscope = scope.clone();
                self.bind_try_evars(&mut hscope, evars, class, reason)?;
                self.compile_tail(f, handler, &mut hscope)
            }
            Expr::Apply { target, args } => {
                // the sentinel propagates through the returned value —
                // tail calls need no exception check
                let (call, _) = self.compile_apply(f, target, args, scope, true)?;
                call.set_tail_call(true);
                let v = call_result(call)?;
                self.builder.build_return(Some(&v)).map_err(be)?;
                Ok(())
            }
            Expr::Call { module, name, args } if !is_bif_module(module) => {
                if self.missing_modules.borrow().contains(module) {
                    return Err(format!("module '{}' is not compiled", module));
                }
                let callee = self.remote_fn(module, name, args.len());
                let argv = self.eval_args(f, args, scope)?;
                self.pop_frame()?;
                let call = self.builder.build_call(callee, &argv, "tail").map_err(be)?;
                call.set_tail_call(true);
                let v = call_result(call)?;
                self.builder.build_return(Some(&v)).map_err(be)?;
                Ok(())
            }
            Expr::PrimOp { name, args } if is_raise(name) => {
                self.compile_raise(f, name, args, scope)?;
                self.builder.build_unreachable().map_err(be)?;
                Ok(())
            }
            _ => {
                let v = self.compile_value(f, e, scope)?;
                self.emit_ret(v)
            }
        }
    }

    fn compile_value(
        &self,
        f: FunctionValue<'ctx>,
        e: &Expr,
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        match e {
            Expr::Var(v) => self.read_var(scope, v),
            Expr::Lit(l) => self.compile_literal(l),
            Expr::Tuple(items) => {
                let refs: Vec<&Expr> = items.iter().collect();
                let slots = self.eval_all_rooted(f, &refs, scope)?;
                let p = self.alloc_words(1 + slots.len() as u64)?;
                let header = self
                    .i64t
                    .const_int(((slots.len() as u64) << 8) | KIND_TUPLE, false);
                self.store_word(p, 0, header)?;
                for (i, s) in slots.iter().enumerate() {
                    let v = self.rooted_get(s)?;
                    self.store_word(p, 1 + i as u64, v)?;
                }
                self.builder
                    .build_ptr_to_int(p, self.i64t, "tuple")
                    .map_err(be)
            }
            Expr::Cons(h, t) => {
                let slots = self.eval_all_rooted(f, &[h.as_ref(), t.as_ref()], scope)?;
                let p = self.alloc_words_kind(2, true)?;
                for (i, s) in slots.iter().enumerate() {
                    let v = self.rooted_get(s)?;
                    self.store_word(p, i as u64, v)?;
                }
                let as_int = self
                    .builder
                    .build_ptr_to_int(p, self.i64t, "cons.addr")
                    .map_err(be)?;
                self.builder
                    .build_or(as_int, self.i64t.const_int(TAG_CONS, false), "cons")
                    .map_err(be)
            }
            Expr::Fun(fun) => {
                let free: Vec<String> = {
                    let mut bound: HashSet<String> = fun.params.iter().cloned().collect();
                    let mut out = BTreeSet::new();
                    free_vars(&fun.body, &mut bound, &mut out);
                    out.into_iter().collect()
                };
                let lifted = self.declare_lift("fun", fun.params.len());
                self.pending.borrow_mut().push(Lift {
                    f_index: lifted,
                    params: fun.params.clone(),
                    captures: free.clone(),
                    sibs: Vec::new(),
                    body: fun.body.clone(),
                });
                let fv = self.lifted.borrow()[lifted];
                self.make_closure(fv, fun.params.len(), &free, scope)
            }
            Expr::FunRef { module, fun } => {
                if module.is_none() && scope.funs.contains_key(fun) {
                    return Err(format!(
                        "letrec-bound fun {}/{} used as a value (unsupported)",
                        fun.name, fun.arity
                    ));
                }
                let shim = self.fun_shim(module.as_deref(), fun)?;
                self.make_closure(shim, fun.arity, &[], scope)
            }
            Expr::Let { vars, arg, body } => {
                self.bind_let(f, vars, arg, scope)?;
                self.compile_value(f, body, scope)
            }
            Expr::LetRec { defs, body } => {
                let mut inner = self.bind_letrec(f, defs, scope)?;
                self.compile_value(f, body, &mut inner)
            }
            Expr::Do(first, then) => {
                let wm = self.next_slot.get();
                self.compile_value(f, first, scope)?;
                self.next_slot.set(wm);
                self.compile_value(f, then, scope)
            }
            Expr::Try {
                arg,
                vars,
                body,
                evars,
                handler,
            } => {
                if vars.len() != 1 {
                    return Err("multi-value try is not supported".into());
                }
                let hbb = self.ctx.append_basic_block(f, "catch");
                let merge = self.ctx.append_basic_block(f, "try.merge");

                self.handlers.borrow_mut().push(hbb);
                let v = self.compile_value(f, arg, scope);
                self.handlers.borrow_mut().pop();
                let v = v?;
                self.bind_var(scope, &vars[0], v)?;
                let bv = self.compile_value(f, body, scope)?;
                let body_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(merge).map_err(be)?;

                self.builder.position_at_end(hbb);
                let ctx = self.ctx_val();
                let class = self.mem_load(ctx, CTX_EXC_CLASS, MemKind::Ctx)?;
                let reason = self.mem_load(ctx, CTX_EXC_REASON, MemKind::Ctx)?;
                let mut hscope = scope.clone();
                self.bind_try_evars(&mut hscope, evars, class, reason)?;
                let hv = self.compile_value(f, handler, &mut hscope)?;
                let handler_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(merge).map_err(be)?;

                self.builder.position_at_end(merge);
                let phi = self.builder.build_phi(self.i64t, "try.val").map_err(be)?;
                phi.add_incoming(&[(&bv, body_end), (&hv, handler_end)]);
                Ok(phi.as_basic_value().into_int_value())
            }
            Expr::Apply { target, args } => {
                let (call, may_raise) = self.compile_apply(f, target, args, scope, false)?;
                let v = call_result(call)?.into_int_value();
                if may_raise {
                    self.check_exc(f, v)
                } else {
                    Ok(v)
                }
            }
            Expr::Call { module, name, args } => {
                if is_bif_module(module) {
                    self.compile_bif(f, module, name, args, scope)
                } else if self.missing_modules.borrow().contains(module) {
                    Err(format!("module '{}' is not compiled", module))
                } else {
                    let callee = self.remote_fn(module, name, args.len());
                    let may_raise = self.raise_set.contains(&(
                        module.clone(),
                        FunName {
                            name: name.clone(),
                            arity: args.len(),
                        },
                    ));
                    let argv = self.eval_args(f, args, scope)?;
                    let call = self.builder.build_call(callee, &argv, "call").map_err(be)?;
                    let v = call_result(call)?.into_int_value();
                    if may_raise {
                        self.check_exc(f, v)
                    } else {
                        Ok(v)
                    }
                }
            }
            Expr::PrimOp { name, args } if is_raise(name) => {
                self.compile_raise(f, name, args, scope)?;
                Ok(self.i64t.get_undef())
            }
            Expr::PrimOp { name, args } if name == "remove_message" && args.is_empty() => {
                self.builder
                    .build_call(
                        self.rt_p_void("mana_rt_recv_remove"),
                        &[self.ctx_val().into()],
                        "",
                    )
                    .map_err(be)?;
                Ok(self.nil())
            }
            Expr::PrimOp { name, args } if name == "recv_next" && args.is_empty() => {
                self.builder
                    .build_call(
                        self.rt_p_void("mana_rt_recv_next"),
                        &[self.ctx_val().into()],
                        "",
                    )
                    .map_err(be)?;
                Ok(self.nil())
            }
            Expr::PrimOp { name, args } if name == "recv_wait_timeout" && args.len() == 1 => {
                let t = self.compile_value(f, &args[0], scope)?;
                let call = self
                    .builder
                    .build_call(
                        self.rt_recv_wait(),
                        &[self.ctx_val().into(), t.into()],
                        "recv.wait",
                    )
                    .map_err(be)?;
                let timed_out = call_result(call)?.into_int_value();
                let c = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        timed_out,
                        self.i64t.const_int(1, false),
                        "timedout",
                    )
                    .map_err(be)?;
                let tr = self.atom_term("true")?;
                let fa = self.atom_term("false")?;
                Ok(self
                    .builder
                    .build_select(c, tr, fa, "waited")
                    .map_err(be)?
                    .into_int_value())
            }
            Expr::CallDyn { module, name, args } => {
                let mut children: Vec<&Expr> = vec![module.as_ref(), name.as_ref()];
                children.extend(args.iter());
                let rooted = self.eval_all_rooted(f, &children, scope)?;
                let list = self.build_list_from_rooted(&rooted[2..])?;
                let m = self.rooted_get(&rooted[0])?;
                let fa = self.rooted_get(&rooted[1])?;
                let call = self
                    .builder
                    .build_call(
                        self.rt_fn("mana_rt_apply3", || {
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
                        &[self.ctx_val().into(), m.into(), fa.into(), list.into()],
                        "dyncall",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            // stacktraces are not built — TODO(stacktraces); the raw
            // stacktrace argument was evaluated as part of the try lowering
            Expr::PrimOp { name, .. } if name == "build_stacktrace" => Ok(self.nil()),
            // re-raise with dynamic class + raw stacktrace (dropped)
            Expr::PrimOp { name, args } if name == "raw_raise" && args.len() == 3 => {
                let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
                let ctx = self.ctx_val();
                self.mem_store(ctx, CTX_EXC_CLASS, argv[0], MemKind::Ctx)?;
                self.mem_store(ctx, CTX_EXC_REASON, argv[1], MemKind::Ctx)?;
                let target = self.unwind_target(f)?;
                self.builder.build_unconditional_branch(target).map_err(be)?;
                let dead = self.ctx.append_basic_block(f, "rawraise.dead");
                self.builder.position_at_end(dead);
                Ok(self.i64t.get_undef())
            }
            Expr::PrimOp { name, .. } => Err(format!("unsupported primop {}", name)),
            Expr::Case { arg, clauses } => {
                let vals = self.compile_case_arg(f, arg, clauses, scope)?;
                let merge = self.ctx.append_basic_block(f, "case.merge");
                let mut incoming: Vec<(Vec<IntValue<'ctx>>, BasicBlock<'ctx>)> = Vec::new();
                self.compile_case(f, &vals, clauses, scope, Some((merge, &mut incoming, 1)))?;
                self.builder.position_at_end(merge);
                let phi = self.builder.build_phi(self.i64t, "case.val").map_err(be)?;
                for (v, bb) in &incoming {
                    phi.add_incoming(&[(&v[0], *bb)]);
                }
                Ok(phi.as_basic_value().into_int_value())
            }
            Expr::Values(_) => Err("multi-value expression outside let/case".into()),
            Expr::Binary(segs) => self.compile_binary_construct(f, segs, scope),
            Expr::Map { pairs, update } => {
                match update {
                    None => {
                        // all-literal immediate keys (the struct/record case):
                        // term order is known at compile time — emit the map
                        // already sorted/deduped and skip mana_rt_map_norm.
                        // Values still evaluate in source order (effects).
                        let lit_keys: Option<Vec<&Literal>> = pairs
                            .iter()
                            .map(|(k, _, _)| match k {
                                Expr::Lit(
                                    l @ (Literal::Int(_) | Literal::Atom(_) | Literal::Nil),
                                ) => Some(l),
                                _ => None,
                            })
                            .collect();
                        if let Some(keys) = lit_keys {
                            let mut sorted: Vec<&Literal> = keys.clone();
                            sorted.sort_by(|a, b| lit_key_ord(a, b));
                            sorted.dedup();
                            let m2 = sorted.len();
                            let children: Vec<&Expr> =
                                pairs.iter().map(|(_, _, v)| v).collect();
                            let slots = self.eval_all_rooted(f, &children, scope)?;
                            let p = self.alloc_words(1 + 2 * m2 as u64)?;
                            let header =
                                self.i64t.const_int(((m2 as u64) << 8) | KIND_MAP, false);
                            self.store_word(p, 0, header)?;
                            for (i, l) in sorted.iter().enumerate() {
                                let k = self.compile_literal(l)?;
                                self.store_word(p, 1 + i as u64, k)?;
                            }
                            // original order: a duplicate key's later value
                            // overwrites the earlier store (last write wins)
                            for (i, l) in keys.iter().enumerate() {
                                let at = sorted
                                    .binary_search_by(|s| lit_key_ord(s, l))
                                    .expect("literal key in sorted set");
                                let v = self.rooted_get(&slots[i])?;
                                self.store_word(p, 1 + (m2 + at) as u64, v)?;
                            }
                            let raw = self
                                .builder
                                .build_ptr_to_int(p, self.i64t, "map.raw")
                                .map_err(be)?;
                            return Ok(raw);
                        }
                        // build unsorted, then normalize (pre-publication
                        // mutation: the term hasn't escaped yet)
                        let n = pairs.len();
                        let mut children: Vec<&Expr> = Vec::with_capacity(2 * n);
                        for (k, _, v) in pairs {
                            children.push(k);
                            children.push(v);
                        }
                        let slots = self.eval_all_rooted(f, &children, scope)?;
                        let p = self.alloc_words(1 + 2 * n as u64)?;
                        let header =
                            self.i64t.const_int(((n as u64) << 8) | KIND_MAP, false);
                        self.store_word(p, 0, header)?;
                        for i in 0..n {
                            let k = self.rooted_get(&slots[2 * i])?;
                            self.store_word(p, 1 + i as u64, k)?;
                            let v = self.rooted_get(&slots[2 * i + 1])?;
                            self.store_word(p, 1 + (n + i) as u64, v)?;
                        }
                        let raw = self
                            .builder
                            .build_ptr_to_int(p, self.i64t, "map.raw")
                            .map_err(be)?;
                        let call = self
                            .builder
                            .build_call(
                                self.rt_fn("mana_rt_map_norm", || {
                                    self.i64t.fn_type(
                                        &[BasicMetadataTypeEnum::IntType(self.i64t)],
                                        false,
                                    )
                                }),
                                &[raw.into()],
                                "map",
                            )
                            .map_err(be)?;
                        Ok(call_result(call)?.into_int_value())
                    }
                    Some(base) => {
                        // `=>` = insert-or-replace (erlc rewrites maps:put/3
                        // into these), `:=` = exact (badkey on miss)
                        let mut acc = self.compile_value(f, base, scope)?;
                        for (k, assoc, v) in pairs {
                            let wm = self.next_slot.get();
                            let acc_slot =
                                if self.framed() { Some(self.spill(acc)?) } else { None };
                            let kv = self.eval_siblings(f, &[k, v], scope)?;
                            let acc2 = match acc_slot {
                                Some(s) => self.reload(s)?,
                                None => acc,
                            };
                            let helper = match assoc {
                                MapAssoc::Assoc => "mana_rt_map_put",
                                MapAssoc::Exact => "mana_rt_map_update_exact",
                            };
                            let callee = self.rt_fn(helper, || {
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
                                        kv[0].into(),
                                        kv[1].into(),
                                        acc2.into(),
                                    ],
                                    "mup",
                                )
                                .map_err(be)?;
                            let r = call_result(call)?.into_int_value();
                            acc = self.check_exc(f, r)?;
                            self.next_slot.set(wm);
                        }
                        Ok(acc)
                    }
                }
            }
        }
    }

    /// Evaluate sibling expressions left→right; a value is spilled only if
    /// a *later* sibling's evaluation contains a GC point. Returns fresh
    /// values valid at the point of return.
    fn eval_siblings(
        &self,
        f: FunctionValue<'ctx>,
        exprs: &[&Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<Vec<IntValue<'ctx>>> {
        // gc_after[i]: any expr j > i contains a GC point
        let mut gc_after = vec![false; exprs.len()];
        let mut acc = false;
        for i in (0..exprs.len()).rev() {
            gc_after[i] = acc;
            acc = acc || self.expr_gc(&exprs[i]);
        }
        enum Held<'ctx> {
            Val(IntValue<'ctx>),
            Slot(u64),
        }
        // spill slots die once reloaded below — release them for reuse
        let wm = self.next_slot.get();
        let mut held = Vec::with_capacity(exprs.len());
        for (i, e) in exprs.iter().enumerate() {
            if gc_after[i] && self.framed() {
                if let Expr::Var(name) = e {
                    if let Some(Binding::Slot(idx)) = scope.vars.get(name.as_str()) {
                        held.push(Held::Slot(*idx));
                        continue;
                    }
                }
                if matches!(
                    e,
                    Expr::Lit(Literal::Int(_) | Literal::Atom(_) | Literal::Nil)
                ) {
                    held.push(Held::Val(self.compile_value(f, e, scope)?));
                    continue;
                }
                let v = self.compile_value(f, e, scope)?;
                held.push(Held::Slot(self.spill(v)?));
            } else {
                let v = self.compile_value(f, e, scope)?;
                held.push(Held::Val(v));
            }
        }        let out = held
            .into_iter()
            .map(|h| match h {
                Held::Val(v) => Ok(v),
                Held::Slot(s) => self.reload(s),
            })
            .collect();
        self.next_slot.set(wm);
        out
    }

    /// Evaluate and root every expression (used when the consumer itself is
    /// an allocation). In frameless functions this can only be reached in
    /// eternal-alloc (raise) mode, where allocation never collects — values
    /// stay in SSA.
    fn eval_all_rooted(
        &self,
        f: FunctionValue<'ctx>,
        exprs: &[&Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<Vec<Rooted<'ctx>>> {
        exprs
            .iter()
            .map(|e| {
                // a variable already in a frame slot IS a root — reuse it;
                // immediates (ints/atoms/nil) never move — keep in SSA
                if let Expr::Var(name) = e {
                    if let Some(Binding::Slot(idx)) = scope.vars.get(name.as_str()) {
                        return Ok(Rooted::Slot(*idx));
                    }
                }
                if matches!(
                    e,
                    Expr::Lit(Literal::Int(_) | Literal::Atom(_) | Literal::Nil)
                ) {
                    return Ok(Rooted::Val(self.compile_value(f, e, scope)?));
                }
                let v = self.compile_value(f, e, scope)?;
                if self.framed() {
                    Ok(Rooted::Slot(self.spill(v)?))
                } else {
                    // frameless: the effect analysis proved no GC point
                    // exists anywhere in this function (raise-path allocs
                    // use the eternal allocator), so SSA is safe
                    Ok(Rooted::Val(v))
                }
            })
            .collect()
    }

    fn rooted_get(&self, r: &Rooted<'ctx>) -> CgResult<IntValue<'ctx>> {
        match r {
            Rooted::Slot(idx) => self.reload(*idx),
            Rooted::Val(v) => Ok(*v),
        }
    }

    /// Arguments for a call: ctx first, then sibling-rule values.
    fn eval_args(
        &self,
        f: FunctionValue<'ctx>,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<Vec<BasicMetadataValueEnum<'ctx>>> {
        let vals = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        let mut argv: Vec<BasicMetadataValueEnum> = vec![self.ctx_val().into()];
        argv.extend(vals.iter().map(|v| BasicMetadataValueEnum::from(*v)));
        Ok(argv)
    }

    /// Compile any `apply`; `tail` pops the frame just before the call.
    /// Returns the call site and whether the callee may raise (tail calls
    /// propagate the sentinel for free via the return value; non-tail
    /// callers must `check_exc`).
    fn compile_apply(
        &self,
        f: FunctionValue<'ctx>,
        target: &ApplyTarget,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
        tail: bool,
    ) -> CgResult<(CallSiteValue<'ctx>, bool)> {
        match target {
            ApplyTarget::LocalFun(fname) => {
                if let Some((lf, cl_slot)) = scope.funs.get(fname).copied() {
                    let mut argv = self.eval_args(f, args, scope)?;
                    let closure = self.reload(cl_slot)?;
                    argv.push(closure.into());
                    if tail {
                        self.pop_frame()?;
                    }
                    let call = self.builder.build_call(lf, &argv, "call").map_err(be)?;
                    Ok((call, true)) // letrec bodies: conservatively may raise
                } else {
                    let callee = self.local_fn(fname)?;
                    let may_raise = self
                        .raise_set
                        .contains(&(self.module_name.clone(), fname.clone()));
                    let argv = self.eval_args(f, args, scope)?;
                    if tail {
                        self.pop_frame()?;
                    }
                    let call = self.builder.build_call(callee, &argv, "call").map_err(be)?;
                    Ok((call, may_raise))
                }
            }
            ApplyTarget::Var(v) => {
                let argv = self.eval_args(f, args, scope)?;
                let fun_val = self.read_var(scope, v)?;
                let call = self.compile_apply_value(f, fun_val, &argv, args.len(), tail)?;
                Ok((call, true))
            }
        }
    }

    /// Apply a fun value: check tag/kind/arity, indirect-call
    /// `(ctx, args..., closure)`.
    fn compile_apply_value(
        &self,
        f: FunctionValue<'ctx>,
        fun_val: IntValue<'ctx>,
        argv: &[BasicMetadataValueEnum<'ctx>],
        nargs: usize,
        tail: bool,
    ) -> CgResult<CallSiteValue<'ctx>> {
        let bad = self.ctx.append_basic_block(f, "badfun");
        let check_hdr = self.ctx.append_basic_block(f, "fun.hdr");
        let good = self.ctx.append_basic_block(f, "fun.call");

        let tag = self.tag_of(fun_val)?;
        let is_boxed = self
            .builder
            .build_int_compare(IntPredicate::EQ, tag, self.i64t.const_zero(), "is.boxed")
            .map_err(be)?;
        self.builder
            .build_conditional_branch(is_boxed, check_hdr, bad)
            .map_err(be)?;

        self.builder.position_at_end(check_hdr);
        let p = self
            .builder
            .build_int_to_ptr(fun_val, self.ptrt, "fun.ptr")
            .map_err(be)?;
        let header = self.load_word(p, 0)?;
        let masked = self
            .builder
            .build_and(header, self.i64t.const_int(0xffff, false), "hdr.ka")
            .map_err(be)?;
        let want = self.i64t.const_int(((nargs as u64) << 8) | KIND_FUN, false);
        let hdr_ok = self
            .builder
            .build_int_compare(IntPredicate::EQ, masked, want, "hdr.ok")
            .map_err(be)?;
        self.builder
            .build_conditional_branch(hdr_ok, good, bad)
            .map_err(be)?;

        self.builder.position_at_end(bad);
        {
            let reason = self.eternal_pair("badfun", fun_val)?;
            let class = self.atom_term("error")?;
            let ctx = self.ctx_val();
            self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
            self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
            let target = self.unwind_target(f)?;
            self.builder.build_unconditional_branch(target).map_err(be)?;
        }

        self.builder.position_at_end(good);
        let code = self.load_word(p, 1)?;
        let code_ptr = self
            .builder
            .build_int_to_ptr(code, self.ptrt, "code.ptr")
            .map_err(be)?;
        let mut full_args = argv.to_vec();
        full_args.push(fun_val.into());
        if tail {
            self.pop_frame()?;
        }
        self.builder
            .build_indirect_call(self.term_fn_type(nargs + 1), code_ptr, &full_args, "apply")
            .map_err(be)
    }

    /// `[header | code | captures...]`, boxed (tag 000). Allocates first,
    /// then reads captures from their variable bindings — safe because the
    /// allocation is the only GC point involved.
    fn make_closure(
        &self,
        code: FunctionValue<'ctx>,
        arity: usize,
        capture_names: &[String],
        scope: &Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let header = self.i64t.const_int(
            ((capture_names.len() as u64) << 16) | ((arity as u64) << 8) | KIND_FUN,
            false,
        );
        // captureless: a per-code-pointer static constant — no allocation
        // (safe: forward_major/minor pass non-heap boxed terms through)
        if capture_names.is_empty() {
            let sym = format!("mana_fun.{}", code.get_name().to_string_lossy());
            let g = match self.module.get_global(&sym) {
                Some(g) => g,
                None => {
                    let init = self.ctx.const_struct(
                        &[
                            header.into(),
                            code.as_global_value().as_pointer_value().into(),
                        ],
                        false,
                    );
                    let g = self.module.add_global(init.get_type(), None, &sym);
                    g.set_initializer(&init);
                    g.set_constant(true);
                    g.set_alignment(8);
                    g.set_linkage(Linkage::LinkOnceODR);
                    g
                }
            };
            return self
                .builder
                .build_ptr_to_int(g.as_pointer_value(), self.i64t, "fun.static")
                .map_err(be);
        }
        let p = self.alloc_words(2 + capture_names.len() as u64)?;
        self.store_word(p, 0, header)?;
        let code_int = self
            .builder
            .build_ptr_to_int(
                code.as_global_value().as_pointer_value(),
                self.i64t,
                "code.addr",
            )
            .map_err(be)?;
        self.store_word(p, 1, code_int)?;
        for (i, name) in capture_names.iter().enumerate() {
            let v = self.read_var(scope, name).map_err(|e| {
                format!("{} (captured by fun)", e)
            })?;
            self.store_word(p, 2 + i as u64, v)?;
        }
        self.builder
            .build_ptr_to_int(p, self.i64t, "fun")
            .map_err(be)
    }

    fn declare_lift(&self, hint: &str, arity: usize) -> usize {
        let n = self.lift_counter.get();
        self.lift_counter.set(n + 1);
        let name = format!(
            "mn_{}.l{}.{}",
            sanitize(&self.module_name),
            n,
            sanitize(hint)
        );
        let f = self
            .module
            .add_function(&name, self.term_fn_type(arity + 1), None);
        f.set_linkage(Linkage::Internal);
        let mut lifted = self.lifted.borrow_mut();
        lifted.push(f);
        lifted.len() - 1
    }

    /// Lift a letrec group: one shared capture environment, direct calls
    /// among members. Returns the scope extended with the group's funs.
    fn bind_letrec(
        &self,
        _f: FunctionValue<'ctx>,
        defs: &[(FunName, Fun)],
        scope: &Scope<'ctx>,
    ) -> CgResult<Scope<'ctx>> {
        let mut free: BTreeSet<String> = BTreeSet::new();
        for (_, fun) in defs {
            let mut bound: HashSet<String> = fun.params.iter().cloned().collect();
            free_vars(&fun.body, &mut bound, &mut free);
        }
        let free: Vec<String> = free.into_iter().collect();

        let indices: Vec<usize> = defs
            .iter()
            .map(|(fname, fun)| {
                self.declare_lift(
                    &format!("{}_{}", fname.name, fname.arity),
                    fun.params.len(),
                )
            })
            .collect();
        let sibs: Vec<(FunName, usize)> = defs
            .iter()
            .map(|(fname, _)| fname.clone())
            .zip(indices.iter().copied())
            .collect();

        // One closure object shared by the whole group for direct calls;
        // its code pointer (first member) is never used via apply.
        let first = self.lifted.borrow()[indices[0]];
        let closure = self.make_closure(first, defs[0].1.params.len(), &free, scope)?;
        let cl_slot = self.spill(closure)?;

        for ((_, fun), idx) in defs.iter().zip(indices.iter()) {
            self.pending.borrow_mut().push(Lift {
                f_index: *idx,
                params: fun.params.clone(),
                captures: free.clone(),
                sibs: sibs.clone(),
                body: fun.body.clone(),
            });
        }

        let mut inner = scope.clone();
        for (fname, idx) in &sibs {
            let lf = self.lifted.borrow()[*idx];
            inner.funs.insert(fname.clone(), (lf, cl_slot));
        }
        Ok(inner)
    }

    /// A shim adapting a plain top-level function to the closure calling
    /// convention. Frameless: it holds no live terms across the call.
    fn fun_shim(&self, module: Option<&str>, fname: &FunName) -> CgResult<FunctionValue<'ctx>> {
        let target_mod = module.unwrap_or(&self.module_name);
        let sym = format!("{}.shim", mangle(target_mod, fname));
        if let Some(existing) = self.module.get_function(&sym) {
            return Ok(existing);
        }
        // check fallibility BEFORE declaring: a linkonce_odr declaration
        // without a body is invalid IR (this leaked when the target module
        // was missing)
        if module.is_some()
            && !is_bif_module(target_mod)
            && self.missing_modules.borrow().contains(target_mod)
        {
            return Err(format!("module '{}' is not compiled", target_mod));
        }
        let shim = self
            .module
            .add_function(&sym, self.term_fn_type(fname.arity + 1), None);
        shim.set_linkage(Linkage::LinkOnceODR);

        // BIF-module targets have no symbol to forward to: give the shim a
        // real (mini-compiled) body that invokes the BIF
        if module.is_some() && is_bif_module(target_mod) {
            let params: Vec<String> = (0..fname.arity).map(|i| format!("_bifshim{}", i)).collect();
            let body = Expr::Call {
                module: target_mod.to_string(),
                name: fname.name.clone(),
                args: params.iter().map(|p| Expr::Var(p.clone())).collect(),
            };
            let saved_bb = self.builder.get_insert_block();
            let saved_ctx = self.cur_ctx.get();
            let saved_handlers = std::mem::take(&mut *self.handlers.borrow_mut());
            let saved_prop = self.propagate_bb.get();
            let saved_frame = self.cur_frame.get();
            let saved_slots = self.var_slots.borrow().clone();
            let saved_next = self.next_slot.get();
            let saved_cap = self.slot_cap.get();
            let saved_peak = self.peak_slot.get();
            let saved_memset = self.frame_memset.get();
            let saved_len_store = self.frame_len_store.get();
            let saved_skip = self.frame_skip.get();

            let entry = self.ctx.append_basic_block(shim, "entry");
            self.builder.position_at_end(entry);
            self.cur_ctx
                .set(Some(shim.get_nth_param(0).unwrap().into_pointer_value()));
            self.propagate_bb.set(None);
            self.setup_frame(&body, &params, &[])?;
            let mut scope = Scope::default();
            for (i, p) in params.iter().enumerate() {
                let v = shim.get_nth_param(1 + i as u32).unwrap().into_int_value();
                self.bind_var(&mut scope, p, v)?;
            }
            let r = self.compile_tail(shim, &body, &mut scope);
            self.patch_frame();

            *self.handlers.borrow_mut() = saved_handlers;
            self.propagate_bb.set(saved_prop);
            self.cur_ctx.set(saved_ctx);
            self.cur_frame.set(saved_frame);
            *self.var_slots.borrow_mut() = saved_slots;
            self.next_slot.set(saved_next);
            self.slot_cap.set(saved_cap);
            self.peak_slot.set(saved_peak);
            self.frame_memset.set(saved_memset);
            self.frame_len_store.set(saved_len_store);
            self.frame_skip.set(saved_skip);
            if let Err(e) = r {
                // an unsupported BIF captured as a fun: the shim raises at
                // runtime if the fun is ever called
                let msg = format!("fun {}:{}/{}: {}", target_mod, fname.name, fname.arity, e);
                eprintln!("manac: warning: {} stubbed", msg);
                self.emit_unsupported_stub(shim, &msg)?;
            }
            if let Some(bb) = saved_bb {
                self.builder.position_at_end(bb);
            }
            return Ok(shim);
        }

        let target = if module.is_none() || module == Some(self.module_name.as_str()) {
            self.local_fn(fname)?
        } else {
            self.remote_fn(target_mod, &fname.name, fname.arity)
        };

        let saved = self.builder.get_insert_block();
        let bb = self.ctx.append_basic_block(shim, "entry");
        self.builder.position_at_end(bb);
        let argv: Vec<BasicMetadataValueEnum> = (0..=fname.arity)
            .map(|i| shim.get_nth_param(i as u32).unwrap().into())
            .collect(); // ctx + args, dropping the trailing closure param
        let call = self.builder.build_call(target, &argv, "fwd").map_err(be)?;
        call.set_tail_call(true);
        let v = call_result(call)?;
        self.builder.build_return(Some(&v)).map_err(be)?;
        if let Some(bb) = saved {
            self.builder.position_at_end(bb);
        }
        Ok(shim)
    }

    /// Bind try-catch variables: `<Class, Reason, Stk>` (3), `<Class,
    /// Reason>` (2) or `<Reason>` (1). The stacktrace slot carries the class
    /// atom so `primop raise(Stk, Reason)` re-raises with the right class
    /// (TODO(stacktraces)).
    fn bind_try_evars(
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

    /// (term, term) -> i64 runtime helper.
    fn rt_tt_i64(&self, name: &str) -> FunctionValue<'ctx> {
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

    fn bool_term(&self, cond: IntValue<'ctx>) -> CgResult<IntValue<'ctx>> {
        let t = self.atom_term("true")?;
        let fa = self.atom_term("false")?;
        Ok(self
            .builder
            .build_select(cond, t, fa, "bool")
            .map_err(be)?
            .into_int_value())
    }

    /// i1: is `a` (and `b`, when given) a small int?
    fn small_test(
        &self,
        a: IntValue<'ctx>,
        b: Option<IntValue<'ctx>>,
    ) -> CgResult<IntValue<'ctx>> {
        let tag_of = |v: IntValue<'ctx>, n: &str| -> CgResult<IntValue<'ctx>> {
            let t = self
                .builder
                .build_and(v, self.i64t.const_int(TAG_MASK, false), n)
                .map_err(be)?;
            self.builder
                .build_int_compare(
                    IntPredicate::EQ,
                    t,
                    self.i64t.const_int(TAG_SMALL, false),
                    n,
                )
                .map_err(be)
        };
        match b {
            None => tag_of(a, "sm.a"),
            Some(b) => {
                // ((a^1) | (b^1)) & 7 == 0  ⇔  both tags are 001
                let xa = self
                    .builder
                    .build_xor(a, self.i64t.const_int(TAG_SMALL, false), "sm.xa")
                    .map_err(be)?;
                let xb = self
                    .builder
                    .build_xor(b, self.i64t.const_int(TAG_SMALL, false), "sm.xb")
                    .map_err(be)?;
                let or = self.builder.build_or(xa, xb, "sm.or").map_err(be)?;
                let m = self
                    .builder
                    .build_and(or, self.i64t.const_int(TAG_MASK, false), "sm.m")
                    .map_err(be)?;
                self.builder
                    .build_int_compare(IntPredicate::EQ, m, self.i64t.const_zero(), "sm.ok")
                    .map_err(be)
            }
        }
    }

    /// (ctx, op, a, b) -> term arithmetic slow path.
    fn rt_arith(&self) -> FunctionValue<'ctx> {
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

    /// Numeric op with a both-small inline path and the mana_rt_arith slow
    /// path (floats / badarith). The slow path may raise but never GCs.
    fn arith_fastslow(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        opcode: u64,
        a: IntValue<'ctx>,
        b: Option<IntValue<'ctx>>,
    ) -> CgResult<IntValue<'ctx>> {
        let both = self.small_test(a, b)?;
        let fast = self.ctx.append_basic_block(f, "ar.fast");
        let slow = self.ctx.append_basic_block(f, "ar.slow");
        let merge = self.ctx.append_basic_block(f, "ar.merge");
        self.builder
            .build_conditional_branch(both, fast, slow)
            .map_err(be)?;

        self.builder.position_at_end(fast);
        let ua = self.untag_int(a)?;
        let fv = match (name, b) {
            ("+", Some(b)) => {
                let ub = self.untag_int(b)?;
                self.builder.build_int_add(ua, ub, "add").map_err(be)?
            }
            ("-", Some(b)) => {
                let ub = self.untag_int(b)?;
                self.builder.build_int_sub(ua, ub, "sub").map_err(be)?
            }
            ("*", Some(b)) => {
                let ub = self.untag_int(b)?;
                self.builder.build_int_mul(ua, ub, "mul").map_err(be)?
            }
            ("div", Some(b)) => {
                let ub = self.untag_int(b)?;
                self.builder
                    .build_int_signed_div(ua, ub, "div")
                    .map_err(be)?
            }
            ("rem", Some(b)) => {
                let ub = self.untag_int(b)?;
                self.builder
                    .build_int_signed_rem(ua, ub, "rem")
                    .map_err(be)?
            }
            ("band", Some(b)) => {
                let ub = self.untag_int(b)?;
                self.builder.build_and(ua, ub, "band").map_err(be)?
            }
            ("bor", Some(b)) => {
                let ub = self.untag_int(b)?;
                self.builder.build_or(ua, ub, "bor").map_err(be)?
            }
            ("bxor", Some(b)) => {
                let ub = self.untag_int(b)?;
                self.builder.build_xor(ua, ub, "bxor").map_err(be)?
            }
            ("bnot", None) => self
                .builder
                .build_xor(ua, self.i64t.const_all_ones(), "bnot")
                .map_err(be)?,
            ("neg", None) => self
                .builder
                .build_int_sub(self.i64t.const_zero(), ua, "neg")
                .map_err(be)?,
            ("abs", None) => {
                let neg = self
                    .builder
                    .build_int_compare(
                        IntPredicate::SLT,
                        ua,
                        self.i64t.const_zero(),
                        "abs.n",
                    )
                    .map_err(be)?;
                let nv = self
                    .builder
                    .build_int_sub(self.i64t.const_zero(), ua, "abs.neg")
                    .map_err(be)?;
                self.builder
                    .build_select(neg, nv, ua, "abs")
                    .map_err(be)?
                    .into_int_value()
            }
            _ => return Err(format!("arith_fastslow: bad op {}", name)),
        };
        let fastv = self.retag_int(fv)?;
        let fast_end = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(merge).map_err(be)?;

        self.builder.position_at_end(slow);
        let bb = b.unwrap_or(self.i64t.const_int(1, false)); // small 0 dummy
        let call = self
            .builder
            .build_call(
                self.rt_arith(),
                &[
                    self.ctx_val().into(),
                    self.i64t.const_int(opcode, false).into(),
                    a.into(),
                    bb.into(),
                ],
                "ar",
            )
            .map_err(be)?;
        let sv = call_result(call)?.into_int_value();
        let sv = self.check_exc(f, sv)?;
        let slow_end = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(merge).map_err(be)?;

        self.builder.position_at_end(merge);
        let phi = self.builder.build_phi(self.i64t, "ar.v").map_err(be)?;
        phi.add_incoming(&[(&fastv, fast_end), (&sv, slow_end)]);
        Ok(phi.as_basic_value().into_int_value())
    }

    /// Branch to a fresh block that raises `error:badarg` unless `ok`.
    fn guard_badarg(
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
        // poor man's stacktrace: MANA_DEBUG_BADARG names the raising
        // function (cold path — the call costs nothing unless raising)
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

    /// `boxed(v) && header.kind == kind` as an i1, via control flow.
    fn kind_test(
        &self,
        f: FunctionValue<'ctx>,
        v: IntValue<'ctx>,
        test: impl FnOnce(&Self, IntValue<'ctx>) -> CgResult<IntValue<'ctx>>,
    ) -> CgResult<IntValue<'ctx>> {
        let entry = self.builder.get_insert_block().unwrap();
        let boxed_bb = self.ctx.append_basic_block(f, "kt.boxed");
        let merge = self.ctx.append_basic_block(f, "kt.merge");
        let tag = self.tag_of(v)?;
        let is_boxed = self
            .builder
            .build_int_compare(IntPredicate::EQ, tag, self.i64t.const_zero(), "kt.tag")
            .map_err(be)?;
        let nonzero = self
            .builder
            .build_int_compare(IntPredicate::NE, v, self.i64t.const_zero(), "kt.nz")
            .map_err(be)?;
        let okptr = self.builder.build_and(is_boxed, nonzero, "kt.ptr").map_err(be)?;
        self.builder
            .build_conditional_branch(okptr, boxed_bb, merge)
            .map_err(be)?;
        self.builder.position_at_end(boxed_bb);
        let p = self
            .builder
            .build_int_to_ptr(v, self.ptrt, "kt.p")
            .map_err(be)?;
        let header = self.load_word(p, 0)?;
        let inner = test(self, header)?;
        let boxed_end = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(merge).map_err(be)?;
        self.builder.position_at_end(merge);
        let phi = self
            .builder
            .build_phi(self.ctx.bool_type(), "kt.res")
            .map_err(be)?;
        let ff = self.ctx.bool_type().const_zero();
        phi.add_incoming(&[(&ff, entry), (&inner, boxed_end)]);
        Ok(phi.as_basic_value().into_int_value())
    }

    fn compile_literal(&self, l: &Literal) -> CgResult<IntValue<'ctx>> {
        match l {
            Literal::Int(n) => Ok(self.small_int(*n)),
            Literal::Big(d) => {
                // an inert interned big-literal term: orders/compares/
                // prints correctly; arithmetic on it is badarith at runtime
                // (TODO(bignum)). Decimal's pow10 tables and >=-guards work.
                let ptr = self.static_bytes(d.as_bytes())?;
                let callee = self.rt_fn("mana_rt_big_literal", || {
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
                    .build_call(
                        callee,
                        &[
                            ptr.into(),
                            self.i64t.const_int(d.len() as u64, false).into(),
                        ],
                        "biglit",
                    )
                    .map_err(be)?;
                Ok(call_result(call)?.into_int_value())
            }
            Literal::Atom(a) => self.atom_term(a),
            Literal::Nil => Ok(self.nil()),
            Literal::Float(x) => {
                let p = self.alloc_words(2)?;
                let header = self.i64t.const_int((1 << 8) | KIND_FLOAT, false);
                self.store_word(p, 0, header)?;
                let bits = self.i64t.const_int(x.to_bits(), false);
                self.store_word(p, 1, bits)?;
                self.builder
                    .build_ptr_to_int(p, self.i64t, "float")
                    .map_err(be)
            }
        }
    }

    fn bind_let(
        &self,
        f: FunctionValue<'ctx>,
        vars: &[String],
        arg: &Expr,
        scope: &mut Scope<'ctx>,
    ) -> CgResult<()> {
        // statement boundary: temps rooted while evaluating `arg` are dead
        // once the values sit in the let-bound var slots
        let wm = self.next_slot.get();
        let r = self.bind_let_inner(f, vars, arg, scope);
        self.next_slot.set(wm);
        r
    }

    fn bind_let_inner(
        &self,
        f: FunctionValue<'ctx>,
        vars: &[String],
        arg: &Expr,
        scope: &mut Scope<'ctx>,
    ) -> CgResult<()> {
        match (vars.len(), arg) {
            (1, _) => {
                let v = self.compile_value(f, arg, scope)?;
                self.bind_var(scope, &vars[0], v)
            }
            (2, Expr::PrimOp { name, args })
                if name == "recv_peek_message" && args.is_empty() =>
            {
                let call = self
                    .builder
                    .build_call(
                        self.rt_p_i64("mana_rt_recv_ready"),
                        &[self.ctx_val().into()],
                        "recv.ready",
                    )
                    .map_err(be)?;
                let ready = call_result(call)?.into_int_value();
                let c = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        ready,
                        self.i64t.const_int(1, false),
                        "has.msg",
                    )
                    .map_err(be)?;
                let tr = self.atom_term("true")?;
                let fa = self.atom_term("false")?;
                let flag = self
                    .builder
                    .build_select(c, tr, fa, "ready")
                    .map_err(be)?
                    .into_int_value();
                self.bind_var(scope, &vars[0], flag)?;
                let call = self
                    .builder
                    .build_call(
                        self.rt_p_i64("mana_rt_recv_peek"),
                        &[self.ctx_val().into()],
                        "recv.msg",
                    )
                    .map_err(be)?;
                let msg = call_result(call)?.into_int_value();
                self.bind_var(scope, &vars[1], msg)?;
                Ok(())
            }
            (_, Expr::Values(es)) if es.len() == vars.len() => {
                for (var, e) in vars.iter().zip(es) {
                    let v = self.compile_value(f, e, scope)?;
                    self.bind_var(scope, var, v)?;
                }
                Ok(())
            }
            (_, Expr::Case { arg: carg, clauses }) => {
                let vs = self.compile_case_values(f, carg, clauses, scope, vars.len())?;
                for (var, v) in vars.iter().zip(vs) {
                    self.bind_var(scope, var, v)?;
                }
                Ok(())
            }
            (_, Expr::Let { vars: iv, arg: ia, body }) => {
                self.bind_let(f, iv, ia, scope)?;
                self.bind_let(f, vars, body, scope)
            }
            (_, Expr::Do(a, b)) => {
                let wm = self.next_slot.get();
                self.compile_value(f, a, scope)?;
                self.next_slot.set(wm);
                self.bind_let(f, vars, b, scope)
            }
            _ => Err("multi-value let from a non-values expression is not supported".into()),
        }
    }

    /// Case scrutinees. If any guard contains a GC point, values must be
    /// re-loadable per clause (later clauses re-match after the guard ran),
    /// so everything goes to slots; otherwise plain sibling evaluation.
    fn compile_case_arg(
        &self,
        f: FunctionValue<'ctx>,
        arg: &Expr,
        clauses: &[Clause],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<CaseVals<'ctx>> {
        let exprs: Vec<&Expr> = match arg {
            Expr::Values(es) => es.iter().collect(),
            other => vec![other],
        };
        let any_guard_gc = clauses.iter().any(|c| self.expr_gc(&c.guard));
        let any_pat_gc = clauses
            .iter()
            .any(|c| c.patterns.iter().any(pattern_may_gc));
        if (any_guard_gc || any_pat_gc) && self.framed() {
            let slots = exprs
                .iter()
                .map(|e| {
                    let v = self.compile_value(f, e, scope)?;
                    self.spill(v)
                })
                .collect::<CgResult<Vec<_>>>()?;
            Ok(CaseVals::Slots(slots))
        } else {
            Ok(CaseVals::Ssa(self.eval_siblings(f, &exprs, scope)?))
        }
    }

    fn compile_case(
        &self,
        f: FunctionValue<'ctx>,
        vals: &CaseVals<'ctx>,
        clauses: &[Clause],
        scope: &Scope<'ctx>,
        mut merge: Option<(
            BasicBlock<'ctx>,
            &mut Vec<(Vec<IntValue<'ctx>>, BasicBlock<'ctx>)>,
            usize,
        )>,
    ) -> CgResult<()> {
        let fail_bb = self.ctx.append_basic_block(f, "case.nomatch");
        let mut next = self.ctx.append_basic_block(f, "clause0");
        self.builder.build_unconditional_branch(next).map_err(be)?;

        // clauses are mutually exclusive at runtime: each attempt may reuse
        // the temp slots of the previous one (subject slots sit below wm)
        let wm = self.next_slot.get();
        for (i, clause) in clauses.iter().enumerate() {
            self.next_slot.set(wm);
            self.builder.position_at_end(next);
            next = if i + 1 < clauses.len() {
                self.ctx.append_basic_block(f, &format!("clause{}", i + 1))
            } else {
                fail_bb
            };
            let nvals = match vals {
                CaseVals::Ssa(vs) => vs.len(),
                CaseVals::Slots(slots) => slots.len(),
            };
            if clause.patterns.len() != nvals {
                return Err(format!(
                    "clause has {} patterns but case argument has {} values",
                    clause.patterns.len(),
                    nvals
                ));
            }
            let mut cscope = scope.clone();
            for (i, p) in clause.patterns.iter().enumerate() {
                // reload lazily: an allocating binary pattern earlier in
                // this clause invalidates SSA copies of later subjects
                let v = match vals {
                    CaseVals::Ssa(vs) => vs[i],
                    CaseVals::Slots(slots) => self.reload(slots[i])?,
                };
                self.match_pattern(f, v, p, &mut cscope, next)?;
            }
            if !is_true_atom(&clause.guard) {
                let g = self.compile_value(f, &clause.guard, &mut cscope)?;
                let t = self.atom_term("true")?;
                let ok = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, g, t, "guard.ok")
                    .map_err(be)?;
                let body_bb = self.ctx.append_basic_block(f, &format!("body{}", i));
                self.builder
                    .build_conditional_branch(ok, body_bb, next)
                    .map_err(be)?;
                self.builder.position_at_end(body_bb);
            }
            match merge {
                None => self.compile_tail(f, &clause.body, &mut cscope)?,
                Some((merge_bb, ref mut incoming, nvals)) => {
                    let vs =
                        self.compile_body_values(f, &clause.body, &mut cscope, nvals)?;
                    let cur = self.builder.get_insert_block().unwrap();
                    incoming.push((vs, cur));
                    self.builder
                        .build_unconditional_branch(merge_bb)
                        .map_err(be)?;
                }
            }
        }

        self.builder.position_at_end(fail_bb);
        {
            let v0 = match vals {
                CaseVals::Ssa(vs) => vs.first().copied().unwrap_or_else(|| self.nil()),
                CaseVals::Slots(slots) => match slots.first() {
                    Some(s) => self.reload(*s)?,
                    None => self.nil(),
                },
            };
            let reason = self.eternal_pair("case_clause", v0)?;
            let class = self.atom_term("error")?;
            let ctx = self.ctx_val();
            self.mem_store(ctx, CTX_EXC_CLASS, class, MemKind::Ctx)?;
            self.mem_store(ctx, CTX_EXC_REASON, reason, MemKind::Ctx)?;
            let target = self.unwind_target(f)?;
            self.builder.build_unconditional_branch(target).map_err(be)?;
        }
        Ok(())
    }

    /// A clause body producing `nvals` values (Core Erlang `<a, b>` bodies
    /// under multi-value lets). nvals == 1 accepts any expression; multi
    /// accepts Values plus Let/Do/Case wrappers around them.
    fn compile_body_values(
        &self,
        f: FunctionValue<'ctx>,
        body: &Expr,
        scope: &mut Scope<'ctx>,
        nvals: usize,
    ) -> CgResult<Vec<IntValue<'ctx>>> {
        if nvals == 1 {
            return Ok(vec![self.compile_value(f, body, scope)?]);
        }
        match body {
            Expr::Values(es) if es.len() == nvals => es
                .iter()
                .map(|e| self.compile_value(f, e, scope))
                .collect(),
            Expr::Let { vars, arg, body } => {
                self.bind_let(f, vars, arg, scope)?;
                self.compile_body_values(f, body, scope, nvals)
            }
            Expr::Do(a, b) => {
                let wm = self.next_slot.get();
                self.compile_value(f, a, scope)?;
                self.next_slot.set(wm);
                self.compile_body_values(f, b, scope, nvals)
            }
            Expr::Case { arg, clauses } => {
                Ok(self.compile_case_values(f, arg, clauses, scope, nvals)?)
            }
            // raising bodies produce no values; the phi inputs are dead
            Expr::PrimOp { name, args } if is_raise(name) => {
                self.compile_raise(f, name, args, scope)?;
                Ok(vec![self.i64t.get_undef(); nvals])
            }
            Expr::Call { module, name, args }
                if module == "erlang"
                    && matches!(
                        (name.as_str(), args.len()),
                        ("error", 1) | ("error", 2) | ("error", 3) | ("exit", 1)
                            | ("throw", 1)
                    ) =>
            {
                self.compile_raise(f, name, &args[..1.max(args.len().min(2))], scope)?;
                Ok(vec![self.i64t.get_undef(); nvals])
            }
            other => Err(format!(
                "multi-value body shape not supported ({} values): {:.60?}",
                nvals, other
            )),
        }
    }

    /// A case in value position yielding `nvals` values via N phis.
    fn compile_case_values(
        &self,
        f: FunctionValue<'ctx>,
        arg: &Expr,
        clauses: &[Clause],
        scope: &mut Scope<'ctx>,
        nvals: usize,
    ) -> CgResult<Vec<IntValue<'ctx>>> {
        let vals = self.compile_case_arg(f, arg, clauses, scope)?;
        let merge = self.ctx.append_basic_block(f, "mcase.merge");
        let mut incoming: Vec<(Vec<IntValue<'ctx>>, BasicBlock<'ctx>)> = Vec::new();
        self.compile_case(f, &vals, clauses, scope, Some((merge, &mut incoming, nvals)))?;
        self.builder.position_at_end(merge);
        let mut out = Vec::with_capacity(nvals);
        for i in 0..nvals {
            let phi = self
                .builder
                .build_phi(self.i64t, &format!("mcase.v{}", i))
                .map_err(be)?;
            for (vs, bb) in &incoming {
                phi.add_incoming(&[(&vs[i], *bb)]);
            }
            out.push(phi.as_basic_value().into_int_value());
        }
        Ok(out)
    }

    /// Emit tests for `pat` against `val`, branching to `fail` on mismatch.
    /// Patterns don't allocate — EXCEPT binary patterns with binary-type
    /// segments, which build sub-binaries (GC points). Wherever a sub-pattern
    /// may allocate, the enclosing arm keeps its subject in a frame slot and
    /// re-derives pointers after the sub-match, so no stale SSA pointer is
    /// ever used across a collection (functions containing such patterns are
    /// framed by effect analysis; bound vars are already slot-backed).
    fn match_pattern(
        &self,
        f: FunctionValue<'ctx>,
        val: IntValue<'ctx>,
        pat: &Pattern,
        scope: &mut Scope<'ctx>,
        fail: BasicBlock<'ctx>,
    ) -> CgResult<()> {
        match pat {
            Pattern::Var(v) => self.bind_var(scope, v, val),
            Pattern::Alias(v, inner) => {
                self.bind_var(scope, v, val)?;
                self.match_pattern(f, val, inner, scope, fail)
            }
            Pattern::Lit(l @ Literal::Big(_)) => {
                // interned big-literal terms have pointer identity, but a
                // matching value may also arrive via ==-equal biglit from
                // another intern site — compare exactly
                let expect = self.compile_literal(l)?;
                let call = self
                    .builder
                    .build_call(
                        self.rt_tt_i64("mana_rt_eq_exact"),
                        &[val.into(), expect.into()],
                        "bigpat",
                    )
                    .map_err(be)?;
                let e = call_result(call)?.into_int_value();
                let ok = self
                    .builder
                    .build_int_compare(
                        IntPredicate::NE,
                        e,
                        self.i64t.const_zero(),
                        "bigpat.ok",
                    )
                    .map_err(be)?;
                self.branch_test(f, ok, fail)
            }
            Pattern::Lit(Literal::Float(x)) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_tt_i64("mana_rt_float_pat"),
                        &[
                            val.into(),
                            self.i64t.const_int(x.to_bits(), false).into(),
                        ],
                        "fpat",
                    )
                    .map_err(be)?;
                let ok = call_result(call)?.into_int_value();
                let ok = self
                    .builder
                    .build_int_compare(
                        IntPredicate::NE,
                        ok,
                        self.i64t.const_zero(),
                        "fpat.ok",
                    )
                    .map_err(be)?;
                self.branch_test(f, ok, fail)
            }
            Pattern::Binary(segs) => self.match_binary(f, val, segs, scope, fail),
            Pattern::Map(pairs) => {
                // a map pattern — even the empty `~{}~`, which requires no
                // keys — only ever matches maps
                let is_map = self.kind_test(f, val, |s, header| {
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
                self.branch_test(f, is_map, fail)?;
                let slot = self.pattern_subject_slot(pat, val)?;
                for (k, sub) in pairs {
                    let subject = match slot {
                        Some(s) => self.reload(s)?,
                        None => val,
                    };
                    // immediate literal keys (atoms/smalls/nil) equal only
                    // bit-identical terms: scan the key words inline — no
                    // runtime call
                    let immediate_key = matches!(
                        k,
                        Expr::Lit(Literal::Atom(_) | Literal::Nil)
                    ) || matches!(k, Expr::Lit(Literal::Int(v)) if v.unsigned_abs() < (1 << 60));
                    let v = if immediate_key {
                        let key = self.compile_value(f, k, scope)?;
                        self.inline_map_get(f, subject, key, fail)?
                    } else {
                        let key = self.compile_value(f, k, scope)?;
                        let call = self
                            .builder
                            .build_call(
                                self.rt_tt_i64("mana_rt_map_pat_get"),
                                &[subject.into(), key.into()],
                                "mpat",
                            )
                            .map_err(be)?;
                        let v = call_result(call)?.into_int_value();
                        let hit = self
                            .builder
                            .build_int_compare(IntPredicate::NE, v, self.sentinel(), "mpat.h")
                            .map_err(be)?;
                        self.branch_test(f, hit, fail)?;
                        v
                    };
                    self.match_pattern(f, v, sub, scope, fail)?;
                }
                Ok(())
            }
            Pattern::Lit(l) => {
                let expect = self.compile_literal(l)?;
                let eq = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, val, expect, "lit.eq")
                    .map_err(be)?;
                self.branch_test(f, eq, fail)
            }
            Pattern::Tuple(ps) => {
                let tag = self.tag_of(val)?;
                let is_boxed = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_zero(),
                        "is.boxed",
                    )
                    .map_err(be)?;
                self.branch_test(f, is_boxed, fail)?;
                let p = self
                    .builder
                    .build_int_to_ptr(val, self.ptrt, "tuple.ptr")
                    .map_err(be)?;
                let header = self.load_word(p, 0)?;
                let want = self
                    .i64t
                    .const_int(((ps.len() as u64) << 8) | KIND_TUPLE, false);
                let hdr_ok = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, header, want, "hdr.ok")
                    .map_err(be)?;
                self.branch_test(f, hdr_ok, fail)?;
                let slot = self.pattern_subject_slot(pat, val)?;
                for (i, sub) in ps.iter().enumerate() {
                    let p = match slot {
                        Some(s) => {
                            let subject = self.reload(s)?;
                            self.builder
                                .build_int_to_ptr(subject, self.ptrt, "tuple.ptr")
                                .map_err(be)?
                        }
                        None => p,
                    };
                    let elem = self.load_word(p, 1 + i as u64)?;
                    self.match_pattern(f, elem, sub, scope, fail)?;
                }
                Ok(())
            }
            Pattern::Cons(h, t) => {
                let tag = self.tag_of(val)?;
                let is_cons = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_int(TAG_CONS, false),
                        "is.cons",
                    )
                    .map_err(be)?;
                self.branch_test(f, is_cons, fail)?;
                let addr = self
                    .builder
                    .build_and(val, self.i64t.const_int(!TAG_MASK, false), "cons.addr")
                    .map_err(be)?;
                let p = self
                    .builder
                    .build_int_to_ptr(addr, self.ptrt, "cons.ptr")
                    .map_err(be)?;
                let slot = self.pattern_subject_slot(pat, val)?;
                let head = self.load_word(p, 0)?;
                self.match_pattern(f, head, h, scope, fail)?;
                let p = match slot {
                    Some(s) => {
                        let subject = self.reload(s)?;
                        let addr = self
                            .builder
                            .build_and(
                                subject,
                                self.i64t.const_int(!TAG_MASK, false),
                                "cons.addr",
                            )
                            .map_err(be)?;
                        self.builder
                            .build_int_to_ptr(addr, self.ptrt, "cons.ptr")
                            .map_err(be)?
                    }
                    None => p,
                };
                let tail = self.load_word(p, 1)?;
                self.match_pattern(f, tail, t, scope, fail)
            }
        }
    }

    /// If this pattern's sub-matches contain a GC point, park the subject in
    /// a frame slot so the caller can re-derive pointers after each one.
    fn pattern_subject_slot(&self, pat: &Pattern, val: IntValue<'ctx>) -> CgResult<Option<u64>> {
        if !pattern_may_gc(pat) {
            return Ok(None);
        }
        if !self.framed() {
            return Err("internal: allocating pattern in frameless function".into());
        }
        Ok(Some(self.spill(val)?))
    }

    /// Match a bitstring pattern. The byte offset is a runtime value once
    /// any segment has a dynamic size (or is utf8). Binary-type segments
    /// allocate sub-binaries; the subject is kept in a frame slot across
    /// those (see match_pattern). Constant-size integer literals compare
    /// against static byte arrays.
    fn match_binary(
        &self,
        f: FunctionValue<'ctx>,
        val: IntValue<'ctx>,
        segs: &[mana_syntax::BinSegment<Box<Pattern>>],
        scope: &mut Scope<'ctx>,
        fail: BasicBlock<'ctx>,
    ) -> CgResult<()> {
        let specs = segs
            .iter()
            .map(|s| parse_seg_spec(&s.spec))
            .collect::<Result<Vec<_>, _>>()?;
        let slot = if specs.iter().any(|s| s.kind.allocates()) {
            if !self.framed() {
                return Err("internal: allocating binary pattern in frameless function".into());
            }
            Some(self.spill(val)?)
        } else {
            None
        };
        let all_const = !specs.iter().any(|s| s.kind.dynamic());
        let rest = specs
            .iter()
            .any(|s| matches!(s.kind, SegKind::Bin { size: SegSize::All }));
        let const_total_bits: u64 = specs
            .iter()
            .map(|s| match s.kind {
                SegKind::Int { size: SegSize::Bytes(n) }
                | SegKind::Bin { size: SegSize::Bytes(n) } => 8 * n,
                SegKind::Int { size: SegSize::Bits(b) } => b,
                _ => 0,
            })
            .sum();
        let at_least = rest || !all_const;
        if !at_least && const_total_bits % 8 != 0 {
            // our binaries are byte-aligned: an exact sub-byte-total
            // pattern can never match
            self.builder.build_unconditional_branch(fail).map_err(be)?;
            let dead = self.ctx.append_basic_block(f, "bm.dead");
            self.builder.position_at_end(dead);
            return Ok(());
        }
        let const_total: u64 = const_total_bits.div_ceil(8);
        // preflight: is-binary + (for all-const patterns) the length check;
        // dynamic patterns re-check bounds per segment. Inline: tag test,
        // kind byte, length compare — no runtime call.
        let ok = self.kind_test(f, val, |s, header| {
            let k = s
                .builder
                .build_and(header, s.i64t.const_int(0xff, false), "bl.k")
                .map_err(be)?;
            let is_bin = s
                .builder
                .build_int_compare(
                    IntPredicate::EQ,
                    k,
                    s.i64t.const_int(KIND_BIN, false),
                    "bl.bin",
                )
                .map_err(be)?;
            let len = s
                .builder
                .build_right_shift(header, s.i64t.const_int(8, false), false, "bl.len")
                .map_err(be)?;
            let want = s.i64t.const_int(const_total, false);
            let lok = s
                .builder
                .build_int_compare(
                    if at_least { IntPredicate::UGE } else { IntPredicate::EQ },
                    len,
                    want,
                    "bl.ok",
                )
                .map_err(be)?;
            s.builder.build_and(is_bin, lok, "bl.and").map_err(be)
        })?;
        self.branch_test(f, ok, fail)?;

        let mut off: IntValue<'ctx> = self.i64t.const_zero();
        // true while every previous segment had a static byte width: the
        // preflight (len >= const_total) then already bounds-checks this
        // segment, so const/byte reads can inline without a runtime call.
        // static_bits tracks the exact bit offset while prefix_static.
        let mut prefix_static = true;
        let mut static_bits: u64 = 0;
        for (spec, seg) in specs.iter().zip(segs) {
            if prefix_static
                && static_bits % 8 != 0
                && !matches!(spec.kind, SegKind::Int { size: SegSize::Bits(_) })
            {
                return Err(
                    "TODO(bitstring): byte segment at a sub-byte offset".into()
                );
            }
            let subject = match slot {
                Some(s) => self.reload(s)?,
                None => val,
            };
            match &spec.kind {
                SegKind::Int { size } => {
                    if let SegSize::Bits(s) = size {
                        // sub-byte unsigned big-endian read at a constant
                        // bit offset (nibble destructuring in
                        // Code.Identifier.escape and friends)
                        if !prefix_static {
                            return Err(
                                "TODO(bitstring): sub-byte segment after dynamic prefix"
                                    .into(),
                            );
                        }
                        let s = *s;
                        let first = static_bits / 8;
                        let last = (static_bits + s - 1) / 8;
                        let bp = self
                            .builder
                            .build_int_to_ptr(subject, self.ptrt, "bb.p")
                            .map_err(be)?;
                        let mut acc = self.i64t.const_zero();
                        for byte_i in first..=last {
                            let gep = unsafe {
                                self.builder
                                    .build_in_bounds_gep(
                                        self.ctx.i8_type(),
                                        bp,
                                        &[self.i64t.const_int(8 + byte_i, false)],
                                        "bb.g",
                                    )
                                    .map_err(be)?
                            };
                            let b = self
                                .builder
                                .build_load(self.ctx.i8_type(), gep, "bb.b")
                                .map_err(be)?
                                .into_int_value();
                            let w = self
                                .builder
                                .build_int_z_extend(b, self.i64t, "bb.w")
                                .map_err(be)?;
                            let shifted = self
                                .builder
                                .build_left_shift(
                                    acc,
                                    self.i64t.const_int(8, false),
                                    "bb.sh",
                                )
                                .map_err(be)?;
                            acc = self.builder.build_or(shifted, w, "bb.acc").map_err(be)?;
                        }
                        let span_bits = (last - first + 1) * 8;
                        let shift = span_bits - (static_bits - first * 8) - s;
                        let down = self
                            .builder
                            .build_right_shift(
                                acc,
                                self.i64t.const_int(shift, false),
                                false,
                                "bb.dn",
                            )
                            .map_err(be)?;
                        let masked = self
                            .builder
                            .build_and(
                                down,
                                self.i64t.const_int((1u64 << s) - 1, false),
                                "bb.msk",
                            )
                            .map_err(be)?;
                        let v = self.retag_int(masked)?;
                        self.match_pattern(f, v, &seg.value, scope, fail)?;
                        static_bits += s;
                        if static_bits % 8 == 0 {
                            off = self.i64t.const_int(static_bits / 8, false);
                        }
                        continue;
                    }
                    let nbytes = self.seg_bytes(f, size, scope, Some(fail))?;
                    // constant integer sub-patterns with constant sizes
                    // compare as bytes (covers erlc's wide folded literals)
                    if let (SegSize::Bytes(n), Pattern::Lit(l @ (Literal::Int(_) | Literal::Big(_)))) =
                        (size, seg.value.as_ref())
                    {
                        if let Some(bytes) =
                            seg_const_bytes(&Expr::Lit(l.clone()), *n, spec.little)?
                        {
                            // short literals under a preflighted length:
                            // inline byte loads + compares (the whitespace
                            // trim pyramid runs ~20 of these per string)
                            if prefix_static && bytes.len() <= 16 {
                                let bp = self
                                    .builder
                                    .build_int_to_ptr(subject, self.ptrt, "bm.p")
                                    .map_err(be)?;
                                let mut ok = self.ctx.bool_type().const_all_ones();
                                for (j, byte) in bytes.iter().enumerate() {
                                    let idx = self
                                        .builder
                                        .build_int_add(
                                            off,
                                            self.i64t.const_int(8 + j as u64, false),
                                            "bm.i",
                                        )
                                        .map_err(be)?;
                                    let gep = unsafe {
                                        self.builder
                                            .build_in_bounds_gep(
                                                self.ctx.i8_type(),
                                                bp,
                                                &[idx],
                                                "bm.g",
                                            )
                                            .map_err(be)?
                                    };
                                    let b = self
                                        .builder
                                        .build_load(self.ctx.i8_type(), gep, "bm.b")
                                        .map_err(be)?
                                        .into_int_value();
                                    let eq = self
                                        .builder
                                        .build_int_compare(
                                            IntPredicate::EQ,
                                            b,
                                            self.ctx.i8_type().const_int(*byte as u64, false),
                                            "bm.eq",
                                        )
                                        .map_err(be)?;
                                    ok = self.builder.build_and(ok, eq, "bm.and").map_err(be)?;
                                }
                                self.branch_test(f, ok, fail)?;
                                off = self
                                    .builder
                                    .build_int_add(
                                        off,
                                        self.i64t.const_int(bytes.len() as u64, false),
                                        "boff",
                                    )
                                    .map_err(be)?;
                                static_bits += 8 * bytes.len() as u64;
                                continue;
                            }
                            let ptr = self.static_bytes(&bytes)?;
                            let call = self
                                .builder
                                .build_call(
                                    self.rt_fn("mana_rt_bin_match_bytes", || {
                                        self.i64t.fn_type(
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
                                        subject.into(),
                                        off.into(),
                                        ptr.into(),
                                        self.i64t.const_int(bytes.len() as u64, false).into(),
                                    ],
                                    "bmb",
                                )
                                .map_err(be)?;
                            let ok = call_result(call)?.into_int_value();
                            let ok = self
                                .builder
                                .build_int_compare(
                                    IntPredicate::NE,
                                    ok,
                                    self.i64t.const_zero(),
                                    "bmb.ok",
                                )
                                .map_err(be)?;
                            self.branch_test(f, ok, fail)?;
                            off = self
                                .builder
                                .build_int_add(
                                    off,
                                    self.i64t.const_int(bytes.len() as u64, false),
                                    "boff",
                                )
                                .map_err(be)?;
                            static_bits += 8 * bytes.len() as u64;
                            continue;
                        }
                    }
                    if matches!(size, SegSize::Bytes(n) if *n > 8) {
                        return Err("TODO(bignum): binding integer segments over 64 bits".into());
                    }
                    // 1-byte unsigned reads under a preflighted length:
                    // inline load (<<h, rest::binary>> — the string-walk
                    // shape)
                    if prefix_static && matches!(size, SegSize::Bytes(1)) && !spec.signed {
                        let bp = self
                            .builder
                            .build_int_to_ptr(subject, self.ptrt, "br.p")
                            .map_err(be)?;
                        let idx = self
                            .builder
                            .build_int_add(off, self.i64t.const_int(8, false), "br.i")
                            .map_err(be)?;
                        let gep = unsafe {
                            self.builder
                                .build_in_bounds_gep(self.ctx.i8_type(), bp, &[idx], "br.g")
                                .map_err(be)?
                        };
                        let b = self
                            .builder
                            .build_load(self.ctx.i8_type(), gep, "br.b")
                            .map_err(be)?
                            .into_int_value();
                        let w = self
                            .builder
                            .build_int_z_extend(b, self.i64t, "br.w")
                            .map_err(be)?;
                        let v = self.retag_int(w)?;
                        self.match_pattern(f, v, &seg.value, scope, fail)?;
                        off = self
                            .builder
                            .build_int_add(off, self.i64t.const_int(1, false), "boff")
                            .map_err(be)?;
                        static_bits += 8;
                        continue;
                    }
                    let flags = (spec.little as u64) | ((spec.signed as u64) << 1);
                    let call = self
                        .builder
                        .build_call(
                            self.rt_fn("mana_rt_bin_read_int", || {
                                self.i64t.fn_type(
                                    &[
                                        BasicMetadataTypeEnum::IntType(self.i64t),
                                        BasicMetadataTypeEnum::IntType(self.i64t),
                                        BasicMetadataTypeEnum::IntType(self.i64t),
                                        BasicMetadataTypeEnum::IntType(self.i64t),
                                    ],
                                    false,
                                )
                            }),
                            &[
                                subject.into(),
                                off.into(),
                                nbytes.into(),
                                self.i64t.const_int(flags, false).into(),
                            ],
                            "bri",
                        )
                        .map_err(be)?;
                    let v = call_result(call)?.into_int_value();
                    if !all_const {
                        let ok = self
                            .builder
                            .build_int_compare(IntPredicate::NE, v, self.sentinel(), "bri.ok")
                            .map_err(be)?;
                        self.branch_test(f, ok, fail)?;
                    }
                    self.match_pattern(f, v, &seg.value, scope, fail)?;
                    off = self.builder.build_int_add(off, nbytes, "boff").map_err(be)?;
                }
                SegKind::Bin { size } => {
                    let len: IntValue<'ctx> = match size {
                        SegSize::All => self.i64t.const_int(u64::MAX, false), // -1
                        _ => self.seg_bytes(f, size, scope, Some(fail))?,
                    };
                    let call = self
                        .builder
                        .build_call(
                            self.rt_fn("mana_rt_bin_slice", || {
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
                                subject.into(),
                                off.into(),
                                len.into(),
                            ],
                            "brs",
                        )
                        .map_err(be)?;
                    let v = call_result(call)?.into_int_value();
                    let ok = self
                        .builder
                        .build_int_compare(IntPredicate::NE, v, self.sentinel(), "brs.ok")
                        .map_err(be)?;
                    self.branch_test(f, ok, fail)?;
                    self.match_pattern(f, v, &seg.value, scope, fail)?;
                    if !matches!(size, SegSize::All) {
                        off = self.builder.build_int_add(off, len, "boff").map_err(be)?;
                    }
                }
                SegKind::Utf8 => {
                    let call = self
                        .builder
                        .build_call(
                            self.rt_tt_i64("mana_rt_bin_read_utf8"),
                            &[subject.into(), off.into()],
                            "bru",
                        )
                        .map_err(be)?;
                    let raw = call_result(call)?.into_int_value();
                    let ok = self
                        .builder
                        .build_int_compare(
                            IntPredicate::SGE,
                            raw,
                            self.i64t.const_zero(),
                            "bru.ok",
                        )
                        .map_err(be)?;
                    self.branch_test(f, ok, fail)?;
                    let cp = self
                        .builder
                        .build_and(raw, self.i64t.const_int(0xffff_ffff, false), "bru.cp")
                        .map_err(be)?;
                    let cpt = self.retag_int(cp)?;
                    self.match_pattern(f, cpt, &seg.value, scope, fail)?;
                    let width = self
                        .builder
                        .build_right_shift(raw, self.i64t.const_int(32, false), false, "bru.w")
                        .map_err(be)?;
                    off = self.builder.build_int_add(off, width, "boff").map_err(be)?;
                }
            }
            match &spec.kind {
                SegKind::Int { size: SegSize::Bytes(n) }
                | SegKind::Bin { size: SegSize::Bytes(n) } => static_bits += 8 * n,
                _ => prefix_static = false,
            }
        }
        // no rest segment: the pattern must consume the binary exactly
        if !rest && !all_const {
            let subject = match slot {
                Some(s) => self.reload(s)?,
                None => val,
            };
            let call = self
                .builder
                .build_call(
                    self.rt_fn("mana_rt_bin_len_check", || {
                        self.i64t.fn_type(
                            &[
                                BasicMetadataTypeEnum::IntType(self.i64t),
                                BasicMetadataTypeEnum::IntType(self.i64t),
                                BasicMetadataTypeEnum::IntType(self.i64t),
                            ],
                            false,
                        )
                    }),
                    &[subject.into(), off.into(), self.i64t.const_zero().into()],
                    "blen.end",
                )
                .map_err(be)?;
            let ok = call_result(call)?.into_int_value();
            let ok = self
                .builder
                .build_int_compare(IntPredicate::NE, ok, self.i64t.const_zero(), "blen.end.ok")
                .map_err(be)?;
            self.branch_test(f, ok, fail)?;
        }
        Ok(())
    }

    /// The byte count of a segment as a runtime value. Dynamic sizes verify
    /// smallness/alignment: in patterns (`fail` set) a bad size is a match
    /// failure; in construction it raises badarg.
    fn seg_bytes(
        &self,
        f: FunctionValue<'ctx>,
        size: &SegSize,
        scope: &mut Scope<'ctx>,
        fail: Option<BasicBlock<'ctx>>,
    ) -> CgResult<IntValue<'ctx>> {
        match size {
            SegSize::Bytes(n) => Ok(self.i64t.const_int(*n, false)),
            SegSize::Bits(_) => Err("internal: seg_bytes on sub-byte segment".into()),
            SegSize::All => Err("internal: seg_bytes on rest segment".into()),
            SegSize::Dyn { size, unit } => {
                let v = self.compile_value(f, size, scope)?;
                // small int?
                let tag = self.tag_of(v)?;
                let is_int = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_int(TAG_SMALL, false),
                        "sz.int",
                    )
                    .map_err(be)?;
                match fail {
                    Some(fail) => self.branch_test(f, is_int, fail)?,
                    None => self.guard_badarg(f, is_int)?,
                }
                let raw = self
                    .builder
                    .build_right_shift(v, self.i64t.const_int(3, false), true, "sz.raw")
                    .map_err(be)?;
                let bits = self
                    .builder
                    .build_int_mul(raw, self.i64t.const_int(*unit as u64, false), "sz.bits")
                    .map_err(be)?;
                // bits >= 0 and byte-aligned
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
                    .build_int_compare(
                        IntPredicate::SGE,
                        bits,
                        self.i64t.const_zero(),
                        "sz.nn",
                    )
                    .map_err(be)?;
                let ok = self.builder.build_and(aligned, nonneg, "sz.ok").map_err(be)?;
                match fail {
                    Some(fail) => self.branch_test(f, ok, fail)?,
                    None => self.guard_badarg(f, ok)?,
                }
                self.builder
                    .build_right_shift(bits, self.i64t.const_int(3, false), false, "sz.bytes")
                    .map_err(be)
            }
        }
    }


    fn branch_test(
        &self,
        f: FunctionValue<'ctx>,
        cond: IntValue<'ctx>,
        fail: BasicBlock<'ctx>,
    ) -> CgResult<()> {
        let cont = self.ctx.append_basic_block(f, "m.cont");
        self.builder
            .build_conditional_branch(cond, cont, fail)
            .map_err(be)?;
        self.builder.position_at_end(cont);
        Ok(())
    }

    // ---- BIFs (none allocate today; TODO(bignum) changes that) ----

    fn compile_bif(
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
        if module == "file" {
            // native file cut (OTP's file.erl/prim_file never compiled) —
            // implemented names dispatch to mana_rt_file by opcode; the
            // rest keep answering {error, enotsup}
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

        match (name, argv.len()) {
            ("raise", 3) => {
                // re-raise with a dynamic class; the stacktrace argument is
                // dropped — TODO(stacktraces)
                let ctx = self.ctx_val();
                self.mem_store(ctx, CTX_EXC_CLASS, argv[0], MemKind::Ctx)?;
                self.mem_store(ctx, CTX_EXC_REASON, argv[1], MemKind::Ctx)?;
                let target = self.unwind_target(f)?;
                self.builder.build_unconditional_branch(target).map_err(be)?;
                let dead = self.ctx.append_basic_block(f, "raise3.dead");
                self.builder.position_at_end(dead);
                Ok(self.i64t.get_undef())
            }
            ("+", 2) | ("-", 2) | ("*", 2) | ("div", 2) | ("rem", 2) => {
                // both-small inline (no allocation, no raise); anything else
                // takes the runtime slow path (floats box without triggering
                // GC — see box_float — so this is NOT a may-gc site)
                let opcode = match name {
                    "+" => 0u64,   // AR_ADD
                    "-" => 1,      // AR_SUB
                    "*" => 2,      // AR_MUL
                    "div" => 4,    // AR_IDIV (slow path = badarith)
                    _ => 5,        // AR_REM
                };
                self.arith_fastslow(f, name, opcode, argv[0], Some(argv[1]))
            }
            ("-", 1) => self.arith_fastslow(f, "neg", 6, argv[0], None),
            ("+", 1) => {
                // +X is a no-op for numbers; badarith otherwise
                let both = self.small_test(argv[0], None)?;
                let slow = self.ctx.append_basic_block(f, "pos.slow");
                let merge = self.ctx.append_basic_block(f, "pos.merge");
                let fast_bb = self.builder.get_insert_block().unwrap();
                self.builder
                    .build_conditional_branch(both, merge, slow)
                    .map_err(be)?;
                self.builder.position_at_end(slow);
                // float or junk: 0 + X coerces/validates
                let zero = self.i64t.const_int(1, false); // small 0
                let call = self
                    .builder
                    .build_call(
                        self.rt_arith(),
                        &[
                            self.ctx_val().into(),
                            self.i64t.const_zero().into(),
                            zero.into(),
                            argv[0].into(),
                        ],
                        "pos",
                    )
                    .map_err(be)?;
                let sv = call_result(call)?.into_int_value();
                let sv = self.check_exc(f, sv)?;
                let slow_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(merge).map_err(be)?;
                self.builder.position_at_end(merge);
                let phi = self.builder.build_phi(self.i64t, "pos.v").map_err(be)?;
                phi.add_incoming(&[(&argv[0], fast_bb), (&sv, slow_end)]);
                Ok(phi.as_basic_value().into_int_value())
            }
            ("<", 2) | ("=<", 2) | (">", 2) | (">=", 2) | ("==", 2) | ("/=", 2)
            | ("=:=", 2) | ("=/=", 2) => {
                // fast path: both small ints (tagging is order-preserving);
                // slow path: full Erlang term order in the runtime
                let pred = match name {
                    "<" => IntPredicate::SLT,
                    "=<" => IntPredicate::SLE,
                    ">" => IntPredicate::SGT,
                    ">=" => IntPredicate::SGE,
                    "==" | "=:=" => IntPredicate::EQ,
                    _ => IntPredicate::NE,
                };
                let (a, b) = (argv[0], argv[1]);
                let one = self.i64t.const_int(1, false);
                let ta = self.tag_of(a)?;
                let tb = self.tag_of(b)?;
                let sa = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, ta, one, "sa")
                    .map_err(be)?;
                let sb = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, tb, one, "sb")
                    .map_err(be)?;
                let both = self.builder.build_and(sa, sb, "both.small").map_err(be)?;
                let fast = self.ctx.append_basic_block(f, "cmp.fast");
                let slow = self.ctx.append_basic_block(f, "cmp.slow");
                let merge = self.ctx.append_basic_block(f, "cmp.merge");
                self.builder
                    .build_conditional_branch(both, fast, slow)
                    .map_err(be)?;

                self.builder.position_at_end(fast);
                let cf = self
                    .builder
                    .build_int_compare(pred, a, b, "cmp.i")
                    .map_err(be)?;
                let vf = self.bool_term(cf)?;
                let fast_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(merge).map_err(be)?;

                self.builder.position_at_end(slow);
                let vs = match name {
                    "=:=" | "=/=" => {
                        let call = self
                            .builder
                            .build_call(
                                self.rt_tt_i64("mana_rt_eq_exact"),
                                &[a.into(), b.into()],
                                "eqx",
                            )
                            .map_err(be)?;
                        let r = call_result(call)?.into_int_value();
                        let want = if name == "=:=" { 1 } else { 0 };
                        let c = self
                            .builder
                            .build_int_compare(
                                IntPredicate::EQ,
                                r,
                                self.i64t.const_int(want, false),
                                "eqx.c",
                            )
                            .map_err(be)?;
                        self.bool_term(c)?
                    }
                    _ => {
                        let call = self
                            .builder
                            .build_call(
                                self.rt_tt_i64("mana_rt_compare"),
                                &[a.into(), b.into()],
                                "ord",
                            )
                            .map_err(be)?;
                        let r = call_result(call)?.into_int_value();
                        let c = self
                            .builder
                            .build_int_compare(pred, r, self.i64t.const_zero(), "ord.c")
                            .map_err(be)?;
                        self.bool_term(c)?
                    }
                };
                let slow_end = self.builder.get_insert_block().unwrap();
                self.builder.build_unconditional_branch(merge).map_err(be)?;

                self.builder.position_at_end(merge);
                let phi = self.builder.build_phi(self.i64t, "cmp.v").map_err(be)?;
                phi.add_incoming(&[(&vf, fast_end), (&vs, slow_end)]);
                Ok(phi.as_basic_value().into_int_value())
            }
            ("self", 0) => {
                let call = self
                    .builder
                    .build_call(self.rt_p_i64("mana_rt_self"), &[self.ctx_val().into()], "self")
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
                // 0 = not an arity-0 fun
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
                self.builder.build_unconditional_branch(target).map_err(be)?;
                self.builder.position_at_end(ok_bb);
                Ok(pid)
            }
            ("make_ref", 0) => {
                let call = self
                    .builder
                    .build_call(self.rt_p_i64("mana_rt_make_ref"), &[self.ctx_val().into()], "r")
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
                // monitor(process, Pid) — first arg assumed 'process'
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
                self.builder.build_unconditional_branch(target).map_err(be)?;
                self.builder.position_at_end(ok_bb);
                Ok(r)
            }
            ("process_flag", 2) => {
                // dispatch on the flag name: trap_exit is real, the rest
                // are accepted no-ops returning a plausible old value
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
            ("/", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_arith(),
                        &[
                            self.ctx_val().into(),
                            self.i64t.const_int(3, false).into(), // AR_FDIV
                            argv[0].into(),
                            argv[1].into(),
                        ],
                        "fdiv",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
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
            ("term_to_binary", 1) | ("term_to_binary", 2)
            | ("binary_to_term", 1) | ("binary_to_term", 2) => {
                let helper = if name == "term_to_binary" {
                    "mana_rt_term_to_binary"
                } else {
                    "mana_rt_binary_to_term"
                };
                let opts = argv.get(1).copied().unwrap_or(self.nil());
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64(helper),
                        &[self.ctx_val().into(), argv[0].into(), opts.into()],
                        "etf",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
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
            ("phash2", 1) | ("phash2", 2) => {
                let callee = self.rt_fn("mana_rt_phash2", || {
                    self.i64t.fn_type(
                        &[
                            BasicMetadataTypeEnum::PointerType(self.ptrt),
                            BasicMetadataTypeEnum::IntType(self.i64t),
                            BasicMetadataTypeEnum::IntType(self.i64t),
                        ],
                        false,
                    )
                });
                let range = argv.get(1).copied().unwrap_or(self.i64t.const_zero());
                let call = self
                    .builder
                    .build_call(
                        callee,
                        &[self.ctx_val().into(), argv[0].into(), range.into()],
                        "ph2",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
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
            ("iolist_size", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_iolist_size"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "iosz",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
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
            ("decode_packet", 3) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_fn("mana_rt_decode_packet", || {
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
                        "dpkt",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("band", 2) | ("bor", 2) | ("bxor", 2) => {
                let opcode = match name {
                    "band" => 8u64, // AR_BAND
                    "bor" => 9,     // AR_BOR
                    _ => 10,        // AR_BXOR
                };
                self.arith_fastslow(f, name, opcode, argv[0], Some(argv[1]))
            }
            ("bnot", 1) => self.arith_fastslow(f, "bnot", 13, argv[0], None),
            ("bsl", 2) | ("bsr", 2) => {
                // no inline fast path: shift semantics (negative amounts,
                // 61-bit overflow abort) live in the runtime
                let opcode = if name == "bsl" { 11u64 } else { 12 }; // AR_BSL/AR_BSR
                let call = self
                    .builder
                    .build_call(
                        self.rt_arith(),
                        &[
                            self.ctx_val().into(),
                            self.i64t.const_int(opcode, false).into(),
                            argv[0].into(),
                            argv[1].into(),
                        ],
                        "bshift",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("float", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_to_float"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "tofl",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("trunc", 1) | ("round", 1) | ("floor", 1) | ("ceil", 1) => {
                let mode = match name {
                    "trunc" => 0u64,
                    "round" => 1,
                    "floor" => 2,
                    _ => 3,
                };
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_f2i"),
                        &[
                            self.ctx_val().into(),
                            self.i64t.const_int(mode, false).into(),
                            argv[0].into(),
                        ],
                        "f2i",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("float_to_binary", 1) | ("float_to_binary", 2) | ("float_to_list", 1)
            | ("float_to_list", 2) => {
                let opts = if argv.len() == 2 { argv[1] } else { self.nil() };
                let callee = self.rt_fn("mana_rt_float_to_binary", || {
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
                            opts.into(),
                            self.i64t
                                .const_int(name.ends_with("list") as u64, false)
                                .into(),
                        ],
                        "f2b",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("binary_to_float", 1) | ("list_to_float", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_parse_float"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "pf",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("!", 2) | ("send", 2) | ("send", 3) => {
                // send/3's options (noconnect/nosuspend) are distribution
                // concerns — ignored; it returns ok instead of the message
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
            ("and", 2) | ("or", 2) | ("xor", 2) => {
                let t = self.atom_term("true")?;
                let a = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, argv[0], t, "a")
                    .map_err(be)?;
                let b = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, argv[1], t, "b")
                    .map_err(be)?;
                let r = match name {
                    "and" => self.builder.build_and(a, b, "and"),
                    "or" => self.builder.build_or(a, b, "or"),
                    _ => self.builder.build_xor(a, b, "xor"),
                }
                .map_err(be)?;
                let fa = self.atom_term("false")?;
                Ok(self
                    .builder
                    .build_select(r, t, fa, "bool")
                    .map_err(be)?
                    .into_int_value())
            }
            ("not", 1) => {
                let t = self.atom_term("true")?;
                let fa = self.atom_term("false")?;
                let a = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, argv[0], t, "a")
                    .map_err(be)?;
                Ok(self
                    .builder
                    .build_select(a, fa, t, "not")
                    .map_err(be)?
                    .into_int_value())
            }
            ("is_integer", 1) | ("is_atom", 1) | ("is_pid", 1) | ("is_reference", 1) => {
                let want: u64 = match name {
                    "is_integer" => 1,
                    "is_atom" => 2,
                    "is_pid" => 0b0110,
                    _ => 0b1110,
                };
                let mask: u64 = if name == "is_pid" || name == "is_reference" {
                    0xF
                } else {
                    7
                };
                let m = self
                    .builder
                    .build_and(argv[0], self.i64t.const_int(mask, false), "tt")
                    .map_err(be)?;
                let c = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        m,
                        self.i64t.const_int(want, false),
                        "tt.c",
                    )
                    .map_err(be)?;
                self.bool_term(c)
            }
            ("is_list", 1) => {
                let tag = self.tag_of(argv[0])?;
                let cons = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_int(0b100, false),
                        "il.c",
                    )
                    .map_err(be)?;
                let nil = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, argv[0], self.nil(), "il.n")
                    .map_err(be)?;
                let c = self.builder.build_or(cons, nil, "il").map_err(be)?;
                self.bool_term(c)
            }
            ("is_boolean", 1) => {
                let t = self.atom_term("true")?;
                let fa = self.atom_term("false")?;
                let a = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, argv[0], t, "ib.t")
                    .map_err(be)?;
                let b = self
                    .builder
                    .build_int_compare(IntPredicate::EQ, argv[0], fa, "ib.f")
                    .map_err(be)?;
                let c = self.builder.build_or(a, b, "ib").map_err(be)?;
                self.bool_term(c)
            }
            ("is_tuple", 1) | ("is_float", 1) | ("is_function", 1) => {
                let kind: u64 = match name {
                    "is_tuple" => KIND_TUPLE,
                    "is_float" => KIND_FLOAT,
                    _ => KIND_FUN,
                };
                let c = self.kind_test(f, argv[0], |s, header| {
                    let k = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xff, false), "k")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            k,
                            s.i64t.const_int(kind, false),
                            "k.c",
                        )
                        .map_err(be)
                })?;
                self.bool_term(c)
            }
            ("is_function", 2) => {
                let arity = argv[1];
                let c = self.kind_test(f, argv[0], |s, header| {
                    let ka = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xffff, false), "ka")
                        .map_err(be)?;
                    let want_lo = s
                        .builder
                        .build_right_shift(arity, s.i64t.const_int(3, false), true, "ar")
                        .map_err(be)?;
                    let want = s
                        .builder
                        .build_left_shift(want_lo, s.i64t.const_int(8, false), "ar8")
                        .map_err(be)?;
                    let want = s
                        .builder
                        .build_or(want, s.i64t.const_int(KIND_FUN, false), "want")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(IntPredicate::EQ, ka, want, "isf2")
                        .map_err(be)
                })?;
                self.bool_term(c)
            }
            ("is_number", 1) => {
                let tag = self.tag_of(argv[0])?;
                let small = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_int(1, false),
                        "n.s",
                    )
                    .map_err(be)?;
                let isf = self.kind_test(f, argv[0], |s, header| {
                    let k = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xff, false), "k")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            k,
                            s.i64t.const_int(KIND_FLOAT, false),
                            "k.f",
                        )
                        .map_err(be)
                })?;
                let c = self.builder.build_or(small, isf, "isnum").map_err(be)?;
                self.bool_term(c)
            }
            ("apply", 3) | ("apply", 2) => {
                let helper = if argv.len() == 3 { "mana_rt_apply3" } else { "mana_rt_apply_fun" };
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
                let call = self.builder.build_call(callee, &cargs, "apply").map_err(be)?;
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
                        // [link]
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
                    self.i64t.fn_type(
                        &[BasicMetadataTypeEnum::PointerType(self.ptrt)],
                        false,
                    )
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
                // options: [flush] (and/or info) — flush is honored, the
                // info return value approximated; options list is constant
                // in practice so it is not inspected
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
            ("monotonic_time", 0) | ("monotonic_time", 1) | ("system_time", 0)
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
            ("garbage_collect", 0) => self.atom_term("true"),
            ("is_port", 1) => self.atom_term("false"),
            // no distribution: everything lives on nonode@nohost
            ("node", 0) | ("node", 1) => self.atom_term("nonode@nohost"),
            ("nodes", 0) | ("nodes", 1) => Ok(self.nil()),
            ("is_alive", 0) => self.atom_term("false"),
            ("is_binary", 1) | ("is_bitstring", 1) => {
                // byte-aligned only: binary <=> bitstring
                let c = self.kind_test(f, argv[0], |s, header| {
                    let k = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xff, false), "k")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            k,
                            s.i64t.const_int(KIND_BIN, false),
                            "k.b",
                        )
                        .map_err(be)
                })?;
                self.bool_term(c)
            }
            ("byte_size", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_byte_size"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "bsz",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("bit_size", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_byte_size"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "bsz",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                let v = self.check_exc(f, v)?;
                let raw = self
                    .builder
                    .build_right_shift(v, self.i64t.const_int(3, false), true, "bits.raw")
                    .map_err(be)?;
                let bits = self
                    .builder
                    .build_int_mul(raw, self.i64t.const_int(8, false), "bits")
                    .map_err(be)?;
                self.retag_int(bits)
            }
            ("binary_part", 3) => {
                let callee = self.rt_fn("mana_rt_binary_part", || {
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
                        "bpart",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("binary_to_integer", 1)
            | ("binary_to_integer", 2)
            | ("list_to_integer", 1)
            | ("list_to_integer", 2) => {
                let helper = if name == "binary_to_integer" {
                    "mana_rt_binary_to_integer"
                } else {
                    "mana_rt_list_to_integer"
                };
                let base = if argv.len() == 2 {
                    argv[1]
                } else {
                    self.i64t.const_int((10 << 3) | 1, false)
                };
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64(helper),
                        &[self.ctx_val().into(), argv[0].into(), base.into()],
                        "x2i",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("integer_to_binary", 1)
            | ("integer_to_binary", 2)
            | ("integer_to_list", 1)
            | ("integer_to_list", 2) => {
                let helper = if name == "integer_to_binary" {
                    "mana_rt_integer_to_binary"
                } else {
                    "mana_rt_integer_to_list"
                };
                let base = if argv.len() == 2 {
                    argv[1]
                } else {
                    self.i64t.const_int((10 << 3) | 1, false)
                };
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64(helper),
                        &[self.ctx_val().into(), argv[0].into(), base.into()],
                        "i2x",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("list_to_tuple", 1) | ("tuple_to_list", 1) => {
                let helper = if name == "list_to_tuple" {
                    "mana_rt_list_to_tuple"
                } else {
                    "mana_rt_tuple_to_list"
                };
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64(helper),
                        &[self.ctx_val().into(), argv[0].into()],
                        "t2l",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("split_binary", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_split_binary"),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "splb",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("list_to_atom", 1) | ("list_to_existing_atom", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_list_to_atom"),
                        &[
                            self.ctx_val().into(),
                            argv[0].into(),
                            self.i64t
                                .const_int((name == "list_to_existing_atom") as u64, false)
                                .into(),
                        ],
                        "l2a",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("atom_to_list", 1) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64("mana_rt_atom_to_list"),
                        &[self.ctx_val().into(), argv[0].into()],
                        "a2l",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("binary_to_list", 1)
            | ("list_to_binary", 1)
            | ("iolist_to_binary", 1)
            | ("atom_to_binary", 1)
            | ("atom_to_binary", 2)
            | ("binary_to_atom", 1)
            | ("binary_to_atom", 2)
            | ("binary_to_existing_atom", 1)
            | ("binary_to_existing_atom", 2) => {
                // encoding args (latin1/utf8) are irrelevant: names are utf8
                if name == "binary_to_atom" || name == "binary_to_existing_atom" {
                    let call = self
                        .builder
                        .build_call(
                            self.rt_ptt_i64("mana_rt_binary_to_atom"),
                            &[
                                self.ctx_val().into(),
                                argv[0].into(),
                                self.i64t
                                    .const_int(
                                        (name == "binary_to_existing_atom") as u64,
                                        false,
                                    )
                                    .into(),
                            ],
                            "b2a",
                        )
                        .map_err(be)?;
                    let v = call_result(call)?.into_int_value();
                    return self.check_exc(f, v);
                }
                let helper = match name {
                    "binary_to_list" => "mana_rt_binary_to_list",
                    "list_to_binary" => "mana_rt_list_to_binary",
                    "iolist_to_binary" => "mana_rt_iolist_to_binary",
                    _ => "mana_rt_atom_to_binary",
                };
                let call = self
                    .builder
                    .build_call(
                        self.rt_pt_i64(helper),
                        &[self.ctx_val().into(), argv[0].into()],
                        "bconv",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("is_map", 1) => {
                let c = self.kind_test(f, argv[0], |s, header| {
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
                self.bool_term(c)
            }
            ("map_size", 1) => self.map_size_of(f, argv[0]),
            ("map_get", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_map_get"),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "mg",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("is_map_key", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_ptt_i64("mana_rt_map_is_key"),
                        &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                        "mk",
                    )
                    .map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("element", 2) => {
                // element(I, Tuple), 1-based; badarg on any misuse
                let (i, t) = (argv[0], argv[1]);
                let ti = self.tag_of(i)?;
                let i_ok = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        ti,
                        self.i64t.const_int(1, false),
                        "el.i",
                    )
                    .map_err(be)?;
                let is_tup = self.kind_test(f, t, |s, header| {
                    let k = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xff, false), "k")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            k,
                            s.i64t.const_int(KIND_TUPLE, false),
                            "k.t",
                        )
                        .map_err(be)
                })?;
                let ok = self.builder.build_and(i_ok, is_tup, "el.ok").map_err(be)?;
                self.guard_badarg(f, ok)?;
                let p = self
                    .builder
                    .build_int_to_ptr(t, self.ptrt, "el.p")
                    .map_err(be)?;
                let header = self.load_word(p, 0)?;
                let arity = self
                    .builder
                    .build_right_shift(header, self.i64t.const_int(8, false), false, "el.n")
                    .map_err(be)?;
                let idx = self.untag_int(i)?;
                let ge1 = self
                    .builder
                    .build_int_compare(
                        IntPredicate::SGE,
                        idx,
                        self.i64t.const_int(1, false),
                        "el.ge",
                    )
                    .map_err(be)?;
                let le = self
                    .builder
                    .build_int_compare(IntPredicate::SLE, idx, arity, "el.le")
                    .map_err(be)?;
                let in_range = self.builder.build_and(ge1, le, "el.rng").map_err(be)?;
                self.guard_badarg(f, in_range)?;
                let slot = unsafe {
                    self.builder
                        .build_in_bounds_gep(self.i64t, p, &[idx], "el.slot")
                        .map_err(be)?
                };
                let v = self
                    .builder
                    .build_load(self.i64t, slot, "el.v")
                    .map_err(be)?;
                if let Some(inst) = v.as_instruction_value() {
                    let _ = inst.set_metadata(self.tbaa_heap, self.tbaa_kind);
                }
                Ok(v.into_int_value())
            }
            ("tuple_size", 1) => {
                let is_tup = self.kind_test(f, argv[0], |s, header| {
                    let k = s
                        .builder
                        .build_and(header, s.i64t.const_int(0xff, false), "k")
                        .map_err(be)?;
                    s.builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            k,
                            s.i64t.const_int(KIND_TUPLE, false),
                            "k.t",
                        )
                        .map_err(be)
                })?;
                self.guard_badarg(f, is_tup)?;
                let p = self
                    .builder
                    .build_int_to_ptr(argv[0], self.ptrt, "ts.p")
                    .map_err(be)?;
                let header = self.load_word(p, 0)?;
                let n = self
                    .builder
                    .build_right_shift(header, self.i64t.const_int(8, false), false, "ts.n")
                    .map_err(be)?;
                self.retag_int(n)
            }
            ("hd", 1) | ("tl", 1) => {
                let tag = self.tag_of(argv[0])?;
                let is_cons = self
                    .builder
                    .build_int_compare(
                        IntPredicate::EQ,
                        tag,
                        self.i64t.const_int(0b100, false),
                        "ht.c",
                    )
                    .map_err(be)?;
                self.guard_badarg(f, is_cons)?;
                let addr = self
                    .builder
                    .build_and(argv[0], self.i64t.const_int(!TAG_MASK, false), "ht.a")
                    .map_err(be)?;
                let p = self
                    .builder
                    .build_int_to_ptr(addr, self.ptrt, "ht.p")
                    .map_err(be)?;
                self.load_word(p, if name == "hd" { 0 } else { 1 })
            }
            ("abs", 1) => self.arith_fastslow(f, "abs", 7, argv[0], None),
            ("min", 2) | ("max", 2) => {
                let call = self
                    .builder
                    .build_call(
                        self.rt_tt_i64("mana_rt_compare"),
                        &[argv[0].into(), argv[1].into()],
                        "mm",
                    )
                    .map_err(be)?;
                let r = call_result(call)?.into_int_value();
                let pred = if name == "min" {
                    IntPredicate::SLE
                } else {
                    IntPredicate::SGE
                };
                let c = self
                    .builder
                    .build_int_compare(pred, r, self.i64t.const_zero(), "mm.c")
                    .map_err(be)?;
                Ok(self
                    .builder
                    .build_select(c, argv[0], argv[1], "mm.v")
                    .map_err(be)?
                    .into_int_value())
            }
            ("setelement", 3) | ("length", 1) | ("++", 2) | ("--", 2) => {
                let (fname, args_ll): (&str, Vec<BasicMetadataValueEnum>) = match name {
                    "setelement" => (
                        "mana_rt_setelement",
                        vec![
                            self.ctx_val().into(),
                            argv[0].into(),
                            argv[1].into(),
                            argv[2].into(),
                        ],
                    ),
                    "length" => (
                        "mana_rt_length",
                        vec![self.ctx_val().into(), argv[0].into()],
                    ),
                    "++" => (
                        "mana_rt_append",
                        vec![self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    ),
                    _ => (
                        "mana_rt_subtract",
                        vec![self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    ),
                };
                let nargs = args_ll.len();
                let callee = self.rt_fn(fname, || {
                    let mut params: Vec<BasicMetadataTypeEnum> =
                        vec![BasicMetadataTypeEnum::PointerType(self.ptrt)];
                    params.extend(
                        (1..nargs).map(|_| BasicMetadataTypeEnum::IntType(self.i64t)),
                    );
                    self.i64t.fn_type(&params, false)
                });
                let call = self.builder.build_call(callee, &args_ll, "rtb").map_err(be)?;
                let v = call_result(call)?.into_int_value();
                self.check_exc(f, v)
            }
            ("display", 1) => {
                self.builder
                    .build_call(self.rt_display(), &[argv[0].into()], "")
                    .map_err(be)?;
                self.atom_term("true")
            }
            _ => Err(format!("unsupported BIF erlang:{}/{}", name, argv.len())),
        }
    }

    /// Raise an exception: primop match_fail/raise or erlang:error|exit|throw.
    /// Reason terms are built with the eternal allocator (never moved, GC
    /// scans their fields). Leaves the builder in a dead block.
    /// (ctx, term, term) -> term runtime helper.
    fn rt_ptt_i64(&self, name: &str) -> FunctionValue<'ctx> {
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

    /// A proper list from already-rooted child values. Nursery mode: one
    /// block of headerless cons cells (single GC point). Eternal (raise
    /// path) mode: per-cell allocs, chained in SSA (no GC there).
    fn build_list_from_rooted(&self, rooted: &[Rooted<'ctx>]) -> CgResult<IntValue<'ctx>> {
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

    /// An internal constant byte array; returns its pointer.
    fn static_bytes(&self, bytes: &[u8]) -> CgResult<PointerValue<'ctx>> {
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

    /// Bitstring construction: evaluate all segment values and dynamic
    /// sizes (rooted), compute the total byte size, allocate once, then
    /// fill with non-allocating writers. Constant segments (integer
    /// literals incl. erlc's wide folded strings, constant utf8) become
    /// static byte arrays written with one memcpy.
    fn compile_binary_construct(
        &self,
        f: FunctionValue<'ctx>,
        segs: &[mana_syntax::BinSegment<Box<Expr>>],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let specs = segs
            .iter()
            .map(|s| parse_seg_spec(&s.spec))
            .collect::<Result<Vec<_>, _>>()?;
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
    fn seg_bytes_from_value(
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
    fn compile_binary_const_term(
        &self,
        f: FunctionValue<'ctx>,
        bytes: &[u8],
        _scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let _ = f;
        self.static_binary(bytes)
    }

    /// io_lib cut: format engine in the runtime, charlists out.
    fn compile_io_lib_bif(
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

    /// :re on the Rust regex crate; version() is "mana" so Elixir's Regex
    /// recompiles from source instead of trusting sigil-baked PCRE blobs.
    fn compile_re_bif(
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

    /// math module: f64 ops in the runtime (box_float never GCs).
    fn compile_math_bif(
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
        let dummy = self.i64t.const_int(1, false); // small 0
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

    /// ets cut: the global KV store (keypos 1 only, no match specs).
    fn compile_ets_bif(
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
        let call = match (name, argv.len()) {
            // tables are identified by their name term; options ignored
            ("new", 2) => self
                .builder
                .build_call(
                    self.rt_pt_i64("mana_rt_ets_new"),
                    &[self.ctx_val().into(), argv[0].into()],
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
            ("delete", 2) => self
                .builder
                .build_call(
                    self.rt_ptt_i64("mana_rt_ets_delete"),
                    &[self.ctx_val().into(), argv[0].into(), argv[1].into()],
                    "ets",
                )
                .map_err(be)?,
            // whole-table delete: treat as ok (closed world: tables die
            // with the process) — TODO(ets)
            ("delete", 1) => return self.atom_term("true"),
            _ => return Err(format!("unsupported BIF ets:{}/{}", name, argv.len())),
        };
        let v = call_result(call)?.into_int_value();
        self.check_exc(f, v)
    }

    /// application cut: env store; no applications actually start.
    fn compile_application_bif(
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
            // set_env/4's opts (timeout/persistent) are irrelevant here
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
            ("get_key", 2) | ("get_application", 0) | ("get_application", 1) => {
                self.atom_term("undefined")
            }
            _ => Err(format!(
                "unsupported BIF application:{}/{}",
                name,
                argv.len()
            )),
        }
    }

    /// code module cut: "loaded" = compiled into this binary.
    fn compile_code_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        match (name, argv.len()) {
            ("root_dir", 0) | ("lib_dir", 0) => {
                // static binaries have no OTP tree; a plausible path keeps
                // header-printing callers alive (they only display it)
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
            ("lib_dir", 1) => {
                let s = b"/mana/lib";
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

    /// persistent_term cut: a global table of eternal deep copies.
    fn compile_pt_bif(
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

    /// unicode module cut: chardata conversion in the runtime (utf8 only —
    /// the encoding arguments are evaluated and ignored).
    fn compile_unicode_bif(
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

    /// crypto cut: the Plug.Crypto subset over RustCrypto.
    fn compile_crypto_bif(
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

    /// gen_tcp/inet cut: everything routes through mana_rt_tcp by opcode.
    /// recv/accept/connect/send suspend the caller — GC + raise points.
    fn compile_tcp_bif(
        &self,
        f: FunctionValue<'ctx>,
        module: &str,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        // (opcode, arg slots, pad-with-infinity?)
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

    /// The native io cut: stdout only, bypassing OTP's group-leader
    /// io-protocol entirely (io.erl is never compiled).
    fn compile_io_bif(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<IntValue<'ctx>> {
        let argv = self.eval_siblings(f, &args.iter().collect::<Vec<_>>(), scope)?;
        match (name, argv.len()) {
            // devices other than stdout are not supported; the device arg
            // (standard_io etc.) is evaluated and ignored
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
                // format/3's device arg (first) is ignored like put_chars/2's
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

    fn compile_maps_bif(
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
                // miss (or non-map) yields the default — TODO(badmap): a
                // non-map should raise
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
                // {ok, V}: alloc, so root v in a temp slot first
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
                // update(K, V, M): key must exist (badkey otherwise)
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
                // fold(Fun, Acc, Map)
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

    fn map_size_of(
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

    fn compile_raise(
        &self,
        f: FunctionValue<'ctx>,
        name: &str,
        args: &[Expr],
        scope: &mut Scope<'ctx>,
    ) -> CgResult<()> {
        let was = self.eternal_alloc.replace(true);
        let result: CgResult<(IntValue<'ctx>, IntValue<'ctx>)> = (|| {
            let (class, reason) = match name {
                // primop raise(Stk, Reason): re-raise. The "stacktrace" slot
                // carries the class atom (TODO(stacktraces)).
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
                // match_fail / error / anything else: class error.
                // BEAM reports function_clause as a bare atom (the args go
                // into the stacktrace, which we don't build yet).
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

    // ---- helpers ----

    fn local_fn(&self, fname: &FunName) -> CgResult<FunctionValue<'ctx>> {
        self.fns
            .borrow()
            .get(fname)
            .copied()
            .ok_or_else(|| format!("undefined local function {}/{}", fname.name, fname.arity))
    }

    fn remote_fn(&self, module: &str, name: &str, arity: usize) -> FunctionValue<'ctx> {
        let sym = mangle(
            module,
            &FunName {
                name: name.to_string(),
                arity,
            },
        );
        self.module.get_function(&sym).unwrap_or_else(|| {
            self.module
                .add_function(&sym, self.term_fn_type(arity), None)
        })
    }

    fn tag_of(&self, val: IntValue<'ctx>) -> CgResult<IntValue<'ctx>> {
        self.builder
            .build_and(val, self.i64t.const_int(TAG_MASK, false), "tag")
            .map_err(be)
    }

    fn untag_int(&self, val: IntValue<'ctx>) -> CgResult<IntValue<'ctx>> {
        self.builder
            .build_right_shift(val, self.i64t.const_int(3, false), true, "untag")
            .map_err(be)
    }

    fn retag_int(&self, val: IntValue<'ctx>) -> CgResult<IntValue<'ctx>> {
        let shifted = self
            .builder
            .build_left_shift(val, self.i64t.const_int(3, false), "shl")
            .map_err(be)?;
        self.builder
            .build_or(shifted, self.i64t.const_int(TAG_SMALL, false), "retag")
            .map_err(be)
    }

    /// Inline nursery bump allocation: load top/end from ctx words 0/1,
    /// bump on the fast path, call `mana_rt_alloc_slow` (collect) on
    /// overflow. Remains a GC point via the slow path.
    fn alloc_words(&self, n: u64) -> CgResult<PointerValue<'ctx>> {
        self.alloc_words_kind(n, false)
    }

    fn alloc_words_kind(&self, n: u64, is_cons: bool) -> CgResult<PointerValue<'ctx>> {
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
        let phi = self.builder.build_phi(self.i64t, "alloc.addr").map_err(be)?;
        phi.add_incoming(&[(&top, fast), (&slow_addr, slow_bb)]);
        self.builder
            .build_int_to_ptr(phi.as_basic_value().into_int_value(), self.ptrt, "alloc")
            .map_err(be)
    }

    fn tbaa_tag(&self, kind: MemKind) -> inkwell::values::MetadataValue<'ctx> {
        match kind {
            MemKind::Ctx => self.tbaa_ctx,
            MemKind::Frame => self.tbaa_frame,
            MemKind::Heap => self.tbaa_heap,
        }
    }

    fn mem_store(
        &self,
        p: PointerValue<'ctx>,
        index: u64,
        v: IntValue<'ctx>,
        kind: MemKind,
    ) -> CgResult<()> {
        let slot = unsafe {
            self.builder
                .build_in_bounds_gep(
                    self.i64t,
                    p,
                    &[self.i64t.const_int(index, false)],
                    "slot",
                )
                .map_err(be)?
        };
        let inst = self.builder.build_store(slot, v).map_err(be)?;
        let _ = inst.set_metadata(self.tbaa_tag(kind), self.tbaa_kind);
        Ok(())
    }

    fn mem_load(
        &self,
        p: PointerValue<'ctx>,
        index: u64,
        kind: MemKind,
    ) -> CgResult<IntValue<'ctx>> {
        let slot = unsafe {
            self.builder
                .build_in_bounds_gep(
                    self.i64t,
                    p,
                    &[self.i64t.const_int(index, false)],
                    "slot",
                )
                .map_err(be)?
        };
        let v = self.builder.build_load(self.i64t, slot, "word").map_err(be)?;
        if let Some(inst) = v.as_instruction_value() {
            let _ = inst.set_metadata(self.tbaa_tag(kind), self.tbaa_kind);
        }
        Ok(v.into_int_value())
    }

    /// Heap-object word access (the overwhelmingly common case).
    fn store_word(
        &self,
        p: PointerValue<'ctx>,
        index: u64,
        v: IntValue<'ctx>,
    ) -> CgResult<()> {
        self.mem_store(p, index, v, MemKind::Heap)
    }

    fn load_word(&self, p: PointerValue<'ctx>, index: u64) -> CgResult<IntValue<'ctx>> {
        self.mem_load(p, index, MemKind::Heap)
    }

    // ---- output ----

    /// Closed-world atom table: one pointer per atom static in the
    /// `mana_atoms` ELF section (linkonce_odr → linker-deduped program-wide,
    /// like the atoms themselves). Pinned via llvm.used so O2 can't discard
    /// the otherwise-unreferenced globals. The runtime walks
    /// __start_mana_atoms..__stop_mana_atoms for binary_to_atom.
    fn emit_atom_table(&self) {
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
        for (fname, code) in self.exports.borrow().iter() {
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
                    code.as_global_value().as_pointer_value().into(),
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

    fn emit_object(&self, out: &Path) -> CgResult<()> {
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

/// A child value of an allocation: rooted in a frame slot, or (raise-path /
/// frameless) held in SSA.
enum Rooted<'ctx> {
    Slot(u64),
    Val(IntValue<'ctx>),
}

enum CaseVals<'ctx> {
    Ssa(Vec<IntValue<'ctx>>),
    Slots(Vec<u64>),
}

/// A parsed bitstring segment spec `(size, unit, type, flags)`. Byte-aligned
/// subset only; sub-byte sizes are TODO(bitstring).
struct SegSpec {
    little: bool,
    signed: bool,
    kind: SegKind,
}

enum SegKind {
    Int { size: SegSize },
    Bin { size: SegSize },
    Utf8,
}

/// Size in BYTES: constant, 'all' (binary rest), or computed at runtime
/// (`expr * unit` bits; the byte-alignment check happens at runtime).
enum SegSize {
    Bytes(u64),
    /// constant bit count that is NOT a byte multiple (nibble reads in
    /// Code.Identifier.escape etc.) — patterns only, static prefix only
    Bits(u64),
    All,
    Dyn { size: Expr, unit: i64 },
}

impl SegKind {
    fn allocates(&self) -> bool {
        matches!(self, SegKind::Bin { .. })
    }
    fn dynamic(&self) -> bool {
        matches!(
            self,
            SegKind::Utf8
                | SegKind::Int { size: SegSize::Dyn { .. } }
                | SegKind::Bin { size: SegSize::Dyn { .. } | SegSize::All }
        )
    }
}

/// Erlang term order for the literal keys the presorted-map-literal path
/// accepts: numbers < atoms < nil (nil is the empty list, which sorts after
/// maps). Atoms compare by name bytes — same as the runtime's atom_bytes
/// memcmp in mana_rt_compare.
fn lit_key_ord(a: &Literal, b: &Literal) -> std::cmp::Ordering {
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

fn atom_list(e: &Expr, out: &mut Vec<String>) {
    match e {
        Expr::Lit(Literal::Atom(a)) => out.push(a.clone()),
        Expr::Cons(h, t) => {
            atom_list(h, out);
            atom_list(t, out);
        }
        _ => {}
    }
}

fn parse_seg_spec(spec: &[Expr]) -> Result<SegSpec, String> {
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

/// Does matching this pattern allocate? (binary patterns with binary-type
/// segments build sub-binaries)
fn pattern_may_gc(p: &Pattern) -> bool {
    match p {
        Pattern::Binary(segs) => segs
            .iter()
            .any(|s| matches!(parse_seg_spec(&s.spec), Ok(sp) if sp.kind.allocates())),
        Pattern::Alias(_, inner) => pattern_may_gc(inner),
        Pattern::Tuple(ps) => ps.iter().any(pattern_may_gc),
        Pattern::Cons(h, t) => pattern_may_gc(h) || pattern_may_gc(t),
        Pattern::Map(pairs) => pairs.iter().any(|(_, sub)| pattern_may_gc(sub)),
        _ => false,
    }
}

/// Decimal digits → big-endian bytes, truncated (mod 2^(8n)) or left-padded
/// to exactly `nbytes` — BEAM's truncating construction semantics.
fn big_to_bytes(dec: &str, nbytes: usize, little: bool) -> Result<Vec<u8>, String> {
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
fn seg_const_bytes(value: &Expr, nbytes: u64, little: bool) -> Result<Option<Vec<u8>>, String> {
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
fn binary_all_const(segs: &[mana_syntax::BinSegment<Box<Expr>>]) -> bool {
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

/// Frame slots the match compiler will spill for this pattern (subjects
/// parked across allocating sub-matches; see pattern_subject_slot).
fn pattern_spill_sites(p: &Pattern) -> usize {
    let own = pattern_may_gc(p) as usize;
    own + match p {
        Pattern::Alias(_, inner) => pattern_spill_sites(inner),
        Pattern::Tuple(ps) => ps.iter().map(pattern_spill_sites).sum(),
        Pattern::Cons(h, t) => pattern_spill_sites(h) + pattern_spill_sites(t),
        Pattern::Map(pairs) => pairs.iter().map(|(_, s)| pattern_spill_sites(s)).sum(),
        _ => 0,
    }
}

/// Modules implemented natively (never compiled from beams).
/// Modules implemented natively by the runtime — never compiled from beams,
/// never chased as dependencies. The mix driver reads this list via
/// `manac --print-bif-modules` (single source of truth for its closure BFS).
pub const BIF_MODULES: &[&str] = &[
    "erlang", "maps", "io", "unicode", "persistent_term", "code", "io_lib",
    "logger", "ets", "application", "file", "math", "re", "timer",
    "gen_tcp", "inet", "crypto",
    "erts_internal", "zlib",
    "elixir_erl", "erl_eval", "beam_lib", "global", "global_group",
    "net_kernel",
];

fn is_bif_module(m: &str) -> bool {
    BIF_MODULES.contains(&m)
}

fn is_raise(primop: &str) -> bool {
    matches!(
        primop,
        "match_fail" | "raise" | "raw_raise" | "error" | "exit" | "throw"
    )
}

/// erlang-module BIFs that may raise (shared by the boolean walker and the
/// condenser — one list, no divergence).
fn erlang_may_raise(name: &str, arity: usize) -> bool {
    matches!(
        (name, arity),
        ("error", 1)
            | ("error", 2)
            | ("error", 3)
            | ("exit", 1)
            | ("throw", 1)
            | ("+", 2)
            | ("-", 2)
            | ("*", 2)
            | ("/", 2)
            | ("div", 2)
            | ("rem", 2)
            | ("band", 2)
            | ("bor", 2)
            | ("bxor", 2)
            | ("bsl", 2)
            | ("bsr", 2)
            | ("bnot", 1)
            | ("get_module_info", 2)
            | ("decode_packet", 3)
            | ("process_flag", 2)
            | ("hibernate", 3)
            | ("iolist_size", 1)
            | ("term_to_binary", 1)
            | ("term_to_binary", 2)
            | ("binary_to_term", 1)
            | ("binary_to_term", 2)
            | ("+", 1)
            | ("-", 1)
            | ("float", 1)
            | ("trunc", 1)
            | ("round", 1)
            | ("floor", 1)
            | ("ceil", 1)
            | ("float_to_binary", 1)
            | ("float_to_binary", 2)
            | ("float_to_list", 1)
            | ("float_to_list", 2)
            | ("binary_to_float", 1)
            | ("list_to_float", 1)
            | ("spawn", 1)
            | ("spawn", 3)
            | ("spawn_link", 1)
            | ("spawn_link", 3)
            | ("spawn_opt", 2)
            | ("spawn_opt", 4)
            | ("spawn_monitor", 1)
            | ("make_fun", 3)
            | ("monitor", 3)
            | ("system_info", 1)
            | ("is_process_alive", 1)
            | ("fun_info", 2)
            | ("fun_info_mfa", 1)
            | ("send_after", 3)
            | ("start_timer", 3)
            | ("cancel_timer", 1)
            | ("cancel_timer", 2)
            | ("monotonic_time", 0)
            | ("monotonic_time", 1)
            | ("system_time", 0)
            | ("system_time", 1)
            | ("convert_time_unit", 3)
            | ("register", 2)
            | ("whereis", 1)
            | ("unregister", 1)
            | ("process_info", 2)
            | ("element", 2)
            | ("setelement", 3)
            | ("tuple_size", 1)
            | ("hd", 1)
            | ("tl", 1)
            | ("length", 1)
            | ("++", 2)
            | ("--", 2)
            | ("abs", 1)
            | ("map_size", 1)
            | ("map_get", 2)
            | ("is_map_key", 2)
            | ("byte_size", 1)
            | ("bit_size", 1)
            | ("binary_part", 3)
            | ("split_binary", 2)
            | ("list_to_tuple", 1)
            | ("tuple_to_list", 1)
            | ("binary_to_list", 1)
            | ("list_to_binary", 1)
            | ("iolist_to_binary", 1)
            | ("integer_to_binary", 1)
            | ("integer_to_binary", 2)
            | ("integer_to_list", 1)
            | ("integer_to_list", 2)
            | ("binary_to_integer", 1)
            | ("binary_to_integer", 2)
            | ("list_to_integer", 1)
            | ("list_to_integer", 2)
            | ("atom_to_binary", 1)
            | ("atom_to_binary", 2)
            | ("atom_to_list", 1)
            | ("list_to_atom", 1)
            | ("list_to_existing_atom", 1)
            | ("binary_to_atom", 1)
            | ("binary_to_atom", 2)
            | ("binary_to_existing_atom", 1)
            | ("binary_to_existing_atom", 2)
            | ("apply", 2)
            | ("apply", 3)
            | ("raise", 3)
            | ("nif_error", 1)
            | ("nif_error", 2)
    )
}

/// Allocating erlang BIFs — GC points (shared list, like erlang_may_raise).
fn erlang_may_gc(name: &str, arity: usize) -> bool {
    matches!(
        (name, arity),
        ("setelement", 3)
            | ("decode_packet", 3)
            | ("hibernate", 3)
            | ("get_keys", 0)
            | ("term_to_binary", 1)
            | ("term_to_binary", 2)
            | ("binary_to_term", 1)
            | ("binary_to_term", 2)
            | ("++", 2)
            | ("--", 2)
            | ("binary_part", 3)
            | ("split_binary", 2)
            | ("list_to_tuple", 1)
            | ("tuple_to_list", 1)
            | ("binary_to_list", 1)
            | ("list_to_binary", 1)
            | ("iolist_to_binary", 1)
            | ("integer_to_binary", 1)
            | ("atom_to_binary", 1)
            | ("atom_to_binary", 2)
            | ("atom_to_list", 1)
            | ("float_to_binary", 1)
            | ("float_to_binary", 2)
            | ("float_to_list", 1)
            | ("float_to_list", 2)
            | ("apply", 2)
            | ("apply", 3)
            | ("raise", 3)
            | ("nif_error", 1)
            | ("nif_error", 2)
    )
}

// ---- GC-effect analysis ----

/// Fixpoint: which reachable functions may trigger a collection.
/// Each function's body is condensed ONCE into (base, deps) — both effect
/// traversals are pure monotone ORs over set-membership lookups, so
/// `base || deps ∩ set != ∅` is exact — then a worklist fixpoint runs over
/// the condensed graph. MANA_CHECK_ANALYSIS=1 cross-checks against the
/// original per-iteration walkers.
fn compute_may_gc(mods: &[Module], reachable: &HashSet<(String, FunName)>) -> GcSet {
    let defs: HashMap<(&str, &FunName), &Fun> = mods
        .iter()
        .flat_map(|m| m.definitions.iter().map(move |(f, b)| ((m.name.as_str(), f), b)))
        .collect();
    let conds: HashMap<(String, FunName), (bool, BTreeSet<(String, FunName)>)> = reachable
        .iter()
        .filter_map(|(m, f)| {
            let fun = defs.get(&(m.as_str(), f))?;
            let mut base = false;
            let mut deps = BTreeSet::new();
            let mut letrec = HashSet::new();
            cond_may_gc(&fun.body, m, &mut letrec, &mut base, &mut deps);
            Some(((m.clone(), f.clone()), (base, deps)))
        })
        .collect();
    let set = effect_fixpoint(conds);
    if std::env::var_os("MANA_CHECK_ANALYSIS").is_some() {
        let slow = compute_may_gc_slow(mods, reachable);
        check_analysis_equal("may_gc", &set, &slow);
    }
    set
}

/// Fixpoint: which reachable functions may raise an exception.
fn compute_may_raise(mods: &[Module], reachable: &HashSet<(String, FunName)>) -> GcSet {
    let defs: HashMap<(&str, &FunName), &Fun> = mods
        .iter()
        .flat_map(|m| m.definitions.iter().map(move |(f, b)| ((m.name.as_str(), f), b)))
        .collect();
    let conds: HashMap<(String, FunName), (bool, BTreeSet<(String, FunName)>)> = reachable
        .iter()
        .filter_map(|(m, f)| {
            let fun = defs.get(&(m.as_str(), f))?;
            let mut base = false;
            let mut deps = BTreeSet::new();
            let mut letrec = HashSet::new();
            cond_may_raise(&fun.body, m, &mut letrec, &mut base, &mut deps);
            Some(((m.clone(), f.clone()), (base, deps)))
        })
        .collect();
    let set = effect_fixpoint(conds);
    if std::env::var_os("MANA_CHECK_ANALYSIS").is_some() {
        let slow = compute_may_raise_slow(mods, reachable);
        check_analysis_equal("may_raise", &set, &slow);
    }
    set
}

/// Least fixpoint of `f ∈ set ⇔ base(f) || deps(f) ∩ set ≠ ∅` via reverse
/// edges: when a function turns true, only its dependents get revisited.
fn effect_fixpoint(
    conds: HashMap<(String, FunName), (bool, BTreeSet<(String, FunName)>)>,
) -> GcSet {
    let mut rdeps: HashMap<(String, FunName), Vec<(String, FunName)>> = HashMap::new();
    let mut set: GcSet = GcSet::new();
    let mut queue: Vec<(String, FunName)> = Vec::new();
    for (k, (base, deps)) in &conds {
        if *base {
            set.insert(k.clone());
            queue.push(k.clone());
        } else {
            for d in deps {
                rdeps.entry(d.clone()).or_default().push(k.clone());
            }
        }
    }
    while let Some(k) = queue.pop() {
        let Some(dependents) = rdeps.get(&k) else {
            continue;
        };
        for d in dependents {
            if !set.contains(d) {
                set.insert(d.clone());
                queue.push(d.clone());
            }
        }
    }
    set
}

fn check_analysis_equal(what: &str, fast: &GcSet, slow: &GcSet) {
    if fast != slow {
        for k in fast.symmetric_difference(slow) {
            eprintln!(
                "manac: {} MISMATCH {}:{}/{} fast={} slow={}",
                what,
                k.0,
                k.1.name,
                k.1.arity,
                fast.contains(k),
                slow.contains(k)
            );
        }
        panic!("manac: {} condensed fixpoint diverges from reference", what);
    }
}

fn compute_may_gc_slow(mods: &[Module], reachable: &HashSet<(String, FunName)>) -> GcSet {
    let defs: HashMap<(&str, &FunName), &Fun> = mods
        .iter()
        .flat_map(|m| m.definitions.iter().map(move |(f, b)| ((m.name.as_str(), f), b)))
        .collect();
    let mut set: GcSet = GcSet::new();
    loop {
        let mut changed = false;
        for (m, f) in reachable {
            if set.contains(&(m.clone(), f.clone())) {
                continue;
            }
            let Some(fun) = defs.get(&(m.as_str(), f)) else {
                continue;
            };
            let mut letrec = HashSet::new();
            if expr_may_gc(&fun.body, m, &set, &mut letrec) {
                set.insert((m.clone(), f.clone()));
                changed = true;
            }
        }
        if !changed {
            return set;
        }
    }
}

fn compute_may_raise_slow(mods: &[Module], reachable: &HashSet<(String, FunName)>) -> GcSet {
    let defs: HashMap<(&str, &FunName), &Fun> = mods
        .iter()
        .flat_map(|m| m.definitions.iter().map(move |(f, b)| ((m.name.as_str(), f), b)))
        .collect();
    let mut set: GcSet = GcSet::new();
    loop {
        let mut changed = false;
        for (m, f) in reachable {
            if set.contains(&(m.clone(), f.clone())) {
                continue;
            }
            let Some(fun) = defs.get(&(m.as_str(), f)) else {
                continue;
            };
            let mut letrec = HashSet::new();
            if expr_may_raise(&fun.body, m, &set, &mut letrec) {
                set.insert((m.clone(), f.clone()));
                changed = true;
            }
        }
        if !changed {
            return set;
        }
    }
}

fn clause_irrefutable(c: &Clause) -> bool {
    is_true_atom(&c.guard) && c.patterns.iter().all(|p| matches!(p, Pattern::Var(_)))
}

/// Can evaluating `e` raise? Sources: raising primops/BIFs, fun-value
/// applies (badfun), refutable cases (case_clause/function_clause), and
/// calls to may-raise functions. Raises inside a `try` argument are caught.
fn expr_may_raise(
    e: &Expr,
    cur_mod: &str,
    raise_set: &GcSet,
    letrec_bound: &mut HashSet<FunName>,
) -> bool {
    match e {
        Expr::Var(_) | Expr::Lit(_) | Expr::FunRef { .. } | Expr::Fun(_) => false,
        Expr::Tuple(items) | Expr::Values(items) => items
            .iter()
            .any(|i| expr_may_raise(i, cur_mod, raise_set, letrec_bound)),
        Expr::Cons(h, t) => {
            expr_may_raise(h, cur_mod, raise_set, letrec_bound)
                || expr_may_raise(t, cur_mod, raise_set, letrec_bound)
        }
        Expr::Let { arg, body, .. } => {
            expr_may_raise(arg, cur_mod, raise_set, letrec_bound)
                || expr_may_raise(body, cur_mod, raise_set, letrec_bound)
        }
        Expr::Do(a, b) => {
            expr_may_raise(a, cur_mod, raise_set, letrec_bound)
                || expr_may_raise(b, cur_mod, raise_set, letrec_bound)
        }
        Expr::LetRec { defs, body } => {
            let added: Vec<FunName> = defs
                .iter()
                .map(|(f, _)| f.clone())
                .filter(|f| letrec_bound.insert(f.clone()))
                .collect();
            let r = expr_may_raise(body, cur_mod, raise_set, letrec_bound);
            for f in added {
                letrec_bound.remove(&f);
            }
            r
        }
        Expr::Apply { target, args } => {
            let target_raises = match target {
                ApplyTarget::Var(_) => true, // badfun/badarity
                ApplyTarget::LocalFun(f) => {
                    letrec_bound.contains(f)
                        || raise_set.contains(&(cur_mod.to_string(), f.clone()))
                }
            };
            target_raises
                || args
                    .iter()
                    .any(|a| expr_may_raise(a, cur_mod, raise_set, letrec_bound))
        }
        Expr::Call { module, name, args } => {
            if matches!(
                module.as_str(),
                "maps" | "io" | "unicode" | "persistent_term" | "code" | "io_lib"
                    | "logger" | "ets" | "application" | "file" | "erts_internal"
                    | "elixir_erl" | "erl_eval" | "beam_lib" | "global" | "global_group"
                    | "net_kernel" | "math" | "re" | "timer" | "gen_tcp" | "inet"
                    | "zlib" | "crypto"
            ) {
                return true;
            }
            let callee = if module == "erlang" {
                erlang_may_raise(name, args.len())
            } else {
                raise_set.contains(&(
                    module.clone(),
                    FunName {
                        name: name.clone(),
                        arity: args.len(),
                    },
                ))
            };
            callee
                || args
                    .iter()
                    .any(|a| expr_may_raise(a, cur_mod, raise_set, letrec_bound))
        }
        Expr::CallDyn { .. } => true,
        Expr::PrimOp { name, .. } if is_raise(name) => true,
        Expr::PrimOp { args, .. } => args
            .iter()
            .any(|a| expr_may_raise(a, cur_mod, raise_set, letrec_bound)),
        Expr::Case { arg, clauses } => {
            let refutable = clauses.last().map_or(true, |c| !clause_irrefutable(c));
            refutable
                || expr_may_raise(arg, cur_mod, raise_set, letrec_bound)
                || clauses.iter().any(|c| {
                    expr_may_raise(&c.guard, cur_mod, raise_set, letrec_bound)
                        || expr_may_raise(&c.body, cur_mod, raise_set, letrec_bound)
                })
        }
        // raises inside the protected argument are caught by this try
        Expr::Try { body, handler, .. } => {
            expr_may_raise(body, cur_mod, raise_set, letrec_bound)
                || expr_may_raise(handler, cur_mod, raise_set, letrec_bound)
        }
        // construction raises badarg on non-int values / non-binary splices;
        // fully-constant literals compile to static terms (no raise)
        Expr::Binary(segs) => !binary_all_const(segs),
        // updates raise badmap/badkey; construction only via children
        Expr::Map { pairs, update } => {
            update.is_some()
                || pairs.iter().any(|(k, _, v)| {
                    expr_may_raise(k, cur_mod, raise_set, letrec_bound)
                        || expr_may_raise(v, cur_mod, raise_set, letrec_bound)
                })
        }
    }
}

/// Does evaluating `e` contain a GC point? Allocation sites are GC points;
/// calls consult the (possibly still-growing) fixpoint set; letrec-bound
/// applies and fun-value applies are conservatively GC points.
fn expr_may_gc(
    e: &Expr,
    cur_mod: &str,
    gc_set: &GcSet,
    letrec_bound: &mut HashSet<FunName>,
) -> bool {
    match e {
        Expr::Var(_) => false,
        Expr::Lit(Literal::Float(_)) => true, // boxed
        Expr::Lit(_) => false,
        // allocation sites (CallDyn builds its args list + callee unknown)
        Expr::Tuple(_) | Expr::Cons(..)
        | Expr::LetRec { .. } | Expr::Map { .. }
        | Expr::CallDyn { .. } => true,
        // captureless funs are static constants — no allocation
        Expr::FunRef { .. } => false,
        Expr::Fun(fun) => {
            let mut bound: HashSet<String> = fun.params.iter().cloned().collect();
            let mut out = BTreeSet::new();
            free_vars(&fun.body, &mut bound, &mut out);
            !out.is_empty()
        }
        // fully-constant binaries are static terms — no allocation
        Expr::Binary(segs) => !binary_all_const(segs),
        Expr::Apply { target, args } => {
            let target_gc = match target {
                ApplyTarget::Var(_) => true,
                ApplyTarget::LocalFun(f) => {
                    letrec_bound.contains(f)
                        || gc_set.contains(&(cur_mod.to_string(), f.clone()))
                }
            };
            target_gc
                || args
                    .iter()
                    .any(|a| expr_may_gc(a, cur_mod, gc_set, letrec_bound))
        }
        Expr::Call { module, name, args } => {
            if module == "erlang"
                && matches!(
                    (name.as_str(), args.len()),
                    ("error", 1) | ("error", 2) | ("error", 3) | ("exit", 1) | ("throw", 1)
                )
            {
                return args
                    .iter()
                    .any(|a| raise_arg_may_gc(a, cur_mod, gc_set, letrec_bound));
            }
            // allocating erlang BIFs are GC points
            if module == "erlang" && erlang_may_gc(name, args.len()) {
                return true;
            }
            if module == "maps"
                && matches!(
                    name.as_str(),
                    "put" | "remove" | "merge" | "from_list" | "to_list" | "find"
                        | "fold" | "keys" | "values" | "iterator" | "next"
                        | "merge_with" | "take" | "update" | "update_with"
                        | "foreach" | "with" | "without"
                )
            {
                return true;
            }
            // io:nl allocates its newline binary; unicode/re allocate results;
            // file/gen_tcp/inet allocate result tuples and may suspend
            if matches!(
                module.as_str(),
                "io" | "unicode" | "re" | "timer" | "file" | "gen_tcp" | "inet"
                    | "crypto"
            ) {
                return true;
            }
            let callee_gc = module != "erlang"
                && gc_set.contains(&(
                    module.clone(),
                    FunName {
                        name: name.clone(),
                        arity: args.len(),
                    },
                ));
            callee_gc
                || args
                    .iter()
                    .any(|a| expr_may_gc(a, cur_mod, gc_set, letrec_bound))
        }
        Expr::PrimOp { name, args } if is_raise(name) => args
            .iter()
            .any(|a| raise_arg_may_gc(a, cur_mod, gc_set, letrec_bound)),
        // recv_wait_timeout suspends the process — other processes run and
        // may collect the shared heap, so it is a GC point
        Expr::PrimOp { name, .. } if name == "recv_wait_timeout" => true,
        Expr::PrimOp { args, .. } => args
            .iter()
            .any(|a| expr_may_gc(a, cur_mod, gc_set, letrec_bound)),
        Expr::Let { arg, body, .. } => {
            expr_may_gc(arg, cur_mod, gc_set, letrec_bound)
                || expr_may_gc(body, cur_mod, gc_set, letrec_bound)
        }
        Expr::Do(a, b) => {
            expr_may_gc(a, cur_mod, gc_set, letrec_bound)
                || expr_may_gc(b, cur_mod, gc_set, letrec_bound)
        }
        Expr::Try {
            arg, body, handler, ..
        } => {
            expr_may_gc(arg, cur_mod, gc_set, letrec_bound)
                || expr_may_gc(body, cur_mod, gc_set, letrec_bound)
                || expr_may_gc(handler, cur_mod, gc_set, letrec_bound)
        }
        Expr::Case { arg, clauses } => {
            expr_may_gc(arg, cur_mod, gc_set, letrec_bound)
                || clauses
                    .iter()
                    .any(|c| c.patterns.iter().any(pattern_may_gc))
                || clauses.iter().any(|c| {
                    expr_may_gc(&c.guard, cur_mod, gc_set, letrec_bound)
                        || expr_may_gc(&c.body, cur_mod, gc_set, letrec_bound)
                })
        }
        Expr::Values(items) => items
            .iter()
            .any(|i| expr_may_gc(i, cur_mod, gc_set, letrec_bound)),
    }
}

/// GC-point analysis for raise arguments: the reason term is built with the
/// eternal allocator (no GC), so allocation nodes don't count — only calls
/// into compiled code do.
fn raise_arg_may_gc(
    e: &Expr,
    cur_mod: &str,
    gc_set: &GcSet,
    letrec_bound: &mut HashSet<FunName>,
) -> bool {
    match e {
        Expr::Var(_) | Expr::Lit(_) | Expr::FunRef { .. } | Expr::Fun(_) => false,
        Expr::Tuple(items) | Expr::Values(items) => items
            .iter()
            .any(|i| raise_arg_may_gc(i, cur_mod, gc_set, letrec_bound)),
        Expr::Cons(h, t) => {
            raise_arg_may_gc(h, cur_mod, gc_set, letrec_bound)
                || raise_arg_may_gc(t, cur_mod, gc_set, letrec_bound)
        }
        // anything with control flow or calls: fall back to the full analysis
        other => expr_may_gc(other, cur_mod, gc_set, letrec_bound),
    }
}

// ---- effect condensers ----
//
// Arm-for-arm mirrors of expr_may_raise / expr_may_gc / raise_arg_may_gc:
// every `set.contains(k)` becomes `deps.insert(k)` (Local resolved against
// cur_mod), every unconditional `true` sets `base`, and early returns that
// skip child scans are mirrored as returns. The walkers' short-circuiting
// doesn't change the OR's value, so `base || deps ∩ set` is exact.

/// Mirror of expr_may_raise.
fn cond_may_raise(
    e: &Expr,
    cur_mod: &str,
    letrec_bound: &mut HashSet<FunName>,
    base: &mut bool,
    deps: &mut BTreeSet<(String, FunName)>,
) {
    match e {
        Expr::Var(_) | Expr::Lit(_) | Expr::FunRef { .. } | Expr::Fun(_) => {}
        Expr::Tuple(items) | Expr::Values(items) => items
            .iter()
            .for_each(|i| cond_may_raise(i, cur_mod, letrec_bound, base, deps)),
        Expr::Cons(h, t) => {
            cond_may_raise(h, cur_mod, letrec_bound, base, deps);
            cond_may_raise(t, cur_mod, letrec_bound, base, deps);
        }
        Expr::Let { arg, body, .. } => {
            cond_may_raise(arg, cur_mod, letrec_bound, base, deps);
            cond_may_raise(body, cur_mod, letrec_bound, base, deps);
        }
        Expr::Do(a, b) => {
            cond_may_raise(a, cur_mod, letrec_bound, base, deps);
            cond_may_raise(b, cur_mod, letrec_bound, base, deps);
        }
        Expr::LetRec { defs, body } => {
            let added: Vec<FunName> = defs
                .iter()
                .map(|(f, _)| f.clone())
                .filter(|f| letrec_bound.insert(f.clone()))
                .collect();
            cond_may_raise(body, cur_mod, letrec_bound, base, deps);
            for f in added {
                letrec_bound.remove(&f);
            }
        }
        Expr::Apply { target, args } => {
            match target {
                ApplyTarget::Var(_) => *base = true, // badfun/badarity
                ApplyTarget::LocalFun(f) => {
                    if letrec_bound.contains(f) {
                        *base = true;
                    } else {
                        deps.insert((cur_mod.to_string(), f.clone()));
                    }
                }
            }
            args.iter()
                .for_each(|a| cond_may_raise(a, cur_mod, letrec_bound, base, deps));
        }
        Expr::Call { module, name, args } => {
            if matches!(
                module.as_str(),
                "maps" | "io" | "unicode" | "persistent_term" | "code" | "io_lib"
                    | "logger" | "ets" | "application" | "file" | "erts_internal"
                    | "elixir_erl" | "erl_eval" | "beam_lib" | "global" | "global_group"
                    | "net_kernel" | "math" | "re" | "timer" | "gen_tcp" | "inet"
                    | "zlib" | "crypto"
            ) {
                *base = true;
                return;
            }
            if module == "erlang" {
                if erlang_may_raise(name, args.len()) {
                    *base = true;
                }
            } else {
                deps.insert((
                    module.clone(),
                    FunName {
                        name: name.clone(),
                        arity: args.len(),
                    },
                ));
            }
            args.iter()
                .for_each(|a| cond_may_raise(a, cur_mod, letrec_bound, base, deps));
        }
        Expr::CallDyn { .. } => *base = true,
        Expr::PrimOp { name, .. } if is_raise(name) => *base = true,
        Expr::PrimOp { args, .. } => args
            .iter()
            .for_each(|a| cond_may_raise(a, cur_mod, letrec_bound, base, deps)),
        Expr::Case { arg, clauses } => {
            if clauses.last().map_or(true, |c| !clause_irrefutable(c)) {
                *base = true;
            }
            cond_may_raise(arg, cur_mod, letrec_bound, base, deps);
            for c in clauses {
                cond_may_raise(&c.guard, cur_mod, letrec_bound, base, deps);
                cond_may_raise(&c.body, cur_mod, letrec_bound, base, deps);
            }
        }
        // raises inside the protected argument are caught by this try
        Expr::Try { body, handler, .. } => {
            cond_may_raise(body, cur_mod, letrec_bound, base, deps);
            cond_may_raise(handler, cur_mod, letrec_bound, base, deps);
        }
        Expr::Binary(segs) => {
            if !binary_all_const(segs) {
                *base = true;
            }
        }
        Expr::Map { pairs, update } => {
            if update.is_some() {
                *base = true;
            }
            for (k, _, v) in pairs {
                cond_may_raise(k, cur_mod, letrec_bound, base, deps);
                cond_may_raise(v, cur_mod, letrec_bound, base, deps);
            }
        }
    }
}

/// Mirror of expr_may_gc.
fn cond_may_gc(
    e: &Expr,
    cur_mod: &str,
    letrec_bound: &mut HashSet<FunName>,
    base: &mut bool,
    deps: &mut BTreeSet<(String, FunName)>,
) {
    match e {
        Expr::Var(_) => {}
        Expr::Lit(Literal::Float(_)) => *base = true, // boxed
        Expr::Lit(_) => {}
        // allocation sites (CallDyn builds its args list + callee unknown)
        Expr::Tuple(_) | Expr::Cons(..)
        | Expr::LetRec { .. } | Expr::Map { .. }
        | Expr::CallDyn { .. } => *base = true,
        // captureless funs are static constants — no allocation
        Expr::FunRef { .. } => {}
        Expr::Fun(fun) => {
            let mut bound: HashSet<String> = fun.params.iter().cloned().collect();
            let mut out = BTreeSet::new();
            free_vars(&fun.body, &mut bound, &mut out);
            if !out.is_empty() {
                *base = true;
            }
        }
        // fully-constant binaries are static terms — no allocation
        Expr::Binary(segs) => {
            if !binary_all_const(segs) {
                *base = true;
            }
        }
        Expr::Apply { target, args } => {
            match target {
                ApplyTarget::Var(_) => *base = true,
                ApplyTarget::LocalFun(f) => {
                    if letrec_bound.contains(f) {
                        *base = true;
                    } else {
                        deps.insert((cur_mod.to_string(), f.clone()));
                    }
                }
            }
            args.iter()
                .for_each(|a| cond_may_gc(a, cur_mod, letrec_bound, base, deps));
        }
        Expr::Call { module, name, args } => {
            if module == "erlang"
                && matches!(
                    (name.as_str(), args.len()),
                    ("error", 1) | ("error", 2) | ("error", 3) | ("exit", 1) | ("throw", 1)
                )
            {
                args.iter()
                    .for_each(|a| cond_raise_arg_may_gc(a, cur_mod, letrec_bound, base, deps));
                return;
            }
            if module == "erlang" && erlang_may_gc(name, args.len()) {
                *base = true;
                return;
            }
            if module == "maps"
                && matches!(
                    name.as_str(),
                    "put" | "remove" | "merge" | "from_list" | "to_list" | "find"
                        | "fold" | "keys" | "values" | "iterator" | "next"
                        | "merge_with" | "take" | "update" | "update_with"
                        | "foreach" | "with" | "without"
                )
            {
                *base = true;
                return;
            }
            // io:nl allocates its newline binary; unicode/re allocate results;
            // file/gen_tcp/inet allocate result tuples and may suspend
            if matches!(
                module.as_str(),
                "io" | "unicode" | "re" | "timer" | "file" | "gen_tcp" | "inet"
                    | "crypto"
            ) {
                *base = true;
                return;
            }
            if module != "erlang" {
                deps.insert((
                    module.clone(),
                    FunName {
                        name: name.clone(),
                        arity: args.len(),
                    },
                ));
            }
            args.iter()
                .for_each(|a| cond_may_gc(a, cur_mod, letrec_bound, base, deps));
        }
        Expr::PrimOp { name, args } if is_raise(name) => args
            .iter()
            .for_each(|a| cond_raise_arg_may_gc(a, cur_mod, letrec_bound, base, deps)),
        // recv_wait_timeout suspends the process — other processes run and
        // may collect the shared heap, so it is a GC point
        Expr::PrimOp { name, .. } if name == "recv_wait_timeout" => *base = true,
        Expr::PrimOp { args, .. } => args
            .iter()
            .for_each(|a| cond_may_gc(a, cur_mod, letrec_bound, base, deps)),
        Expr::Let { arg, body, .. } => {
            cond_may_gc(arg, cur_mod, letrec_bound, base, deps);
            cond_may_gc(body, cur_mod, letrec_bound, base, deps);
        }
        Expr::Do(a, b) => {
            cond_may_gc(a, cur_mod, letrec_bound, base, deps);
            cond_may_gc(b, cur_mod, letrec_bound, base, deps);
        }
        Expr::Try {
            arg, body, handler, ..
        } => {
            cond_may_gc(arg, cur_mod, letrec_bound, base, deps);
            cond_may_gc(body, cur_mod, letrec_bound, base, deps);
            cond_may_gc(handler, cur_mod, letrec_bound, base, deps);
        }
        Expr::Case { arg, clauses } => {
            cond_may_gc(arg, cur_mod, letrec_bound, base, deps);
            if clauses
                .iter()
                .any(|c| c.patterns.iter().any(pattern_may_gc))
            {
                *base = true;
            }
            for c in clauses {
                cond_may_gc(&c.guard, cur_mod, letrec_bound, base, deps);
                cond_may_gc(&c.body, cur_mod, letrec_bound, base, deps);
            }
        }
        Expr::Values(items) => items
            .iter()
            .for_each(|i| cond_may_gc(i, cur_mod, letrec_bound, base, deps)),
    }
}

/// Mirror of raise_arg_may_gc.
fn cond_raise_arg_may_gc(
    e: &Expr,
    cur_mod: &str,
    letrec_bound: &mut HashSet<FunName>,
    base: &mut bool,
    deps: &mut BTreeSet<(String, FunName)>,
) {
    match e {
        Expr::Var(_) | Expr::Lit(_) | Expr::FunRef { .. } | Expr::Fun(_) => {}
        Expr::Tuple(items) | Expr::Values(items) => items
            .iter()
            .for_each(|i| cond_raise_arg_may_gc(i, cur_mod, letrec_bound, base, deps)),
        Expr::Cons(h, t) => {
            cond_raise_arg_may_gc(h, cur_mod, letrec_bound, base, deps);
            cond_raise_arg_may_gc(t, cur_mod, letrec_bound, base, deps);
        }
        // anything with control flow or calls: fall back to the full analysis
        other => cond_may_gc(other, cur_mod, letrec_bound, base, deps),
    }
}

/// Count bound variable names and *spill sites* for frame sizing. Spills
/// only happen for children of allocations (eval_all_rooted), call/BIF
/// arguments (eval_siblings), case scrutinees, and letrec closures — the
/// sum over those sites bounds any execution path. Does not descend into
/// Fun/LetRec definition bodies (they get their own frames when lifted).
fn frame_prepass(e: &Expr, vars: &mut BTreeSet<String>, nodes: &mut usize) {
    match e {
        Expr::Var(_) | Expr::Lit(_) | Expr::FunRef { .. } | Expr::Fun(_) => {}
        Expr::Tuple(items) | Expr::Values(items) => {
            *nodes += items.len();
            items.iter().for_each(|i| frame_prepass(i, vars, nodes))
        }
        Expr::Cons(h, t) => {
            *nodes += 2;
            frame_prepass(h, vars, nodes);
            frame_prepass(t, vars, nodes);
        }
        Expr::Let { vars: vs, arg, body } => {
            vars.extend(vs.iter().cloned());
            frame_prepass(arg, vars, nodes);
            frame_prepass(body, vars, nodes);
        }
        Expr::LetRec { body, .. } => {
            *nodes += 1; // shared closure slot
            frame_prepass(body, vars, nodes);
        }
        Expr::Apply { args, .. } => {
            *nodes += args.len();
            args.iter().for_each(|a| frame_prepass(a, vars, nodes))
        }
        Expr::CallDyn { module, name, args } => {
            *nodes += args.len() + 2;
            frame_prepass(module, vars, nodes);
            frame_prepass(name, vars, nodes);
            args.iter().for_each(|a| frame_prepass(a, vars, nodes));
        }
        Expr::Call { args, .. } | Expr::PrimOp { args, .. } => {
            *nodes += args.len();
            args.iter().for_each(|a| frame_prepass(a, vars, nodes))
        }
        Expr::Case { arg, clauses } => {
            *nodes += match arg.as_ref() {
                Expr::Values(es) => es.len(),
                _ => 1,
            };
            frame_prepass(arg, vars, nodes);
            for c in clauses {
                let mut pvars = Vec::new();
                c.patterns.iter().for_each(|p| pattern_vars(p, &mut pvars));
                vars.extend(pvars);
                // allocating (binary) sub-patterns spill their subjects
                c.patterns
                    .iter()
                    .for_each(|p| *nodes += pattern_spill_sites(p));
                frame_prepass(&c.guard, vars, nodes);
                frame_prepass(&c.body, vars, nodes);
            }
        }
        Expr::Try {
            arg,
            vars: vs,
            body,
            evars,
            handler,
        } => {
            vars.extend(vs.iter().cloned());
            vars.extend(evars.iter().cloned());
            frame_prepass(arg, vars, nodes);
            frame_prepass(body, vars, nodes);
            frame_prepass(handler, vars, nodes);
        }
        Expr::Binary(segs) => {
            for s in segs {
                frame_prepass(&s.value, vars, nodes);
                s.spec.iter().for_each(|x| frame_prepass(x, vars, nodes));
            }
        }
        Expr::Map { pairs, update } => {
            for (k, _, v) in pairs {
                frame_prepass(k, vars, nodes);
                frame_prepass(v, vars, nodes);
            }
            if let Some(u) = update {
                frame_prepass(u, vars, nodes);
            }
        }
        Expr::Do(a, b) => {
            frame_prepass(a, vars, nodes);
            frame_prepass(b, vars, nodes);
        }
    }
}

// ---- free variable analysis ----

fn free_vars(e: &Expr, bound: &mut HashSet<String>, out: &mut BTreeSet<String>) {
    match e {
        Expr::Var(v) => {
            if !bound.contains(v) {
                out.insert(v.clone());
            }
        }
        Expr::Lit(_) | Expr::FunRef { .. } => {}
        Expr::Tuple(items) | Expr::Values(items) => {
            items.iter().for_each(|i| free_vars(i, bound, out))
        }
        Expr::Cons(h, t) => {
            free_vars(h, bound, out);
            free_vars(t, bound, out);
        }
        Expr::Fun(f) => {
            let added: Vec<&String> = f
                .params
                .iter()
                .filter(|p| bound.insert((*p).clone()))
                .collect();
            free_vars(&f.body, bound, out);
            for p in added {
                bound.remove(p);
            }
        }
        Expr::Let { vars, arg, body } => {
            free_vars(arg, bound, out);
            let added: Vec<&String> =
                vars.iter().filter(|v| bound.insert((*v).clone())).collect();
            free_vars(body, bound, out);
            for v in added {
                bound.remove(v);
            }
        }
        Expr::LetRec { defs, body } => {
            for (_, f) in defs {
                let added: Vec<&String> = f
                    .params
                    .iter()
                    .filter(|p| bound.insert((*p).clone()))
                    .collect();
                free_vars(&f.body, bound, out);
                for p in added {
                    bound.remove(p);
                }
            }
            free_vars(body, bound, out);
        }
        Expr::Apply { target, args } => {
            if let ApplyTarget::Var(v) = target {
                if !bound.contains(v) {
                    out.insert(v.clone());
                }
            }
            args.iter().for_each(|a| free_vars(a, bound, out));
        }
        Expr::CallDyn { module, name, args } => {
            free_vars(module, bound, out);
            free_vars(name, bound, out);
            args.iter().for_each(|a| free_vars(a, bound, out));
        }
        Expr::Call { args, .. } | Expr::PrimOp { args, .. } => {
            args.iter().for_each(|a| free_vars(a, bound, out))
        }
        Expr::Case { arg, clauses } => {
            free_vars(arg, bound, out);
            for c in clauses {
                let mut pvars = Vec::new();
                c.patterns.iter().for_each(|p| pattern_vars(p, &mut pvars));
                let added: Vec<String> = pvars
                    .into_iter()
                    .filter(|v| bound.insert(v.clone()))
                    .collect();
                free_vars(&c.guard, bound, out);
                free_vars(&c.body, bound, out);
                for v in added {
                    bound.remove(&v);
                }
            }
        }
        Expr::Binary(segs) => {
            for s in segs {
                free_vars(&s.value, bound, out);
                s.spec.iter().for_each(|x| free_vars(x, bound, out));
            }
        }
        Expr::Map { pairs, update } => {
            for (k, _, v) in pairs {
                free_vars(k, bound, out);
                free_vars(v, bound, out);
            }
            if let Some(u) = update {
                free_vars(u, bound, out);
            }
        }
        Expr::Try {
            arg,
            vars,
            body,
            evars,
            handler,
        } => {
            free_vars(arg, bound, out);
            let added: Vec<&String> =
                vars.iter().filter(|v| bound.insert((*v).clone())).collect();
            free_vars(body, bound, out);
            for v in added {
                bound.remove(v);
            }
            let added: Vec<&String> = evars
                .iter()
                .filter(|v| bound.insert((*v).clone()))
                .collect();
            free_vars(handler, bound, out);
            for v in added {
                bound.remove(v);
            }
        }
        Expr::Do(a, b) => {
            free_vars(a, bound, out);
            free_vars(b, bound, out);
        }
    }
}

fn pattern_vars(p: &Pattern, out: &mut Vec<String>) {
    match p {
        Pattern::Var(v) => out.push(v.clone()),
        Pattern::Lit(_) => {}
        Pattern::Alias(v, inner) => {
            out.push(v.clone());
            pattern_vars(inner, out);
        }
        Pattern::Tuple(ps) => ps.iter().for_each(|p| pattern_vars(p, out)),
        Pattern::Cons(h, t) => {
            pattern_vars(h, out);
            pattern_vars(t, out);
        }
        Pattern::Binary(segs) => segs.iter().for_each(|s| pattern_vars(&s.value, out)),
        Pattern::Map(pairs) => pairs.iter().for_each(|(_, p)| pattern_vars(p, out)),
    }
}

// ---- reachability ----

enum Edge {
    Local(FunName),
    Remote(String, FunName),
    /// literal M:F named in a spawn/apply argument position where the
    /// argument-list length is not statically known — every defined arity
    /// of the target is reachable
    RemoteAnyArity(String, String),
}

fn reachable_funs(
    mods: &[Module],
    entry_mod: &str,
    entry: &FunName,
    poisoned: &HashMap<String, String>,
    seed_exports: &[String],
) -> CgResult<(HashSet<(String, FunName)>, HashSet<String>)> {
    let defs: HashMap<(&str, &FunName), &Fun> = mods
        .iter()
        .flat_map(|m| m.definitions.iter().map(move |(f, b)| ((m.name.as_str(), f), b)))
        .collect();
    let have_module: HashSet<&str> = mods.iter().map(|m| m.name.as_str()).collect();

    if !defs.contains_key(&(entry_mod, entry)) {
        if !have_module.contains(entry_mod) {
            return Err(format!(
                "entry module '{}' is not among the compiled modules ({})",
                entry_mod,
                have_module.iter().copied().collect::<Vec<_>>().join(", ")
            ));
        }
        let known: Vec<String> = mods
            .iter()
            .find(|m| m.name == entry_mod)
            .map(|m| {
                m.definitions
                    .iter()
                    .map(|(f, _)| format!("{}/{}", f.name, f.arity))
                    .collect()
            })
            .unwrap_or_default();
        return Err(format!(
            "entry function {}/{} is not defined in module '{}' (defined: {})",
            entry.name,
            entry.arity,
            entry_mod,
            known.join(", ")
        ));
    }

    let mut seen: HashSet<(String, FunName)> = HashSet::new();
    let mut work = vec![(entry_mod.to_string(), entry.clone())];
    // Dynamic dispatch (erlang:apply/3, incl. erlc's computed M:F(...)
    // calls) can only name a module through an atom. A compiled module
    // whose name atom appears as a literal anywhere in reachable code
    // (protocol impl_for tables, dispatch lists, pick-a-module functions)
    // gets its exports seeded as roots; modules that are merely statically
    // required (Kernel etc.) keep full pruning. Reflection exports
    // (module_info) stays out — the runtime answers it; __info__ compiles
    // (get_module_info BIF backs its attributes/compile clauses).
    let module_names: HashSet<&str> = mods.iter().map(|m| m.name.as_str()).collect();
    let mod_by_name: HashMap<&str, &Module> =
        mods.iter().map(|m| (m.name.as_str(), m)).collect();
    let seed_set: HashSet<&str> = seed_exports.iter().map(|s| s.as_str()).collect();
    // Dynamic-dispatch seeding: a module is a candidate target when its
    // name atom appears in reachable code (protocol impl tables, dispatch
    // lists). Which of its exports are roots depends on how dispatch names
    // functions: literal name positions (`impl.to_string(x)`) seed just
    // that name/arity; a dynamic name position anywhere (apply with a
    // computed function) falls back to seeding every export of candidate
    // modules. Elixir modules only — Erlang infra mentions each other's
    // atoms constantly ({global, Name} etc.) and would drag in the whole
    // OTP kernel; behaviour callback dispatch needs a finer rule —
    // TODO(behaviour-seeding).
    let mut mentioned: BTreeSet<String> = BTreeSet::new();
    let mut missing_dyn: BTreeSet<String> = BTreeSet::new();
    let mut missing_modules: std::collections::BTreeMap<String, (String, FunName)> =
        Default::default();
    // atoms mentioned by modules that contain a dynamic function-name
    // position: those get FULL export seeding (the dispatch could name
    // anything); everything else seeds only literally-named pairs
    let mut mentioned_dyn: BTreeSet<String> = BTreeSet::new();
    let mut dyn_pairs: HashSet<(String, usize)> = HashSet::new();
    // atoms in module position of {M, F, Args} / {M, Opts} literal tuples
    // (child specs) — chased as candidates even without an Elixir. prefix
    let mut tuple_heads: HashSet<String> = HashSet::new();
    let mut dyn_modules: HashSet<String> = HashSet::new();
    let mut module_atoms: HashMap<String, BTreeSet<String>> = HashMap::new();
    let mut seeded: HashSet<(String, FunName)> = HashSet::new();
    // seeding-scan deltas (see the incremental-seeding note in the loop)
    let mut new_mentioned: Vec<String> = Vec::new();
    let mut new_dyn: Vec<String> = Vec::new();
    let mut new_pairs: Vec<(String, usize)> = Vec::new();
    while let Some((module, fname)) = work.pop() {
        if !seen.insert((module.clone(), fname.clone())) {
            continue;
        }
        if seed_set.contains(module.as_str()) && mentioned.insert(module.clone()) {
            new_mentioned.push(module.clone());
        }
        let fun = defs[&(module.as_str(), &fname)];
        let mut atoms = BTreeSet::new();
        collect_atoms(&fun.body, &mut atoms);
        for a in atoms {
            if module_names.contains(a.as_str()) {
                if mentioned.insert(a.clone()) {
                    new_mentioned.push(a.clone());
                }
                module_atoms.entry(module.clone()).or_default().insert(a);
            } else if a.starts_with("Elixir.") {
                // possibly a dispatch target whose beam was never pulled
                // (consolidated protocol impls); the driver decides
                // whether a beam exists for it
                missing_dyn.insert(a);
            }
        }
        // (ModuleAtom, FunAtom) appearing as consecutive literal call args
        // is MFA-shaped data flow (proc_lib:start_link(gen, init_it, ...)):
        // seed every defined arity of the named function
        let mut arg_pairs = Vec::new();
        collect_atom_arg_pairs(&fun.body, &mut arg_pairs);
        for (pm, pf) in arg_pairs {
            if let Some(target) = mod_by_name.get(pm.as_str()) {
                for (df, _) in &target.definitions {
                    if df.name == pf && seeded.insert((pm.clone(), df.clone())) {
                        work.push((pm.clone(), df.clone()));
                    }
                }
            }
        }
        let mut fun_dyn = false;
        let mut item_pairs: HashSet<(String, usize)> = HashSet::new();
        collect_dyn_names(&fun.body, &mut item_pairs, &mut fun_dyn, &mut tuple_heads);
        for p in item_pairs {
            if dyn_pairs.insert(p.clone()) {
                new_pairs.push(p);
            }
        }
        if fun_dyn {
            dyn_modules.insert(module.clone());
        }
        if dyn_modules.contains(&module) {
            if let Some(atoms) = module_atoms.get(&module) {
                for a in atoms {
                    if mentioned_dyn.insert(a.clone()) {
                        new_dyn.push(a.clone());
                    }
                }
            }
        }
        // Incremental seeding. The old form rescanned every mentioned
        // module's exports on every work item; all the inputs (mentioned,
        // mentioned_dyn, dyn_pairs) only ever grow, so processing just the
        // deltas reaches the identical least fixpoint.
        // full seeding stays Elixir-only (Erlang infra mentions each
        // other constantly — full-seeding gen/global pulls all of OTP);
        // pair seeding (dynamically-named functions) applies everywhere.
        // Application-own modules (--seed-exports) get FULL export
        // retention once touched — configs/templates dispatch into
        // them by runtime-built atoms no static analysis can see.
        // Untouched ones stay pruned (each conformance program must
        // not drag in its siblings' closures).
        while !(new_mentioned.is_empty() && new_dyn.is_empty() && new_pairs.is_empty()) {
            // a module newly mentioned: seed per its current full status
            for a in std::mem::take(&mut new_mentioned) {
                let full = (mentioned_dyn.contains(&a) && a.starts_with("Elixir."))
                    || seed_set.contains(a.as_str());
                let m = mod_by_name[a.as_str()];
                for ex in &m.exports {
                    if ex.name == "module_info" {
                        continue;
                    }
                    if !(full || dyn_pairs.contains(&(ex.name.clone(), ex.arity))) {
                        continue;
                    }
                    if defs.contains_key(&(m.name.as_str(), ex))
                        && seeded.insert((m.name.clone(), ex.clone()))
                    {
                        work.push((m.name.clone(), ex.clone()));
                    }
                }
            }
            // a mentioned module upgraded to full (named by a dyn-dispatch
            // module): seed every export
            for a in std::mem::take(&mut new_dyn) {
                if !(a.starts_with("Elixir.") && mentioned.contains(&a)) {
                    continue;
                }
                let m = mod_by_name[a.as_str()];
                for ex in &m.exports {
                    if ex.name == "module_info" {
                        continue;
                    }
                    if defs.contains_key(&(m.name.as_str(), ex))
                        && seeded.insert((m.name.clone(), ex.clone()))
                    {
                        work.push((m.name.clone(), ex.clone()));
                    }
                }
            }
            // a new literally-named (fun, arity) pair: seed it in every
            // mentioned module that exports it
            for (pf, pa) in std::mem::take(&mut new_pairs) {
                if pf == "module_info" {
                    continue;
                }
                let exn = FunName { name: pf, arity: pa };
                for a in &mentioned {
                    let m = mod_by_name[a.as_str()];
                    if m.exports.contains(&exn)
                        && defs.contains_key(&(m.name.as_str(), &exn))
                        && seeded.insert((m.name.clone(), exn.clone()))
                    {
                        work.push((m.name.clone(), exn.clone()));
                    }
                }
            }
        }
        let mut edges = Vec::new();
        let mut letrec_bound = HashSet::new();
        collect_edges(&fun.body, &mut edges, &mut letrec_bound);
        for edge in edges {
            let (tmod, tfun) = match edge {
                Edge::Local(f) => (module.clone(), f),
                Edge::Remote(m, _) if is_bif_module(&m) => continue, // BIF
                Edge::Remote(m, f) => (m, f),
                Edge::RemoteAnyArity(m, _) if is_bif_module(&m) => continue,
                Edge::RemoteAnyArity(m, fa) => {
                    if have_module.contains(m.as_str()) {
                        if let Some(target) = mod_by_name.get(m.as_str()) {
                            for (df, _) in &target.definitions {
                                if df.name == fa {
                                    work.push((m.clone(), df.clone()));
                                }
                            }
                        }
                    } else {
                        // an uncompiled module named in a dynamic MFA — the
                        // driver may be able to pull its beam
                        missing_dyn.insert(m);
                    }
                    continue;
                }
            };
            if defs.contains_key(&(tmod.as_str(), &tfun)) {
                work.push((tmod, tfun));
            } else if have_module.contains(tmod.as_str()) {
                return Err(format!(
                    "function {}:{}/{} (required by {}:{}/{}) is not defined",
                    tmod, tfun.name, tfun.arity, module, fname.name, fname.arity
                ));
            } else if let Some(parse_err) = poisoned.get(&tmod) {
                return Err(format!(
                    "module '{}' (required by {}:{}/{}) failed to parse: {}",
                    tmod, module, fname.name, fname.arity, parse_err
                ));
            } else {
                // keep walking so ONE run reports every missing module —
                // the driver batch-pulls them instead of one per rebuild
                missing_modules
                    .entry(tmod)
                    .or_insert_with(|| (module.clone(), fname.clone()));
            }
        }
    }
    // missing modules are non-fatal: the driver pulls the ones it can
    // locate and rebuilds; callers of the rest get stubbed (loud at
    // runtime only if actually reached)
    for (m, (rm, rf)) in &missing_modules {
        eprintln!(
            "manac: module '{}' (required by {}:{}/{}) is not among the compiled modules",
            m, rm, rf.name, rf.arity
        );
    }
    // module-position tuple heads ({M, Opts} / {M, F, Args} child specs)
    // are candidates too, Elixir-prefixed or not (telemetry_poller!)
    for h in &tuple_heads {
        if !module_names.contains(h.as_str()) {
            missing_dyn.insert(h.clone());
        }
    }
    for m in &missing_dyn {
        eprintln!("manac: note: dynamic module candidate '{}' is not compiled", m);
    }
    let missing_set: HashSet<String> = missing_modules.keys().cloned().collect();
    if std::env::var("MANA_DEBUG_SEED").is_ok() {
        eprintln!(
            "manac: seed debug: mentioned={} pairs={} seeded={} to_string1={} chars_int_seeded={}",
            mentioned.len(),
            dyn_pairs.len(),
            seeded.len(),
            dyn_pairs.contains(&("to_string".to_string(), 1)),
            seeded
                .iter()
                .any(|(m, _)| m == "Elixir.String.Chars.Integer"),
        );
    }
    Ok((seen, missing_set))
}

/// Consecutive literal-atom argument pairs in call argument lists —
/// MFA-shaped data flow feeding behaviour spawn machinery.
fn collect_atom_arg_pairs(e: &Expr, out: &mut Vec<(String, String)>) {
    fn scan_args(args: &[Expr], out: &mut Vec<(String, String)>) {
        for w in args.windows(2) {
            if let (Expr::Lit(Literal::Atom(m)), Expr::Lit(Literal::Atom(fa))) =
                (&w[0], &w[1])
            {
                out.push((m.clone(), fa.clone()));
            }
        }
    }
    match e {
        Expr::Lit(_) | Expr::Var(_) | Expr::FunRef { .. } => {}
        Expr::Tuple(items) | Expr::Values(items) => {
            items.iter().for_each(|i| collect_atom_arg_pairs(i, out))
        }
        Expr::Cons(h, t) => {
            collect_atom_arg_pairs(h, out);
            collect_atom_arg_pairs(t, out);
        }
        Expr::Fun(f) => collect_atom_arg_pairs(&f.body, out),
        Expr::Let { arg, body, .. } => {
            collect_atom_arg_pairs(arg, out);
            collect_atom_arg_pairs(body, out);
        }
        Expr::LetRec { defs, body } => {
            defs.iter()
                .for_each(|(_, f)| collect_atom_arg_pairs(&f.body, out));
            collect_atom_arg_pairs(body, out);
        }
        Expr::Apply { args, .. } | Expr::PrimOp { args, .. } => {
            scan_args(args, out);
            args.iter().for_each(|a| collect_atom_arg_pairs(a, out));
        }
        Expr::Call { args, .. } => {
            scan_args(args, out);
            args.iter().for_each(|a| collect_atom_arg_pairs(a, out));
        }
        Expr::CallDyn { module, name, args } => {
            scan_args(args, out);
            collect_atom_arg_pairs(module, out);
            collect_atom_arg_pairs(name, out);
            args.iter().for_each(|a| collect_atom_arg_pairs(a, out));
        }
        Expr::Case { arg, clauses } => {
            collect_atom_arg_pairs(arg, out);
            for c in clauses {
                collect_atom_arg_pairs(&c.guard, out);
                collect_atom_arg_pairs(&c.body, out);
            }
        }
        Expr::Try { arg, body, handler, .. } => {
            collect_atom_arg_pairs(arg, out);
            collect_atom_arg_pairs(body, out);
            collect_atom_arg_pairs(handler, out);
        }
        Expr::Do(a, b) => {
            collect_atom_arg_pairs(a, out);
            collect_atom_arg_pairs(b, out);
        }
        Expr::Binary(segs) => segs
            .iter()
            .for_each(|s| collect_atom_arg_pairs(&s.value, out)),
        Expr::Map { pairs, update } => {
            for (k, _, v) in pairs {
                collect_atom_arg_pairs(k, out);
                collect_atom_arg_pairs(v, out);
            }
            if let Some(u) = update {
                collect_atom_arg_pairs(u, out);
            }
        }
    }
}

/// Literal function names in dynamic-call name positions (with arity), and
/// whether any name position is a computed expression.
fn collect_dyn_names(
    e: &Expr,
    pairs: &mut HashSet<(String, usize)>,
    dyn_any: &mut bool,
    heads: &mut HashSet<String>,
) {
    match e {
        Expr::CallDyn { module: _, name, args } => {
            match name.as_ref() {
                Expr::Lit(Literal::Atom(a)) => {
                    pairs.insert((a.clone(), args.len()));
                }
                _ => *dyn_any = true,
            }
            args.iter().for_each(|a| collect_dyn_names(a, pairs, dyn_any, heads));
        }
        Expr::Call { module, name, args } => {
            // a surviving erlang:apply/3 call has fully dynamic M and F
            if module == "erlang" && name == "apply" && args.len() == 3 {
                *dyn_any = true;
            }
            // make_fun(Mod, F, A) with literal F/A: a callback-cache shape
            // (gen_server) — the named function is dynamically dispatched
            if module == "erlang" && name == "make_fun" && args.len() == 3 {
                if let (Expr::Lit(Literal::Atom(fa)), Expr::Lit(Literal::Int(n))) =
                    (&args[1], &args[2])
                {
                    if *n >= 0 {
                        pairs.insert((fa.clone(), *n as usize));
                    }
                }
            }
            args.iter().for_each(|a| collect_dyn_names(a, pairs, dyn_any, heads));
        }
        Expr::Lit(_) | Expr::Var(_) | Expr::FunRef { .. } => {}
        Expr::Tuple(items) | Expr::Values(items) => {
            // {Mod, Fun, Args} literal tuples (supervisor child specs,
            // callback tuples) are applied dynamically: seed the
            // (fun, arity) pair — it only takes effect on modules that are
            // already dynamic candidates, so incidental 3-tuples are inert
            if items.len() == 3 {
                if let (Expr::Lit(Literal::Atom(m)), Expr::Lit(Literal::Atom(fa))) =
                    (&items[0], &items[1])
                {
                    if let Some(n) = static_list_len(&items[2]) {
                        pairs.insert((fa.clone(), n));
                        heads.insert(m.clone());
                    }
                }
            }
            // {Module, Opts} child specs: Supervisor calls
            // Module.child_spec(Opts) dynamically
            if items.len() == 2 {
                if let (Expr::Lit(Literal::Atom(m)), Expr::Lit(Literal::Nil))
                | (Expr::Lit(Literal::Atom(m)), Expr::Cons(..)) = (&items[0], &items[1])
                {
                    heads.insert(m.clone());
                    pairs.insert(("child_spec".to_string(), 1));
                }
            }
            items.iter().for_each(|i| collect_dyn_names(i, pairs, dyn_any, heads))
        }
        Expr::Cons(h, t) => {
            collect_dyn_names(h, pairs, dyn_any, heads);
            collect_dyn_names(t, pairs, dyn_any, heads);
        }
        Expr::Fun(f) => collect_dyn_names(&f.body, pairs, dyn_any, heads),
        Expr::Let { arg, body, .. } => {
            collect_dyn_names(arg, pairs, dyn_any, heads);
            collect_dyn_names(body, pairs, dyn_any, heads);
        }
        Expr::LetRec { defs, body } => {
            defs.iter()
                .for_each(|(_, f)| collect_dyn_names(&f.body, pairs, dyn_any, heads));
            collect_dyn_names(body, pairs, dyn_any, heads);
        }
        Expr::Apply { args, .. } | Expr::PrimOp { args, .. } => {
            args.iter().for_each(|a| collect_dyn_names(a, pairs, dyn_any, heads))
        }
        Expr::Case { arg, clauses } => {
            collect_dyn_names(arg, pairs, dyn_any, heads);
            for c in clauses {
                collect_dyn_names(&c.guard, pairs, dyn_any, heads);
                collect_dyn_names(&c.body, pairs, dyn_any, heads);
            }
        }
        Expr::Try { arg, body, handler, .. } => {
            collect_dyn_names(arg, pairs, dyn_any, heads);
            collect_dyn_names(body, pairs, dyn_any, heads);
            collect_dyn_names(handler, pairs, dyn_any, heads);
        }
        Expr::Do(a, b) => {
            collect_dyn_names(a, pairs, dyn_any, heads);
            collect_dyn_names(b, pairs, dyn_any, heads);
        }
        Expr::Binary(segs) => segs
            .iter()
            .for_each(|s| collect_dyn_names(&s.value, pairs, dyn_any, heads)),
        Expr::Map { pairs: mp, update } => {
            for (k, _, v) in mp {
                collect_dyn_names(k, pairs, dyn_any, heads);
                collect_dyn_names(v, pairs, dyn_any, heads);
            }
            if let Some(u) = update {
                collect_dyn_names(u, pairs, dyn_any, heads);
            }
        }
    }
}

/// Every atom literal in an expression tree, including clause patterns
/// (protocol dispatch matches on module atoms) — drives apply export
/// seeding in reachable_funs.
fn collect_atoms(e: &Expr, out: &mut BTreeSet<String>) {
    fn pat_atoms(p: &Pattern, out: &mut BTreeSet<String>) {
        match p {
            Pattern::Lit(Literal::Atom(a)) => {
                out.insert(a.clone());
            }
            Pattern::Lit(_) | Pattern::Var(_) => {}
            Pattern::Alias(_, inner) => pat_atoms(inner, out),
            Pattern::Tuple(ps) => ps.iter().for_each(|p| pat_atoms(p, out)),
            Pattern::Cons(h, t) => {
                pat_atoms(h, out);
                pat_atoms(t, out);
            }
            Pattern::Binary(segs) => segs.iter().for_each(|s| pat_atoms(&s.value, out)),
            Pattern::Map(pairs) => pairs.iter().for_each(|(k, v)| {
                collect_atoms(k, out);
                pat_atoms(v, out);
            }),
        }
    }
    match e {
        Expr::Lit(Literal::Atom(a)) => {
            out.insert(a.clone());
        }
        Expr::Lit(_) | Expr::Var(_) | Expr::FunRef { .. } => {}
        Expr::Tuple(items) | Expr::Values(items) => {
            items.iter().for_each(|i| collect_atoms(i, out))
        }
        Expr::Cons(h, t) => {
            collect_atoms(h, out);
            collect_atoms(t, out);
        }
        Expr::Fun(f) => collect_atoms(&f.body, out),
        Expr::Let { arg, body, .. } => {
            collect_atoms(arg, out);
            collect_atoms(body, out);
        }
        Expr::LetRec { defs, body } => {
            defs.iter().for_each(|(_, f)| collect_atoms(&f.body, out));
            collect_atoms(body, out);
        }
        Expr::Apply { args, .. } => args.iter().for_each(|a| collect_atoms(a, out)),
        Expr::Call { args, .. } | Expr::PrimOp { args, .. } => {
            args.iter().for_each(|a| collect_atoms(a, out))
        }
        Expr::CallDyn { module, name, args } => {
            collect_atoms(module, out);
            collect_atoms(name, out);
            args.iter().for_each(|a| collect_atoms(a, out));
        }
        Expr::Case { arg, clauses } => {
            collect_atoms(arg, out);
            for c in clauses {
                c.patterns.iter().for_each(|p| pat_atoms(p, out));
                collect_atoms(&c.guard, out);
                collect_atoms(&c.body, out);
            }
        }
        Expr::Try { arg, body, handler, .. } => {
            collect_atoms(arg, out);
            collect_atoms(body, out);
            collect_atoms(handler, out);
        }
        Expr::Do(a, b) => {
            collect_atoms(a, out);
            collect_atoms(b, out);
        }
        Expr::Binary(segs) => segs.iter().for_each(|s| collect_atoms(&s.value, out)),
        Expr::Map { pairs, update } => {
            for (k, _, v) in pairs {
                collect_atoms(k, out);
                collect_atoms(v, out);
            }
            if let Some(u) = update {
                collect_atoms(u, out);
            }
        }
    }
}

/// Length of a statically-spelled proper list (cons spine ending in nil),
/// if determinable.
fn static_list_len(e: &Expr) -> Option<usize> {
    match e {
        Expr::Lit(Literal::Nil) => Some(0),
        Expr::Cons(_, t) => static_list_len(t).map(|n| n + 1),
        _ => None,
    }
}

fn collect_edges(e: &Expr, out: &mut Vec<Edge>, letrec_bound: &mut HashSet<FunName>) {
    match e {
        Expr::Var(_) | Expr::Lit(_) => {}
        Expr::FunRef { module, fun } => match module {
            Some(m) => out.push(Edge::Remote(m.clone(), fun.clone())),
            None => {
                if !letrec_bound.contains(fun) {
                    out.push(Edge::Local(fun.clone()));
                }
            }
        },
        Expr::Tuple(items) | Expr::Values(items) => items
            .iter()
            .for_each(|i| collect_edges(i, out, letrec_bound)),
        Expr::Cons(h, t) => {
            collect_edges(h, out, letrec_bound);
            collect_edges(t, out, letrec_bound);
        }
        Expr::Fun(f) => collect_edges(&f.body, out, letrec_bound),
        Expr::Let { arg, body, .. } => {
            collect_edges(arg, out, letrec_bound);
            collect_edges(body, out, letrec_bound);
        }
        Expr::LetRec { defs, body } => {
            let added: Vec<FunName> = defs
                .iter()
                .map(|(f, _)| f.clone())
                .filter(|f| letrec_bound.insert(f.clone()))
                .collect();
            defs.iter()
                .for_each(|(_, f)| collect_edges(&f.body, out, letrec_bound));
            collect_edges(body, out, letrec_bound);
            for f in added {
                letrec_bound.remove(&f);
            }
        }
        Expr::Apply { target, args } => {
            if let ApplyTarget::LocalFun(f) = target {
                if !letrec_bound.contains(f) {
                    out.push(Edge::Local(f.clone()));
                }
            }
            args.iter()
                .for_each(|a| collect_edges(a, out, letrec_bound));
        }
        Expr::Call { module, name, args } => {
            out.push(Edge::Remote(
                module.clone(),
                FunName {
                    name: name.clone(),
                    arity: args.len(),
                },
            ));
            // literal-MFA spawns/applies are dynamic dispatch reachability
            // can see: spawn(M, F, Args) / spawn_opt / apply — behaviour
            // machinery (proc_lib → gen:init_it) lives on this path
            let mfa_args = match (module.as_str(), name.as_str(), args.len()) {
                ("erlang", "spawn", 3)
                | ("erlang", "spawn_link", 3)
                | ("erlang", "spawn_monitor", 3)
                | ("erlang", "spawn_opt", 4)
                | ("erlang", "apply", 3) => Some((&args[0], &args[1], &args[2])),
                _ => None,
            };
            if let Some((m, fa, alist)) = mfa_args {
                if let (Expr::Lit(Literal::Atom(m)), Expr::Lit(Literal::Atom(fa))) = (m, fa)
                {
                    match static_list_len(alist) {
                        Some(n) => out.push(Edge::Remote(
                            m.clone(),
                            FunName { name: fa.clone(), arity: n },
                        )),
                        None => out.push(Edge::RemoteAnyArity(m.clone(), fa.clone())),
                    }
                }
            }
            args.iter()
                .for_each(|a| collect_edges(a, out, letrec_bound));
        }
        Expr::CallDyn { module, name, args } => {
            out.push(Edge::Remote(
                "erlang".into(),
                FunName { name: "apply".into(), arity: 3 },
            ));
            collect_edges(module, out, letrec_bound);
            collect_edges(name, out, letrec_bound);
            args.iter()
                .for_each(|a| collect_edges(a, out, letrec_bound));
        }
        Expr::PrimOp { args, .. } => args
            .iter()
            .for_each(|a| collect_edges(a, out, letrec_bound)),
        Expr::Case { arg, clauses } => {
            collect_edges(arg, out, letrec_bound);
            for c in clauses {
                collect_edges(&c.guard, out, letrec_bound);
                collect_edges(&c.body, out, letrec_bound);
            }
        }
        Expr::Binary(segs) => {
            for s in segs {
                collect_edges(&s.value, out, letrec_bound);
                s.spec
                    .iter()
                    .for_each(|x| collect_edges(x, out, letrec_bound));
            }
        }
        Expr::Map { pairs, update } => {
            for (k, _, v) in pairs {
                collect_edges(k, out, letrec_bound);
                collect_edges(v, out, letrec_bound);
            }
            if let Some(u) = update {
                collect_edges(u, out, letrec_bound);
            }
        }
        Expr::Try {
            arg, body, handler, ..
        } => {
            collect_edges(arg, out, letrec_bound);
            collect_edges(body, out, letrec_bound);
            collect_edges(handler, out, letrec_bound);
        }
        Expr::Do(a, b) => {
            collect_edges(a, out, letrec_bound);
            collect_edges(b, out, letrec_bound);
        }
    }
}

fn is_true_atom(e: &Expr) -> bool {
    matches!(e, Expr::Lit(Literal::Atom(a)) if a == "true")
}

fn mangle(module: &str, f: &FunName) -> String {
    format!("mn_{}_{}_{}", sanitize(module), sanitize(&f.name), f.arity)
}

fn sanitize(s: &str) -> String {
    s.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() {
                c.to_string()
            } else {
                format!("_x{:02x}", c as u32)
            }
        })
        .collect()
}

fn be(e: inkwell::builder::BuilderError) -> String {
    format!("LLVM builder: {}", e)
}

fn call_result(call: CallSiteValue<'_>) -> CgResult<inkwell::values::BasicValueEnum<'_>> {
    match call.try_as_basic_value() {
        ValueKind::Basic(v) => Ok(v),
        ValueKind::Instruction(_) => Err("call to void function used as a value".into()),
    }
}
