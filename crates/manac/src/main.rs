//! manac is the compiler driver. It compiles Core Erlang to a native binary.
//!
//! Usage: manac [-o OUT] [--entry [MODULE:]FUN/ARITY] [--emit-ir] FILES...
//!
//! The inputs are `.core` files or `.erl` files. The driver runs `.erl`
//! files through `erlc +to_core` first. The driver compiles all modules
//! together, as a closed world. It compiles only the code that the entry
//! reaches. The default entry is `main/0` in the module of the first input.
//! Each module becomes one object. The linker joins the objects into a
//! single binary.
//!
//! If a file does not parse, the driver skips it and prints a warning. The
//! skip becomes an error only if the program needs that module.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

fn main() -> ExitCode {
    // The AST walkers recurse once per list cell. The stdlib modules hold
    // list literals that are thousands of elements deep. The compiler
    // thread needs a deep stack.
    let child = std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(run)
        .expect("spawning compiler thread");
    match child.join().expect("compiler thread panicked") {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("manac: {}", e);
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let mut inputs: Vec<PathBuf> = Vec::new();
    let mut output: Option<PathBuf> = None;
    let mut entry_spec: Option<String> = None;
    let mut emit_ir = false;
    let mut seed_exports: Vec<String> = Vec::new();
    let mut native_manifest: Option<PathBuf> = None;
    let mut native_objs: Vec<PathBuf> = Vec::new();

    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "-o" => output = Some(PathBuf::from(args.next().ok_or("-o requires an argument")?)),
            "--entry" => {
                entry_spec = Some(args.next().ok_or("--entry requires [MODULE:]FUN/ARITY")?)
            }
            "--emit-ir" => emit_ir = true,
            // External native modules come from the `native/` crates of hex
            // packages. The manifest holds `MODULE FUN ARITY SYMBOL MAYGC MAYRAISE`
            // lines. The static libraries to link come with it.
            "--native-manifest" => {
                native_manifest = Some(PathBuf::from(
                    args.next().ok_or("--native-manifest requires a path")?,
                ))
            }
            "--native-obj" => native_objs.push(PathBuf::from(
                args.next().ok_or("--native-obj requires a path")?,
            )),
            // The mix driver uses this list of runtime modules for its
            // dependency-closure BFS. The output has one module per line.
            "--print-bif-modules" => {
                for m in mana_codegen::BIF_MODULES {
                    println!("{}", m);
                }
                return Ok(());
            }
            // For modules that belong to the application, every export stays
            // a root. Dependencies are pruned. Config atoms and template
            // names wire the application together.
            "--seed-exports" => {
                seed_exports.push(args.next().ok_or("--seed-exports requires a module name")?)
            }
            "-h" | "--help" => {
                println!("usage: manac [-o OUT] [--entry [MODULE:]FUN/ARITY] [--emit-ir] FILES...");
                return Ok(());
            }
            other if other.starts_with('-') => return Err(format!("unknown flag {}", other)),
            other => inputs.push(PathBuf::from(other)),
        }
    }
    if inputs.is_empty() {
        return Err("no input files (try --help)".into());
    }

    if let Some(path) = &native_manifest {
        let m = parse_native_manifest(path)?;
        mana_codegen::set_native_manifest(m);
    }

    // The driver loads every input in parallel. Each worker reads the file
    // and hashes it. If the summary cache has the hash, the worker does not
    // parse. The AST is rebuilt only on an object-cache miss. Otherwise the
    // worker parses, summarizes, and publishes the summary. A failure is
    // fatal only if the program needs the module. The order is kept:
    // units[0] is the default entry module, and the link order is the input
    // order. The workers get deep stacks. The AST walkers and the parser
    // recurse once per list cell on stdlib literals.
    let t_total = std::time::Instant::now();
    let cache = obj_cache(emit_ir)?;
    // The reference-walker cross-check needs every AST present.
    let force_ast = std::env::var_os("MANA_CHECK_ANALYSIS").is_some();
    let pool = rayon::ThreadPoolBuilder::new()
        .stack_size(256 * 1024 * 1024)
        .build()
        .map_err(|e| format!("thread pool: {}", e))?;
    use rayon::prelude::*;
    let loaded: Vec<Result<mana_codegen::ModuleUnit, (String, String)>> = pool.install(|| {
        inputs
            .par_iter()
            .map(|input| {
                let core_path = match input.extension().and_then(|e| e.to_str()) {
                    Some("core") => input.clone(),
                    Some("erl") => erl_to_core(input).map_err(|e| (String::new(), e))?,
                    _ => {
                        return Err((
                            String::new(),
                            format!("{}: input must be .erl or .core", input.display()),
                        ))
                    }
                };
                let src = std::fs::read_to_string(&core_path).map_err(|e| {
                    (
                        String::new(),
                        format!("reading {}: {}", core_path.display(), e),
                    )
                })?;
                let source_hash = *blake3::hash(src.as_bytes()).as_bytes();
                if !force_ast {
                    if let Some(sum) = cache.as_ref().and_then(|c| c.get_summary(&source_hash)) {
                        return Ok(mana_codegen::ModuleUnit {
                            path: core_path,
                            source_hash,
                            summary: sum,
                            ast: None,
                        });
                    }
                }
                match mana_syntax::parse_module(&src) {
                    Ok(m) => {
                        let summary = mana_codegen::summarize(&m);
                        if let Some(c) = cache.as_ref() {
                            c.put_summary(&source_hash, &summary);
                        }
                        Ok(mana_codegen::ModuleUnit {
                            path: core_path,
                            source_hash,
                            summary,
                            ast: Some(m),
                        })
                    }
                    Err(e) => {
                        // The module name is unknown when the parse fails.
                        // The file stem is the key instead.
                        let name = core_path
                            .file_stem()
                            .map(|s| s.to_string_lossy().into_owned())
                            .unwrap_or_default();
                        eprintln!(
                            "manac: warning: skipping {} (parse error: {})",
                            core_path.display(),
                            e
                        );
                        Err((name, e))
                    }
                }
            })
            .collect()
    });
    let mut units: Vec<mana_codegen::ModuleUnit> = Vec::new();
    let mut poisoned: HashMap<String, String> = HashMap::new();
    for r in loaded {
        match r {
            Ok(u) => units.push(u),
            // An empty name marks a hard I/O or usage error, not a parse poison.
            Err((name, e)) if name.is_empty() => return Err(e),
            Err((name, e)) => {
                poisoned.insert(name, e);
            }
        }
    }
    if units.is_empty() {
        return Err("no input module could be parsed".into());
    }
    let parse_s = t_total.elapsed().as_secs_f64();

    let (entry_mod, entry) = resolve_entry(entry_spec.as_deref(), &units[0].summary.name)?;

    let out = output.unwrap_or_else(|| PathBuf::from(&entry_mod));
    let obj_dir = std::env::temp_dir().join(format!("manac-{}", std::process::id()));
    let (objs, stats) = mana_codegen::compile_program(
        &units,
        &entry_mod,
        &entry,
        &obj_dir,
        emit_ir,
        &poisoned,
        cache.as_ref(),
        &seed_exports,
    )?;

    let t_link = std::time::Instant::now();
    let link_result = link(&objs, &native_objs, &out);
    let link_s = t_link.elapsed().as_secs_f64();
    let _ = std::fs::remove_dir_all(&obj_dir);
    link_result?;
    eprintln!(
        "manac: time: parse={:.2}s/{} reach={:.2}s gc={:.2}s raise={:.2}s key={:.2}s codegen={:.2}s (hit={} miss={}) link={:.2}s total={:.2}s",
        parse_s,
        inputs.len(),
        stats.reach_s,
        stats.gc_s,
        stats.raise_s,
        stats.key_s,
        stats.codegen_s,
        stats.hits,
        stats.misses,
        link_s,
        t_total.elapsed().as_secs_f64()
    );
    println!("{}", out.display());
    Ok(())
}

/// The content-addressed object cache. It lives under the user cache
/// directory of the OS (~/.cache/mana, ~/Library/Caches/mana,
/// %LOCALAPPDATA%\mana). MANA_CACHE_DIR overrides the location.
/// MANA_NO_CACHE or --emit-ir disables the cache. The tool identity is the
/// content hash of the manac binary itself (the dev-branch rule). A rebuild
/// of the compiler invalidates every cache entry. This is the correct result.
fn obj_cache(emit_ir: bool) -> Result<Option<mana_codegen::ObjCache>, String> {
    if emit_ir || std::env::var_os("MANA_NO_CACHE").is_some() {
        return Ok(None);
    }
    let root = match std::env::var_os("MANA_CACHE_DIR") {
        Some(d) => PathBuf::from(d),
        None => match dirs::cache_dir() {
            Some(d) => d.join("mana"),
            None => return Ok(None), // No home directory. Run without a cache.
        },
    };
    let exe = std::env::current_exe().map_err(|e| format!("current_exe: {}", e))?;
    let bytes = std::fs::read(&exe).map_err(|e| format!("reading {}: {}", exe.display(), e))?;
    let tool_hash = *blake3::hash(&bytes).as_bytes();
    Ok(Some(mana_codegen::ObjCache {
        root,
        tool_hash,
        debug: std::env::var_os("MANA_DEBUG_CACHE").is_some(),
    }))
}

/// Parse `[MODULE:]FUN/ARITY`. If the module is absent, the module of the
/// first input file is the default. A module name can contain dots, for
/// example 'Elixir.Foo', but never a colon.
fn resolve_entry(
    spec: Option<&str>,
    default_module: &str,
) -> Result<(String, mana_syntax::FunName), String> {
    let spec = spec.unwrap_or("main/0");
    let (mf, arity) = spec
        .rsplit_once('/')
        .ok_or_else(|| format!("bad --entry '{}': expected [MODULE:]FUN/ARITY", spec))?;
    let arity: usize = arity
        .parse()
        .map_err(|_| format!("bad --entry arity in '{}'", spec))?;
    let (module, fun) = match mf.split_once(':') {
        Some((m, f)) => (m.to_string(), f.to_string()),
        None => (default_module.to_string(), mf.to_string()),
    };
    Ok((module, mana_syntax::FunName { name: fun, arity }))
}

fn erl_to_core(input: &Path) -> Result<PathBuf, String> {
    let dir = match input.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    };
    let status = Command::new("erlc")
        .arg("+to_core")
        .arg("-o")
        .arg(dir)
        .arg(input)
        .status()
        .map_err(|e| format!("running erlc: {}", e))?;
    if !status.success() {
        return Err("erlc failed".into());
    }
    Ok(input.with_extension("core"))
}

fn link(objs: &[PathBuf], native_objs: &[PathBuf], out: &Path) -> Result<(), String> {
    let rt = runtime_lib()?;
    let status = Command::new("cc")
        .args(objs)
        // The package native static libraries go before libmana_rt.a. Then
        // their undefined mana_rt_* symbols resolve against the runtime.
        .args(native_objs)
        .arg(&rt)
        .args(["-lpthread", "-ldl", "-lm"])
        .arg("-o")
        .arg(out)
        .status()
        .map_err(|e| format!("running cc: {}", e))?;
    if !status.success() {
        return Err("linking failed".into());
    }
    Ok(())
}

/// Parse a native-module manifest. Each line holds whitespace-separated
/// fields: `MODULE FUN ARITY SYMBOL MAYGC MAYRAISE`. MAYGC and MAYRAISE are
/// 0 or 1. The parser ignores blank lines and `#` comments.
fn parse_native_manifest(path: &Path) -> Result<mana_codegen::NativeManifest, String> {
    let text =
        std::fs::read_to_string(path).map_err(|e| format!("reading {}: {}", path.display(), e))?;
    let mut m = mana_codegen::NativeManifest::default();
    for (n, line) in text.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let f: Vec<&str> = line.split_whitespace().collect();
        if f.len() != 6 {
            return Err(format!(
                "{}:{}: expected `MODULE FUN ARITY SYMBOL MAYGC MAYRAISE`, got {:?}",
                path.display(),
                n + 1,
                line
            ));
        }
        let arity: usize = f[2]
            .parse()
            .map_err(|_| format!("{}:{}: bad arity {:?}", path.display(), n + 1, f[2]))?;
        m.modules.insert(f[0].to_string());
        m.fns.insert(
            (f[0].to_string(), f[1].to_string(), arity),
            mana_codegen::NativeFn {
                symbol: f[3].to_string(),
                may_gc: f[4] != "0",
                may_raise: f[5] != "0",
            },
        );
    }
    Ok(m)
}

/// Find libmana_rt.a. If $MANA_RT_LIB is set, it wins. Otherwise the
/// function looks next to manac. Cargo puts both artifacts in the same
/// target directory.
fn runtime_lib() -> Result<PathBuf, String> {
    if let Ok(p) = std::env::var("MANA_RT_LIB") {
        return Ok(PathBuf::from(p));
    }
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let candidate = exe
        .parent()
        .ok_or("cannot locate manac directory")?
        .join("libmana_rt.a");
    if candidate.exists() {
        Ok(candidate)
    } else {
        Err(format!(
            "runtime library not found at {} (set MANA_RT_LIB)",
            candidate.display()
        ))
    }
}
