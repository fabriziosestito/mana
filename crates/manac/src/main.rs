//! manac — Core Erlang → native binary compiler driver.
//!
//! Usage: manac [-o OUT] [--entry [MODULE:]FUN/ARITY] [--emit-ir] FILES...
//!
//! Inputs are `.core` files or `.erl` files (run through `erlc +to_core`
//! first). All modules are compiled together, closed-world: only code
//! reachable from the entry (default: `main/0` in the first input's module)
//! is compiled, one object per module, linked into a single binary.
//!
//! A file that fails to parse is skipped with a warning; it only becomes an
//! error if the program actually needs that module.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

fn main() -> ExitCode {
    // AST walkers recurse per list cell; stdlib modules carry list literals
    // thousands of elements deep — give the compiler a deep stack
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
            "-o" => {
                output = Some(PathBuf::from(
                    args.next().ok_or("-o requires an argument")?,
                ))
            }
            "--entry" => {
                entry_spec = Some(args.next().ok_or("--entry requires [MODULE:]FUN/ARITY")?)
            }
            "--emit-ir" => emit_ir = true,
            // external native modules (hex-package native/ crates): a
            // manifest of `MODULE FUN ARITY SYMBOL MAYGC MAYRAISE` lines,
            // plus the compiled static lib(s) to link.
            "--native-manifest" => {
                native_manifest = Some(PathBuf::from(
                    args.next().ok_or("--native-manifest requires a path")?,
                ))
            }
            "--native-obj" => native_objs.push(PathBuf::from(
                args.next().ok_or("--native-obj requires a path")?,
            )),
            // the runtime-implemented module list, for the mix driver's
            // dependency-closure BFS (one line per module)
            "--print-bif-modules" => {
                for m in mana_codegen::BIF_MODULES {
                    println!("{}", m);
                }
                return Ok(());
            }
            // application-own modules: every export stays a root (deps are
            // pruned; the app is wired by config atoms and template names)
            "--seed-exports" => seed_exports
                .push(args.next().ok_or("--seed-exports requires a module name")?),
            "-h" | "--help" => {
                println!(
                    "usage: manac [-o OUT] [--entry [MODULE:]FUN/ARITY] [--emit-ir] FILES..."
                );
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

    // Load every input in parallel: read + hash, then either a summary-cache
    // hit (no parse — the AST is only re-materialized on an object-cache
    // miss) or parse + summarize + publish. Failures are only fatal if the
    // module is needed. Order is preserved: units[0] is the default entry
    // module and link order follows input order. Workers get deep stacks —
    // AST walkers and the parser recurse per list cell on stdlib literals.
    let t_total = std::time::Instant::now();
    let cache = obj_cache(emit_ir)?;
    // the reference-walker cross-check needs every AST present
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
                    (String::new(), format!("reading {}: {}", core_path.display(), e))
                })?;
                let source_hash = *blake3::hash(src.as_bytes()).as_bytes();
                if !force_ast {
                    if let Some(sum) =
                        cache.as_ref().and_then(|c| c.get_summary(&source_hash))
                    {
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
                        // module name is unknown when parsing fails; key
                        // by file stem
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
            // empty name = a hard I/O or usage error, not a parse poison
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

/// The content-addressed object cache under the OS user-cache dir
/// (~/.cache/mana, ~/Library/Caches/mana, %LOCALAPPDATA%\mana), overridden
/// by MANA_CACHE_DIR, disabled by MANA_NO_CACHE or --emit-ir. The tool
/// identity is the manac binary's own content hash (dev-branch rule, like
/// Go): rebuilding the compiler invalidates everything, correctly.
fn obj_cache(emit_ir: bool) -> Result<Option<mana_codegen::ObjCache>, String> {
    if emit_ir || std::env::var_os("MANA_NO_CACHE").is_some() {
        return Ok(None);
    }
    let root = match std::env::var_os("MANA_CACHE_DIR") {
        Some(d) => PathBuf::from(d),
        None => match dirs::cache_dir() {
            Some(d) => d.join("mana"),
            None => return Ok(None), // no home dir — run uncached
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

/// `[MODULE:]FUN/ARITY`; module defaults to the first input file's module.
/// (Module names may contain dots — 'Elixir.Foo' — but never colons.)
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
    Ok((
        module,
        mana_syntax::FunName {
            name: fun,
            arity,
        },
    ))
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
        // package native static libs go before libmana_rt.a so their
        // undefined mana_rt_* symbols resolve against the runtime
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

/// Parse a native-module manifest: whitespace-separated
/// `MODULE FUN ARITY SYMBOL MAYGC MAYRAISE` lines (MAYGC/MAYRAISE = 0|1),
/// blank lines and `#` comments ignored.
fn parse_native_manifest(path: &Path) -> Result<mana_codegen::NativeManifest, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("reading {}: {}", path.display(), e))?;
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

/// Find libmana_rt.a: $MANA_RT_LIB overrides; otherwise look next to manac
/// (cargo puts both artifacts in the same target dir).
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
