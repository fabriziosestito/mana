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

    // Parse every input; failures are only fatal if the module is needed.
    let mut modules: Vec<mana_syntax::Module> = Vec::new();
    let mut poisoned: HashMap<String, String> = HashMap::new();
    for input in &inputs {
        let core_path = match input.extension().and_then(|e| e.to_str()) {
            Some("core") => input.clone(),
            Some("erl") => erl_to_core(input)?,
            _ => return Err(format!("{}: input must be .erl or .core", input.display())),
        };
        let src = std::fs::read_to_string(&core_path)
            .map_err(|e| format!("reading {}: {}", core_path.display(), e))?;
        match mana_syntax::parse_module(&src) {
            Ok(m) => modules.push(m),
            Err(e) => {
                // module name is unknown when parsing fails; key by file stem
                let name = core_path
                    .file_stem()
                    .map(|s| s.to_string_lossy().into_owned())
                    .unwrap_or_default();
                eprintln!(
                    "manac: warning: skipping {} (parse error: {})",
                    core_path.display(),
                    e
                );
                poisoned.insert(name, e);
            }
        }
    }
    if modules.is_empty() {
        return Err("no input module could be parsed".into());
    }

    let (entry_mod, entry) = resolve_entry(entry_spec.as_deref(), &modules[0].name)?;

    let out = output.unwrap_or_else(|| PathBuf::from(&entry_mod));
    let obj_dir = std::env::temp_dir().join(format!("manac-{}", std::process::id()));
    let cache = obj_cache(emit_ir)?;
    let objs = mana_codegen::compile_program(
        &modules,
        &entry_mod,
        &entry,
        &obj_dir,
        emit_ir,
        &poisoned,
        cache.as_ref(),
        &seed_exports,
    )?;

    let link_result = link(&objs, &out);
    let _ = std::fs::remove_dir_all(&obj_dir);
    link_result?;
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

fn link(objs: &[PathBuf], out: &Path) -> Result<(), String> {
    let rt = runtime_lib()?;
    let status = Command::new("cc")
        .args(objs)
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
