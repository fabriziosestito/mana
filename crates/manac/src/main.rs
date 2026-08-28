//! manac — Core Erlang → native binary compiler driver.
//!
//! Usage: manac [-o OUT] [--emit-ir] FILE.{erl,core}
//!
//! .erl inputs are first run through `erlc +to_core`.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("manac: {}", e);
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let mut input: Option<PathBuf> = None;
    let mut output: Option<PathBuf> = None;
    let mut emit_ir = false;

    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "-o" => {
                output = Some(PathBuf::from(
                    args.next().ok_or("-o requires an argument")?,
                ))
            }
            "--emit-ir" => emit_ir = true,
            "-h" | "--help" => {
                println!("usage: manac [-o OUT] [--emit-ir] FILE.{{erl,core}}");
                return Ok(());
            }
            other if other.starts_with('-') => return Err(format!("unknown flag {}", other)),
            other => input = Some(PathBuf::from(other)),
        }
    }
    let input = input.ok_or("no input file (try --help)")?;

    let core_path = match input.extension().and_then(|e| e.to_str()) {
        Some("core") => input.clone(),
        Some("erl") => erl_to_core(&input)?,
        _ => return Err("input must be a .erl or .core file".into()),
    };

    let src = std::fs::read_to_string(&core_path)
        .map_err(|e| format!("reading {}: {}", core_path.display(), e))?;
    let ast = mana_syntax::parse_module(&src)?;

    let out = output.unwrap_or_else(|| PathBuf::from(&ast.name));
    let obj = out.with_extension("o");
    mana_codegen::compile_module(&ast, &obj, emit_ir)?;

    link(&obj, &out)?;
    let _ = std::fs::remove_file(&obj);
    println!("{}", out.display());
    Ok(())
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

fn link(obj: &Path, out: &Path) -> Result<(), String> {
    let rt = runtime_lib()?;
    let status = Command::new("cc")
        .arg(obj)
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
