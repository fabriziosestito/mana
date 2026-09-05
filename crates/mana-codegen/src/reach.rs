//! Reachability analysis over module summaries. The module holds the list
//! of native BIF modules, the per-build manifest of external native modules,
//! and the walk that finds every function reachable from the entry point.
//! The walk also seeds exports of modules that dynamic dispatch can name.
//! The native manifest is build data. It must never leak into cached
//! summaries.

use crate::*;

/// Modules that the runtime implements natively. The compiler never
/// compiles them from beams and never follows them as dependencies. The mix
/// driver reads this list with `manac --print-bif-modules`. The list is the
/// single source of truth for the closure BFS of the driver.
pub const BIF_MODULES: &[&str] = &[
    "erlang", "maps", "io", "unicode", "persistent_term", "code", "io_lib",
    "logger", "ets", "application", "file", "prim_file", "math", "re", "timer",
    "gen_tcp", "inet", "crypto",
    "erts_internal", "zlib",
    "elixir_erl", "erl_eval", "beam_lib", "global", "global_group",
    "net_kernel",
];

pub(crate) fn is_bif_module(m: &str) -> bool {
    BIF_MODULES.contains(&m)
}

// External native modules (hex-package `native/` crates)
//
// BIF_MODULES is native code baked into libmana_rt.a and known to the
// compiler. External native modules are different. Each build declares them
// from the `mana_native:` metadata of the project dependencies. Each one is
// a stub module. Its calls lower to a symbol linked from the compiled
// `native/` crate of the package. The manifest is data, not part of the
// tool binary. It must not leak into cached summaries. The summarizer
// records a call into a native module as an ordinary remote dependency,
// which is cache-safe. The per-function (gc,raise) verdicts are injected at
// fixpoint time (compute_may_gc / compute_may_raise). The reference walkers
// read them. Both steps run on every build.

#[derive(Clone, Debug)]
pub struct NativeFn {
    /// The `#[no_mangle]` symbol in the native crate of the package.
    pub symbol: String,
    pub may_gc: bool,
    pub may_raise: bool,
}

#[derive(Clone, Debug, Default)]
pub struct NativeManifest {
    pub fns: HashMap<(String, String, usize), NativeFn>,
    pub modules: HashSet<String>,
}

pub(crate) static NATIVE_MODULES: std::sync::OnceLock<NativeManifest> = std::sync::OnceLock::new();

/// Install the native-module manifest for this build. Call it once, before
/// compile.
pub fn set_native_manifest(m: NativeManifest) {
    let _ = NATIVE_MODULES.set(m);
}

pub(crate) fn is_native_module(m: &str) -> bool {
    NATIVE_MODULES.get().is_some_and(|nm| nm.modules.contains(m))
}

pub(crate) fn native_fn(module: &str, name: &str, arity: usize) -> Option<&'static NativeFn> {
    NATIVE_MODULES
        .get()?
        .fns
        .get(&(module.to_string(), name.to_string(), arity))
}

// Reachability

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Edge {
    Local(FunName),
    Remote(String, FunName),
    /// A literal M:F in a spawn or apply argument position where the length
    /// of the argument list is not known statically. Every defined arity of
    /// the target is reachable.
    RemoteAnyArity(String, String),
}

pub(crate) fn reachable_funs(
    units: &[ModuleUnit],
    entry_mod: &str,
    entry: &FunName,
    poisoned: &HashMap<String, String>,
    seed_exports: &[String],
) -> CgResult<(HashSet<(String, FunName)>, HashSet<String>)> {
    let defs: HashMap<(&str, &FunName), &summary::FunSummary> = units
        .iter()
        .flat_map(|u| {
            u.summary
                .funs
                .iter()
                .map(move |f| ((u.summary.name.as_str(), &f.name), f))
        })
        .collect();
    let have_module: HashSet<&str> = units.iter().map(|u| u.summary.name.as_str()).collect();

    if !defs.contains_key(&(entry_mod, entry)) {
        if !have_module.contains(entry_mod) {
            return Err(format!(
                "entry module '{}' is not among the compiled modules ({})",
                entry_mod,
                have_module.iter().copied().collect::<Vec<_>>().join(", ")
            ));
        }
        let known: Vec<String> = units
            .iter()
            .find(|u| u.summary.name == entry_mod)
            .map(|u| {
                u.summary
                    .funs
                    .iter()
                    .map(|f| format!("{}/{}", f.name.name, f.name.arity))
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
    // Dynamic dispatch can only name a module through an atom. This covers
    // erlang:apply/3 and the computed M:F(...) calls that erlc emits. A
    // compiled module is a dispatch candidate when its name atom appears as
    // a literal in reachable code (protocol impl_for tables, dispatch lists,
    // pick-a-module functions). Its exports become roots. Modules that are
    // only required statically (Kernel and others) keep full pruning. The
    // reflection export module_info stays out, because the runtime answers
    // it. __info__ compiles, because the get_module_info BIF backs its
    // attributes/compile clauses.
    let module_names: HashSet<&str> = units.iter().map(|u| u.summary.name.as_str()).collect();
    let mod_by_name: HashMap<&str, &ModuleSummary> = units
        .iter()
        .map(|u| (u.summary.name.as_str(), &u.summary))
        .collect();
    let seed_set: HashSet<&str> = seed_exports.iter().map(|s| s.as_str()).collect();
    // Which exports of a candidate become roots depends on how dispatch
    // names functions. A literal name position (`impl.to_string(x)`) seeds
    // only that name/arity. A dynamic name position anywhere (apply with a
    // computed function) seeds every export of the candidate modules. Full
    // seeding applies to Elixir modules only. Erlang infrastructure modules
    // mention the atoms of each other constantly ({global, Name} and
    // others). Full seeding of them will pull in the whole OTP kernel.
    // Behaviour callback dispatch needs a finer rule.
    // TODO(behaviour-seeding): write that rule.
    let mut mentioned: BTreeSet<String> = BTreeSet::new();
    let mut missing_dyn: BTreeSet<String> = BTreeSet::new();
    let mut missing_modules: std::collections::BTreeMap<String, (String, FunName)> =
        Default::default();
    // Atoms that modules with a dynamic function-name position mention.
    // These get full export seeding, because the dispatch can name any
    // function. All other atoms seed only pairs with a literal name.
    let mut mentioned_dyn: BTreeSet<String> = BTreeSet::new();
    let mut dyn_pairs: HashSet<(String, usize)> = HashSet::new();
    // Function names from MFA tuples. Each is seeded at every defined
    // arity, because apply-time extension of the args list makes the
    // literal arity unreliable.
    let mut dyn_any_names: HashSet<String> = HashSet::new();
    // Atoms in module position of {M, F, Args} / {M, Opts} literal tuples
    // (child specs). These are candidates even without an Elixir. prefix.
    let mut tuple_heads: HashSet<String> = HashSet::new();
    let mut dyn_modules: HashSet<String> = HashSet::new();
    let mut module_atoms: HashMap<String, BTreeSet<String>> = HashMap::new();
    let mut seeded: HashSet<(String, FunName)> = HashSet::new();
    // Deltas of the seeding scan. See the incremental-seeding comment in
    // the loop.
    let mut new_mentioned: Vec<String> = Vec::new();
    let mut new_dyn: Vec<String> = Vec::new();
    let mut new_pairs: Vec<(String, usize)> = Vec::new();
    let mut new_any_names: Vec<String> = Vec::new();
    while let Some((module, fname)) = work.pop() {
        if !seen.insert((module.clone(), fname.clone())) {
            continue;
        }
        if seed_set.contains(module.as_str()) && mentioned.insert(module.clone()) {
            new_mentioned.push(module.clone());
        }
        let fun = defs[&(module.as_str(), &fname)];
        for a in &fun.atoms {
            if module_names.contains(a.as_str()) {
                if mentioned.insert(a.clone()) {
                    new_mentioned.push(a.clone());
                }
                module_atoms
                    .entry(module.clone())
                    .or_default()
                    .insert(a.clone());
            } else if a.starts_with("Elixir.") {
                // The atom can name a dispatch target whose beam was never
                // pulled (consolidated protocol impls). The driver decides
                // whether a beam exists for it.
                missing_dyn.insert(a.clone());
            }
        }
        // A (ModuleAtom, FunAtom) pair in consecutive literal call args is
        // MFA-shaped data flow, for example proc_lib:start_link(gen,
        // init_it, ...). Seed every defined arity of the named function.
        for (pm, pf) in &fun.arg_pairs {
            if let Some(target) = mod_by_name.get(pm.as_str()) {
                for df in &target.funs {
                    if df.name.name == *pf && seeded.insert((pm.clone(), df.name.clone())) {
                        work.push((pm.clone(), df.name.clone()));
                    }
                }
            }
        }
        for h in &fun.tuple_heads {
            tuple_heads.insert(h.clone());
        }
        for p in &fun.dyn_pairs {
            if dyn_pairs.insert(p.clone()) {
                new_pairs.push(p.clone());
            }
        }
        for n in &fun.dyn_any_names {
            if dyn_any_names.insert(n.clone()) {
                new_any_names.push(n.clone());
            }
        }
        if fun.fun_dyn {
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
        // Incremental seeding. The inputs (mentioned, mentioned_dyn,
        // dyn_pairs) only grow. A scan of only the deltas reaches the same
        // least fixpoint as a rescan of every mentioned module's exports on
        // every work item.
        // Full seeding stays Elixir-only. Erlang infrastructure modules
        // mention each other constantly. Full seeding of gen or global pulls
        // in all of OTP. Pair seeding (functions with a dynamic name)
        // applies everywhere.
        // Modules of the application itself (--seed-exports) keep all
        // exports once the walk touches them. Configs and templates dispatch
        // into them with atoms built at run time. No static analysis can see
        // those atoms. Untouched modules stay pruned. Each conformance
        // program must not pull in the closures of its siblings.
        while !(new_mentioned.is_empty()
            && new_dyn.is_empty()
            && new_pairs.is_empty()
            && new_any_names.is_empty())
        {
            // A newly mentioned module: seed it per its current full status.
            for a in std::mem::take(&mut new_mentioned) {
                let full = (mentioned_dyn.contains(&a) && a.starts_with("Elixir."))
                    || seed_set.contains(a.as_str());
                let m = mod_by_name[a.as_str()];
                for ex in &m.exports {
                    if ex.name == "module_info" {
                        continue;
                    }
                    if !(full
                        || dyn_pairs.contains(&(ex.name.clone(), ex.arity))
                        || dyn_any_names.contains(&ex.name))
                    {
                        continue;
                    }
                    if defs.contains_key(&(m.name.as_str(), ex))
                        && seeded.insert((m.name.clone(), ex.clone()))
                    {
                        work.push((m.name.clone(), ex.clone()));
                    }
                }
            }
            // A mentioned module upgraded to full status, because a module
            // with dynamic dispatch names it: seed every export.
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
            // A new (fun, arity) pair with a literal name: seed it in every
            // mentioned module that exports it.
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
            // A new function name from an MFA tuple: seed every defined
            // arity of it in every mentioned module.
            for pf in std::mem::take(&mut new_any_names) {
                if pf == "module_info" {
                    continue;
                }
                for a in &mentioned {
                    let m = mod_by_name[a.as_str()];
                    for ex in &m.exports {
                        if ex.name == pf
                            && defs.contains_key(&(m.name.as_str(), ex))
                            && seeded.insert((m.name.clone(), ex.clone()))
                        {
                            work.push((m.name.clone(), ex.clone()));
                        }
                    }
                }
            }
        }
        for edge in &fun.edges {
            let (tmod, tfun) = match edge {
                Edge::Local(f) => (module.clone(), f.clone()),
                Edge::Remote(m, _) if is_bif_module(m) || is_native_module(m) => continue,
                Edge::Remote(m, f) => (m.clone(), f.clone()),
                Edge::RemoteAnyArity(m, _) if is_bif_module(m) || is_native_module(m) => continue,
                Edge::RemoteAnyArity(m, fa) => {
                    if have_module.contains(m.as_str()) {
                        if let Some(target) = mod_by_name.get(m.as_str()) {
                            for df in &target.funs {
                                if df.name.name == *fa {
                                    work.push((m.clone(), df.name.clone()));
                                }
                            }
                        }
                    } else {
                        // A dynamic MFA names an uncompiled module. The
                        // driver can pull its beam.
                        missing_dyn.insert(m.clone());
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
                // Continue the walk, so that one run reports every missing
                // module. The driver pulls them in one batch instead of one
                // per rebuild.
                missing_modules
                    .entry(tmod)
                    .or_insert_with(|| (module.clone(), fname.clone()));
            }
        }
    }
    // Missing modules are not fatal. The driver pulls the ones that it can
    // locate and rebuilds. Callers of the rest get stubs. A stub is loud at
    // run time only if the program reaches it.
    for (m, (rm, rf)) in &missing_modules {
        eprintln!(
            "manac: module '{}' (required by {}:{}/{}) is not among the compiled modules",
            m, rm, rf.name, rf.arity
        );
    }
    // Tuple heads in module position ({M, Opts} / {M, F, Args} child specs)
    // are candidates too, with or without an Elixir. prefix. telemetry_poller
    // is one example.
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

/// Consecutive literal-atom argument pairs in call argument lists. They are
/// MFA-shaped data flow that feeds the behaviour spawn machinery.
pub(crate) fn collect_atom_arg_pairs(e: &Expr, out: &mut Vec<(String, String)>) {
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

/// Literal function names (with arity) in the name positions of dynamic
/// calls. Also reports whether any name position is a computed expression.
pub(crate) fn collect_dyn_names(
    e: &Expr,
    pairs: &mut HashSet<(String, usize)>,
    dyn_any: &mut bool,
    heads: &mut HashSet<String>,
    any_names: &mut HashSet<String>,
) {
    match e {
        Expr::CallDyn { module: _, name, args } => {
            match name.as_ref() {
                Expr::Lit(Literal::Atom(a)) => {
                    pairs.insert((a.clone(), args.len()));
                }
                _ => *dyn_any = true,
            }
            args.iter()
                .for_each(|a| collect_dyn_names(a, pairs, dyn_any, heads, any_names));
        }
        Expr::Call { module, name, args } => {
            // An erlang:apply/3 call that survives to this point has a fully
            // dynamic M and F.
            if module == "erlang" && name == "apply" && args.len() == 3 {
                *dyn_any = true;
            }
            // make_fun(Mod, F, A) with a literal F and A is a callback-cache
            // shape (gen_server). The named function is dispatched
            // dynamically.
            if module == "erlang" && name == "make_fun" && args.len() == 3 {
                if let (Expr::Lit(Literal::Atom(fa)), Expr::Lit(Literal::Int(n))) =
                    (&args[1], &args[2])
                {
                    if *n >= 0 {
                        pairs.insert((fa.clone(), *n as usize));
                    }
                }
            }
            args.iter()
                .for_each(|a| collect_dyn_names(a, pairs, dyn_any, heads, any_names));
        }
        Expr::Lit(_) | Expr::Var(_) | Expr::FunRef { .. } => {}
        Expr::Tuple(items) | Expr::Values(items) => {
            // {Mod, Fun, Args} literal tuples (supervisor child specs,
            // callback tuples) are applied dynamically. The args list is
            // often extended at apply time. For example, the banner
            // {M, F, []} of Plug.Debugger is called with arity 5. So seed
            // the name at every defined arity. The seed stays inert unless
            // the module is a dynamic candidate.
            if items.len() == 3 {
                if let (Expr::Lit(Literal::Atom(m)), Expr::Lit(Literal::Atom(fa))) =
                    (&items[0], &items[1])
                {
                    if static_list_len(&items[2]).is_some() {
                        any_names.insert(fa.clone());
                        heads.insert(m.clone());
                    }
                }
            }
            // {Module, Opts} child specs: Supervisor calls
            // Module.child_spec(Opts) dynamically.
            if items.len() == 2 {
                if let (Expr::Lit(Literal::Atom(m)), Expr::Lit(Literal::Nil))
                | (Expr::Lit(Literal::Atom(m)), Expr::Cons(..)) = (&items[0], &items[1])
                {
                    heads.insert(m.clone());
                    pairs.insert(("child_spec".to_string(), 1));
                }
            }
            items.iter().for_each(|i| collect_dyn_names(i, pairs, dyn_any, heads, any_names))
        }
        Expr::Cons(h, t) => {
            collect_dyn_names(h, pairs, dyn_any, heads, any_names);
            collect_dyn_names(t, pairs, dyn_any, heads, any_names);
        }
        Expr::Fun(f) => collect_dyn_names(&f.body, pairs, dyn_any, heads, any_names),
        Expr::Let { arg, body, .. } => {
            collect_dyn_names(arg, pairs, dyn_any, heads, any_names);
            collect_dyn_names(body, pairs, dyn_any, heads, any_names);
        }
        Expr::LetRec { defs, body } => {
            defs.iter()
                .for_each(|(_, f)| collect_dyn_names(&f.body, pairs, dyn_any, heads, any_names));
            collect_dyn_names(body, pairs, dyn_any, heads, any_names);
        }
        Expr::Apply { args, .. } | Expr::PrimOp { args, .. } => {
            args.iter().for_each(|a| collect_dyn_names(a, pairs, dyn_any, heads, any_names))
        }
        Expr::Case { arg, clauses } => {
            collect_dyn_names(arg, pairs, dyn_any, heads, any_names);
            for c in clauses {
                collect_dyn_names(&c.guard, pairs, dyn_any, heads, any_names);
                collect_dyn_names(&c.body, pairs, dyn_any, heads, any_names);
            }
        }
        Expr::Try { arg, body, handler, .. } => {
            collect_dyn_names(arg, pairs, dyn_any, heads, any_names);
            collect_dyn_names(body, pairs, dyn_any, heads, any_names);
            collect_dyn_names(handler, pairs, dyn_any, heads, any_names);
        }
        Expr::Do(a, b) => {
            collect_dyn_names(a, pairs, dyn_any, heads, any_names);
            collect_dyn_names(b, pairs, dyn_any, heads, any_names);
        }
        Expr::Binary(segs) => segs
            .iter()
            .for_each(|s| collect_dyn_names(&s.value, pairs, dyn_any, heads, any_names)),
        Expr::Map { pairs: mp, update } => {
            for (k, _, v) in mp {
                collect_dyn_names(k, pairs, dyn_any, heads, any_names);
                collect_dyn_names(v, pairs, dyn_any, heads, any_names);
            }
            if let Some(u) = update {
                collect_dyn_names(u, pairs, dyn_any, heads, any_names);
            }
        }
    }
}

/// Every atom literal in an expression tree, including clause patterns.
/// Protocol dispatch matches on module atoms. The result drives apply
/// export seeding in reachable_funs.
pub(crate) fn collect_atoms(e: &Expr, out: &mut BTreeSet<String>) {
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

/// Length of a proper list that the source spells out statically (a cons
/// spine that ends in nil). Returns None when the length is not known.
pub(crate) fn static_list_len(e: &Expr) -> Option<usize> {
    match e {
        Expr::Lit(Literal::Nil) => Some(0),
        Expr::Cons(_, t) => static_list_len(t).map(|n| n + 1),
        _ => None,
    }
}

pub(crate) fn collect_edges(e: &Expr, out: &mut Vec<Edge>, letrec_bound: &mut HashSet<FunName>) {
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
            // A spawn or apply with a literal MFA is dynamic dispatch that
            // reachability can see: spawn(M, F, Args), spawn_opt, apply. The
            // behaviour machinery (proc_lib to gen:init_it) lives on this
            // path.
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

pub(crate) fn is_true_atom(e: &Expr) -> bool {
    matches!(e, Expr::Lit(Literal::Atom(a)) if a == "true")
}
