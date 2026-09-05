use crate::*;

pub(crate) fn is_raise(primop: &str) -> bool {
    matches!(
        primop,
        "match_fail" | "raise" | "raw_raise" | "error" | "exit" | "throw"
    )
}

/// erlang-module BIFs that may raise (shared by the boolean walker and the
/// condenser — one list, no divergence).
pub(crate) fn erlang_may_raise(name: &str, arity: usize) -> bool {
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
            | ("system_flag", 2)
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
            | ("statistics", 1)
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
            | ("pid_to_list", 1)
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
pub(crate) fn erlang_may_gc(name: &str, arity: usize) -> bool {
    matches!(
        (name, arity),
        ("setelement", 3)
            | ("memory", 0)
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
/// Per-function (base, deps) condensations come straight from the module
/// summaries — both effect traversals are pure monotone ORs over
/// set-membership lookups, so `base || deps ∩ set != ∅` is exact — and a
/// worklist fixpoint runs over the condensed graph. MANA_CHECK_ANALYSIS=1
/// cross-checks against the original per-iteration AST walkers (requires
/// every unit to carry its AST — the driver disables the summary cache
/// under the flag).
pub(crate) fn compute_may_gc(units: &[ModuleUnit], reachable: &HashSet<(String, FunName)>) -> GcSet {
    let defs: HashMap<(&str, &FunName), &summary::FunSummary> = units
        .iter()
        .flat_map(|u| {
            u.summary
                .funs
                .iter()
                .map(move |f| ((u.summary.name.as_str(), &f.name), f))
        })
        .collect();
    let conds: HashMap<(String, FunName), (bool, Vec<(String, FunName)>)> = reachable
        .iter()
        .filter_map(|(m, f)| {
            let fs = defs.get(&(m.as_str(), f))?;
            Some(((m.clone(), f.clone()), (fs.gc_base, fs.gc_deps.clone())))
        })
        .collect();
    let conds = inject_native_conds(conds, true);
    let set = effect_fixpoint(conds);
    // native fns were injected only to resolve their callers; they are not
    // compiled functions, so drop them from the result (the reference
    // walker never has them as keys either).
    let set: GcSet = set.into_iter().filter(|(m, _)| !is_native_module(m)).collect();
    if std::env::var_os("MANA_CHECK_ANALYSIS").is_some() {
        if let Some(mods) = all_asts(units) {
            let slow = compute_may_gc_slow(&mods, reachable);
            check_analysis_equal("may_gc", &set, &slow);
        }
    }
    set
}

/// Fixpoint: which reachable functions may raise an exception.
pub(crate) fn compute_may_raise(units: &[ModuleUnit], reachable: &HashSet<(String, FunName)>) -> GcSet {
    let defs: HashMap<(&str, &FunName), &summary::FunSummary> = units
        .iter()
        .flat_map(|u| {
            u.summary
                .funs
                .iter()
                .map(move |f| ((u.summary.name.as_str(), &f.name), f))
        })
        .collect();
    let conds: HashMap<(String, FunName), (bool, Vec<(String, FunName)>)> = reachable
        .iter()
        .filter_map(|(m, f)| {
            let fs = defs.get(&(m.as_str(), f))?;
            Some(((m.clone(), f.clone()), (fs.raise_base, fs.raise_deps.clone())))
        })
        .collect();
    let conds = inject_native_conds(conds, false);
    let set = effect_fixpoint(conds);
    let set: GcSet = set.into_iter().filter(|(m, _)| !is_native_module(m)).collect();
    if std::env::var_os("MANA_CHECK_ANALYSIS").is_some() {
        if let Some(mods) = all_asts(units) {
            let slow = compute_may_raise_slow(&mods, reachable);
            check_analysis_equal("may_raise", &set, &slow);
        }
    }
    set
}

/// Native-module callees appear in summary deps but never in `defs` (they
/// are not compiled). Inject them into the fixpoint with the manifest's
/// per-fn verdict as their base and no further deps, so a compiled caller's
/// dep on a native fn resolves. `gc` selects the may_gc vs may_raise flag.
pub(crate) fn inject_native_conds(
    mut conds: HashMap<(String, FunName), (bool, Vec<(String, FunName)>)>,
    gc: bool,
) -> HashMap<(String, FunName), (bool, Vec<(String, FunName)>)> {
    if NATIVE_MODULES.get().is_none() {
        return conds;
    }
    let mut extra: Vec<((String, FunName), bool)> = Vec::new();
    for (_, deps) in conds.values() {
        for (m, f) in deps {
            if is_native_module(m) {
                let v = native_fn(m, &f.name, f.arity).map_or(true, |nf| if gc { nf.may_gc } else { nf.may_raise });
                extra.push(((m.clone(), f.clone()), v));
            }
        }
    }
    for (k, v) in extra {
        conds.entry(k).or_insert((v, Vec::new()));
    }
    conds
}

/// The parsed ASTs of every unit, or None if any unit came from a summary
/// hit (check mode needs the reference walkers).
pub(crate) fn all_asts(units: &[ModuleUnit]) -> Option<Vec<&Module>> {
    units.iter().map(|u| u.ast.as_ref()).collect()
}

/// Least fixpoint of `f ∈ set ⇔ base(f) || deps(f) ∩ set ≠ ∅` via reverse
/// edges: when a function turns true, only its dependents get revisited.
pub(crate) fn effect_fixpoint(
    conds: HashMap<(String, FunName), (bool, Vec<(String, FunName)>)>,
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

pub(crate) fn check_analysis_equal(what: &str, fast: &GcSet, slow: &GcSet) {
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

pub(crate) fn compute_may_gc_slow(mods: &[&Module], reachable: &HashSet<(String, FunName)>) -> GcSet {
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

pub(crate) fn compute_may_raise_slow(mods: &[&Module], reachable: &HashSet<(String, FunName)>) -> GcSet {
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

pub(crate) fn clause_irrefutable(c: &Clause) -> bool {
    is_true_atom(&c.guard) && c.patterns.iter().all(|p| matches!(p, Pattern::Var(_)))
}

/// Can evaluating `e` raise? Sources: raising primops/BIFs, fun-value
/// applies (badfun), refutable cases (case_clause/function_clause), and
/// calls to may-raise functions. Raises inside a `try` argument are caught.
pub(crate) fn expr_may_raise(
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
            if is_native_module(module) {
                let nr = native_fn(module, name, args.len()).map_or(true, |nf| nf.may_raise);
                return nr
                    || args
                        .iter()
                        .any(|a| expr_may_raise(a, cur_mod, raise_set, letrec_bound));
            }
            if matches!(
                module.as_str(),
                "maps" | "io" | "unicode" | "persistent_term" | "code" | "io_lib"
                    | "logger" | "ets" | "application" | "file" | "prim_file"
                    | "erts_internal"
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
pub(crate) fn expr_may_gc(
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
            if is_native_module(module) {
                let ng = native_fn(module, name, args.len()).map_or(true, |nf| nf.may_gc);
                return ng
                    || args
                        .iter()
                        .any(|a| expr_may_gc(a, cur_mod, gc_set, letrec_bound));
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
                "io" | "unicode" | "re" | "timer" | "file" | "prim_file"
                    | "gen_tcp" | "inet" | "crypto" | "zlib"
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
pub(crate) fn raise_arg_may_gc(
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
pub(crate) fn cond_may_raise(
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
                    | "logger" | "ets" | "application" | "file" | "prim_file"
                    | "erts_internal"
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
pub(crate) fn cond_may_gc(
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
                "io" | "unicode" | "re" | "timer" | "file" | "prim_file"
                    | "gen_tcp" | "inet" | "crypto" | "zlib"
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
pub(crate) fn cond_raise_arg_may_gc(
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
