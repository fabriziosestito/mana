//! Dynamic calls and code introspection: erlang:apply/2, erlang:apply/3,
//! erlang:make_fun/3, module_info, and the `code` module BIFs. The world is
//! closed. Only exported functions of compiled modules are callable. The
//! binary is static, so "loaded" means compiled in. Every other target
//! raises undef, like BEAM without the module loaded.

use super::*;

// The behaviours table holds (module_atom, behaviour_atom) raw-pointer pairs.
extern "C" {
    static __start_mana_behaviours: u64;
    static __stop_mana_behaviours: u64;
}

pub(crate) fn behaviours_of(m: u64) -> Vec<u64> {
    let mut out = Vec::new();
    unsafe {
        let start = &raw const __start_mana_behaviours;
        let stop = &raw const __stop_mana_behaviours;
        let n = (stop as usize - start as usize) / 16;
        for i in 0..n {
            let e = start.add(2 * i);
            // A self-referential pair is the section anchor, not data.
            if *e | TAG_ATOM == m && *e.add(1) != *e {
                out.push(*e.add(1) | TAG_ATOM);
            }
        }
    }
    out
}

// Closed-world export table. Codegen plants one entry per exported function
// in the `mana_exports` ELF section. Atoms are deduplicated program-wide, so
// the lookup is by tagged-word identity.
extern "C" {
    static __start_mana_exports: u64;
    static __stop_mana_exports: u64;
}

/// Export entry (codegen, `mana_exports` section, 5 words): {mod atom, fun
/// atom, arity, c_code, fun_code}. The first two words are raw pointers to
/// the atom structs. `c_code` is the C-ABI wrapper that the runtime calls
/// directly (apply/3, spawn MFA). `fun_code` is the uniform `tailcc` closure
/// shim (`args ++ [fun]`) that fun objects from make_fun/3 carry. Compiled
/// code calls fun code with the tailcc convention. A C pointer in that slot
/// mismatches the callee-pop and jumps into garbage.
pub(crate) struct Export {
    pub(crate) c_code: usize,
    pub(crate) fun_code: usize,
}

pub(crate) fn exports() -> &'static rustc_hash::FxHashMap<(u64, u64, u64), Export> {
    static TABLE: std::sync::OnceLock<rustc_hash::FxHashMap<(u64, u64, u64), Export>> =
        std::sync::OnceLock::new();
    TABLE.get_or_init(|| {
        let mut map = rustc_hash::FxHashMap::default();
        unsafe {
            let start = &raw const __start_mana_exports;
            let stop = &raw const __stop_mana_exports;
            let n = (stop as usize - start as usize) / 40;
            for i in 0..n {
                let e = start.add(5 * i);
                let (m, f, a, c_code, fun_code) = (*e, *e.add(1), *e.add(2), *e.add(3), *e.add(4));
                if m != 0 && f != 0 {
                    map.insert(
                        (m | TAG_ATOM, f | TAG_ATOM, a),
                        Export {
                            c_code: c_code as usize,
                            fun_code: fun_code as usize,
                        },
                    );
                }
            }
        }
        map
    })
}

/// Map from (mod, fun, arity) to the C-ABI code pointer, for the calls of
/// the runtime itself.
pub(crate) fn export_table() -> &'static rustc_hash::FxHashMap<(u64, u64, u64), usize> {
    static TABLE: std::sync::OnceLock<rustc_hash::FxHashMap<(u64, u64, u64), usize>> =
        std::sync::OnceLock::new();
    TABLE.get_or_init(|| exports().iter().map(|(k, v)| (*k, v.c_code)).collect())
}

extern "C" {
    /// Codegen emits this C-ABI trampoline in the entry module. It forwards
    /// the uniform argument words into a `tailcc` fun body.
    fn mana_call_fun(
        ctx: *mut ProcCtx,
        x0: u64,
        x1: u64,
        x2: u64,
        x3: u64,
        x4: u64,
        code: usize,
    ) -> u64;
}

/// Calls the code of a fun object (uniform tailcc ABI) with `argv ++ [fun]`.
pub(crate) unsafe fn call_fun_code(
    ctx: *mut ProcCtx,
    code: usize,
    argv: &[u64],
    fun_term: u64,
) -> u64 {
    let n = argv.len() + 1; // The extra word is the trailing closure.
    let mut x = [0u64; ABI_REGS];
    if n <= ABI_REGS {
        x[..argv.len()].copy_from_slice(argv);
        x[argv.len()] = fun_term;
    } else {
        // Arguments 0..ABI_REGS-2 go in registers. The rest, with the
        // closure, go to the spill area.
        x[..ABI_REGS - 1].copy_from_slice(&argv[..ABI_REGS - 1]);
        let spill = unsafe { (*ctx).argv_spill };
        let rest: Vec<u64> = argv[ABI_REGS - 1..]
            .iter()
            .copied()
            .chain(std::iter::once(fun_term))
            .collect();
        assert!(
            rest.len() <= ARGV_SPILL_WORDS,
            "fun arity exceeds the argument spill"
        );
        for (i, v) in rest.iter().enumerate() {
            unsafe { *spill.add(i) = *v };
        }
    }
    unsafe { mana_call_fun(ctx, x[0], x[1], x[2], x[3], x[4], code) }
}

/// Calls compiled code with unpacked arguments. If `fun_term != 0`, `code`
/// is a fun body (uniform tailcc ABI, through the trampoline, fun term
/// trailing). Otherwise `code` is the C-ABI wrapper of an export (arities
/// 0..8).
pub(crate) unsafe fn call_dynamic(
    ctx: *mut ProcCtx,
    code: usize,
    argv: &[u64],
    fun_term: u64,
) -> Option<u64> {
    if fun_term != 0 {
        return Some(unsafe { call_fun_code(ctx, code, argv, fun_term) });
    }
    type C = *mut ProcCtx;
    let a = argv;
    let r = match (a.len(), fun_term != 0) {
        (0, false) => std::mem::transmute::<usize, extern "C" fn(C) -> u64>(code)(ctx),
        (1, false) => std::mem::transmute::<usize, extern "C" fn(C, u64) -> u64>(code)(ctx, a[0]),
        (2, false) => {
            std::mem::transmute::<usize, extern "C" fn(C, u64, u64) -> u64>(code)(ctx, a[0], a[1])
        }
        (3, false) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64) -> u64>(code)(
            ctx, a[0], a[1], a[2],
        ),
        (4, false) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64) -> u64>(
            code,
        )(ctx, a[0], a[1], a[2], a[3]),
        (5, false) => {
            std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64, u64) -> u64>(code)(
                ctx, a[0], a[1], a[2], a[3], a[4],
            )
        }
        (6, false) => std::mem::transmute::<
            usize,
            extern "C" fn(C, u64, u64, u64, u64, u64, u64) -> u64,
        >(code)(ctx, a[0], a[1], a[2], a[3], a[4], a[5]),
        (7, false) => std::mem::transmute::<
            usize,
            extern "C" fn(C, u64, u64, u64, u64, u64, u64, u64) -> u64,
        >(code)(ctx, a[0], a[1], a[2], a[3], a[4], a[5], a[6]),
        (8, false) => std::mem::transmute::<
            usize,
            extern "C" fn(C, u64, u64, u64, u64, u64, u64, u64, u64) -> u64,
        >(code)(ctx, a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]),
        (0, true) => {
            std::mem::transmute::<usize, extern "C" fn(C, u64) -> u64>(code)(ctx, fun_term)
        }
        (1, true) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64) -> u64>(code)(
            ctx, a[0], fun_term,
        ),
        (2, true) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64) -> u64>(code)(
            ctx, a[0], a[1], fun_term,
        ),
        (3, true) => std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64) -> u64>(
            code,
        )(ctx, a[0], a[1], a[2], fun_term),
        (4, true) => {
            std::mem::transmute::<usize, extern "C" fn(C, u64, u64, u64, u64, u64) -> u64>(code)(
                ctx, a[0], a[1], a[2], a[3], fun_term,
            )
        }
        (5, true) => std::mem::transmute::<
            usize,
            extern "C" fn(C, u64, u64, u64, u64, u64, u64) -> u64,
        >(code)(ctx, a[0], a[1], a[2], a[3], a[4], fun_term),
        (6, true) => std::mem::transmute::<
            usize,
            extern "C" fn(C, u64, u64, u64, u64, u64, u64, u64) -> u64,
        >(code)(ctx, a[0], a[1], a[2], a[3], a[4], a[5], fun_term),
        (7, true) => std::mem::transmute::<
            usize,
            extern "C" fn(C, u64, u64, u64, u64, u64, u64, u64, u64) -> u64,
        >(code)(ctx, a[0], a[1], a[2], a[3], a[4], a[5], a[6], fun_term),
        (8, true) => std::mem::transmute::<
            usize,
            extern "C" fn(C, u64, u64, u64, u64, u64, u64, u64, u64, u64) -> u64,
        >(code)(
            ctx, a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], fun_term,
        ),
        _ => return None,
    };
    Some(r)
}

/// Unpacks a proper list of at most 8 elements. Err(()) means the list is
/// improper or too long.
pub(crate) fn unpack_args(list: u64) -> Result<([u64; 8], usize), ()> {
    let mut v = [0u64; 8];
    let mut n = 0;
    let mut cur = list;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS || n == 8 {
            return Err(());
        }
        let p = (cur & !TAG_MASK) as *const u64;
        unsafe {
            v[n] = *p;
            cur = *p.add(1);
        }
        n += 1;
    }
    Ok((v, n))
}

pub(crate) fn raise_undef(ctx: &mut ProcCtx) -> u64 {
    ctx.exc_class = atom_error();
    ctx.exc_reason = known().undef;
    EXC_SENTINEL
}

/// erlang:apply/3, closed world. Only exported functions of compiled modules
/// are callable. Every other target is undef, like BEAM without the module
/// loaded. Arities above 8 are TODO(apply-arity).
#[no_mangle]
pub extern "C" fn mana_rt_apply3(ctx: *mut ProcCtx, m: u64, f: u64, args: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if m & TAG_MASK != TAG_ATOM || f & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let Ok((argv, n)) = unpack_args(args) else {
        if std::env::var_os("MANA_DEBUG_BADARG").is_some() {
            eprintln!(
                "mana: apply3 bad args list for {}:{} (args {:#x})",
                String::from_utf8_lossy(atom_bytes(m)),
                String::from_utf8_lossy(atom_bytes(f)),
                args
            );
        }
        return raise_badarg(ctx);
    };
    let Some(&code) = export_table().get(&(m, f, n as u64)) else {
        // Dynamic calls into the BIF surface. Everywhere else these calls
        // compile statically. This is the hot set, extended on demand.
        if atom_bytes(m) == b"erlang" {
            match (atom_bytes(f), n) {
                (b"error", 1) | (b"exit", 1) | (b"throw", 1) => {
                    let class = match atom_bytes(f) {
                        b"error" => atom_error(),
                        b"exit" => find_atom("exit").expect("exit atom"),
                        _ => find_atom("throw").expect("throw atom"),
                    };
                    ctx.exc_class = class;
                    ctx.exc_reason = argv[0];
                    return EXC_SENTINEL;
                }
                (b"apply", 3) => return mana_rt_apply3(ctx, argv[0], argv[1], argv[2]),
                (b"apply", 2) => return mana_rt_apply_fun(ctx, argv[0], argv[1]),
                (b"send", 2) | (b"!", 2) => {
                    mana_rt_send(ctx, argv[0], argv[1]);
                    return argv[1];
                }
                (b"self", 0) => return make_pid(ctx.current),
                _ => {}
            }
        }
        // module_info is never compiled. This answers the introspection
        // shapes that callers use: attributes gives the behaviours, module
        // gives the atom.
        if atom_bytes(f) == b"module_info" && module_is_compiled(m) {
            if n == 0 {
                return NIL;
            }
            if n == 1 {
                return module_info_item(ctx, m, argv[0]);
            }
        }
        if std::env::var_os("MANA_DEBUG_UNDEF").is_some() {
            eprintln!(
                "mana: undef {}:{}/{}",
                String::from_utf8_lossy(atom_bytes(m)),
                String::from_utf8_lossy(atom_bytes(f)),
                n
            );
        }
        return raise_undef(ctx);
    };
    unsafe { call_dynamic(ctx, code, &argv[..n], 0).unwrap_or_else(|| raise_undef(ctx)) }
}

/// Introspection items shared by the module_info fallback in apply3 and by
/// erlang:get_module_info/2. Compiled `__info__/1` clauses call the latter.
pub(crate) fn module_info_item(ctx: &mut ProcCtx, m: u64, item: u64) -> u64 {
    match atom_bytes(item) {
        b"module" => m,
        b"attributes" => {
            // The result is one [{behaviour, [B]}] per declared behaviour.
            let bs = behaviours_of(m);
            let saved = ctx.roots_head;
            let mut fr = [0u64, 2, NIL, 0];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            for &b in bs.iter().rev() {
                let inner = alloc_nursery(ctx, 2);
                unsafe {
                    *inner = b;
                    *inner.add(1) = NIL;
                }
                let t = alloc_nursery(ctx, 3);
                unsafe {
                    *t = (2 << 8) | KIND_TUPLE;
                    *t.add(1) = atom_intern(b"behaviour");
                    *t.add(2) = inner as u64 | TAG_CONS;
                }
                fr[3] = t as u64;
                let cell = alloc_nursery(ctx, 2);
                unsafe {
                    *cell = fr[3];
                    *cell.add(1) = fr[2];
                }
                fr[2] = cell as u64 | TAG_CONS;
            }
            ctx.roots_head = saved;
            fr[2]
        }
        b"functions" | b"exports" => {
            // The result holds the {name, arity} pairs from the export table.
            // The sort by name and arity makes the order deterministic. BEAM
            // does not specify the order.
            let mut fs: Vec<(u64, u64)> = export_table()
                .keys()
                .filter(|(km, _, _)| *km == m)
                .map(|(_, kf, ka)| (*kf, *ka))
                .collect();
            fs.sort_by(|a, b| atom_bytes(a.0).cmp(atom_bytes(b.0)).then(a.1.cmp(&b.1)));
            let saved = ctx.roots_head;
            let mut fr = [0u64, 2, NIL, 0];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            for &(f, a) in fs.iter().rev() {
                let t = alloc_nursery(ctx, 3);
                unsafe {
                    *t = (2 << 8) | KIND_TUPLE;
                    *t.add(1) = f;
                    *t.add(2) = ((a << 3) as u64) | TAG_SMALL;
                }
                fr[3] = t as u64;
                let cell = alloc_nursery(ctx, 2);
                unsafe {
                    *cell = fr[3];
                    *cell.add(1) = fr[2];
                }
                fr[2] = cell as u64 | TAG_CONS;
            }
            ctx.roots_head = saved;
            fr[2]
        }
        _ => NIL,
    }
}

/// erlang:get_module_info/2. Compiled `__info__/1` clauses reach this from
/// their attributes and compile arms. The useful arms answer. The rest
/// return [].
#[no_mangle]
pub extern "C" fn mana_rt_get_module_info(ctx: *mut ProcCtx, m: u64, item: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if m & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    module_info_item(ctx, m, item)
}

/// erlang:apply/2 calls a fun value with a runtime argument list.
#[no_mangle]
pub extern "C" fn mana_rt_apply_fun(ctx: *mut ProcCtx, fun: u64, args: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Ok((argv, n)) = unpack_args(args) else {
        return raise_badarg(ctx);
    };
    if fun & TAG_MASK != TAG_BOXED || fun == 0 {
        return raise_badarg(ctx);
    }
    let header = unsafe { *(fun as *const u64) };
    if header & 0xff != KIND_FUN || (header >> 8) & 0xff != n as u64 {
        // A wrong kind or arity raises a bare badarg. A badarity tuple
        // carries a stacktrace-shaped payload that the runtime does not
        // build. TODO(stacktraces) tracks this.
        return raise_badarg(ctx);
    }
    let code = unsafe { *(fun as *const u64).add(1) } as usize;
    unsafe { call_dynamic(ctx, code, &argv[..n], fun).unwrap_or_else(|| raise_badarg(ctx)) }
}

// Code introspection. The binary is static, so "loaded" means compiled in.

pub(crate) fn module_is_compiled(m: u64) -> bool {
    if m & TAG_MASK == TAG_ATOM && is_cut_module(atom_bytes(m)) {
        return true;
    }
    // The set of module atoms with at least one export, built once. This
    // path serves code:ensure_loaded and function_exported?, which Plug and
    // Phoenix call per request. A scan of the whole export table on each
    // call cost ~4% of a request.
    static MODULES: std::sync::OnceLock<rustc_hash::FxHashSet<u64>> = std::sync::OnceLock::new();
    MODULES
        .get_or_init(|| export_table().keys().map(|&(em, _, _)| em).collect())
        .contains(&m)
}

/// Modules that the compiler implements natively (BIF cuts) or compiles as
/// runtime raises. They have no export-table entries, but they "exist" for
/// code:ensure_loaded and is_loaded. Phoenix.PubSub probes :persistent_term
/// this way. This list MUST stay in sync with is_bif_module in codegen and
/// with the unimplemented-raise list.
pub(crate) fn is_cut_module(name: &[u8]) -> bool {
    matches!(
        name,
        b"erlang"
            | b"maps"
            | b"io"
            | b"unicode"
            | b"persistent_term"
            | b"code"
            | b"io_lib"
            | b"logger"
            | b"ets"
            | b"application"
            | b"prim_file"
            | b"file"
            | b"math"
            | b"re"
            | b"timer"
            | b"gen_tcp"
            | b"inet"
            | b"crypto"
            | b"erts_internal"
            | b"elixir_erl"
            | b"erl_eval"
            | b"beam_lib"
            | b"global"
            | b"global_group"
            | b"net_kernel"
            | b"zlib"
    )
}

/// erlang:module_loaded/1, closed world. A compiled or cut module is loaded.
#[no_mangle]
pub extern "C" fn mana_rt_module_loaded(ctx: *mut ProcCtx, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if m & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    if module_is_compiled(m) {
        known().true_a
    } else {
        known().false_a
    }
}

/// code:is_loaded/1 returns {file, "native"} or false. Ecto.Queryable.Atom
/// probes schema modules through this.
#[no_mangle]
pub extern "C" fn mana_rt_code_is_loaded(ctx: *mut ProcCtx, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if m & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    if !module_is_compiled(m) {
        return known().false_a;
    }
    // {file, "native"} with a charlist. This is the shape that
    // code:is_loaded returns for preloaded or static code.
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &b in b"native".iter().rev() {
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = ((b as u64) << 3) | TAG_SMALL;
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
    }
    let t = alloc_nursery(ctx, 3);
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = atom_intern(b"file");
        *t.add(2) = fr[2];
    }
    ctx.roots_head = saved;
    t as u64
}

/// code:lib_dir/1 and code:priv_dir/1. The --app boot generator stores the
/// build-time directory of each application under env {:mana_app_dirs, App}
/// as a binary. An unknown app gets {error, bad_name}, like BEAM.
#[no_mangle]
pub extern "C" fn mana_rt_code_app_dir(ctx: *mut ProcCtx, app: u64, is_priv: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    if app & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctxr);
    }
    let tab = atom_intern(b"mana_app_dirs");
    let miss = known().undefined;
    let hit = mana_rt_app_get_env(ctx, tab, app, miss, 1);
    let ctxr = unsafe { &mut *ctx };
    if hit == known().undefined {
        let t = alloc_nursery(ctxr, 3);
        unsafe {
            *t = (2 << 8) | KIND_TUPLE;
            *t.add(1) = atom_error();
            *t.add(2) = atom_intern(b"bad_name");
        }
        return t as u64;
    }
    // {ok, DirBin} becomes a charlist. priv_dir appends "/priv".
    let dir = unsafe { *((hit & !TAG_MASK) as *const u64).add(2) };
    let mut bytes = bin_bytes(dir).to_vec();
    if is_priv != 0 {
        bytes.extend_from_slice(b"/priv");
    }
    bytes_to_charlist(ctxr, &bytes)
}

/// code:ensure_loaded/1 returns {module, M} or {error, nofile}. The tuples
/// are eternal. They are tiny, and the call sites bound their number.
#[no_mangle]
pub extern "C" fn mana_rt_code_ensure_loaded(ctx: *mut ProcCtx, m: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if m & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let (tag, val) = if module_is_compiled(m) {
        (known().module, m)
    } else {
        (atom_error(), known().nofile)
    };
    let p = alloc_space(3);
    ctx.global.eternal.lock().push((p as usize, false));
    unsafe {
        *p = (2 << 8) | KIND_TUPLE;
        *p.add(1) = tag;
        *p.add(2) = val;
    }
    p as u64
}

/// erlang:function_exported/3. module_loaded/1 shares the table.
#[no_mangle]
pub extern "C" fn mana_rt_function_exported(_ctx: *mut ProcCtx, m: u64, f: u64, a: u64) -> u64 {
    if a & TAG_MASK != TAG_SMALL {
        return known().false_a;
    }
    let arity = (a as i64 >> 3) as u64;
    if export_table().contains_key(&(m, f, arity)) {
        known().true_a
    } else {
        known().false_a
    }
}

extern "C" {
    /// Codegen emits this uniform `tailcc` fun body. It raises undef. It is
    /// the code pointer for make_fun/3 of a function that is not compiled.
    static mana_fun_undef: u8;
}

pub(crate) fn make_fun_undef_code() -> usize {
    unsafe { &raw const mana_fun_undef as usize }
}

/// erlang:make_fun/3 builds a fun value for an exported function. The
/// closure convention appends the fun term as a trailing argument. The code
/// pointer is the `fun_code` shim of the export (see `Export`). A function
/// that is not compiled gets the undef body.
#[no_mangle]
pub extern "C" fn mana_rt_make_fun(ctx: *mut ProcCtx, m: u64, f: u64, arity: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if m & TAG_MASK != TAG_ATOM || f & TAG_MASK != TAG_ATOM || arity & TAG_MASK != TAG_SMALL {
        return raise_badarg(ctx);
    }
    let a = (arity as i64 >> 3) as u64;
    let code = exports()
        .get(&(m, f, a))
        .map(|e| e.fun_code)
        .unwrap_or_else(|| {
            if std::env::var_os("MANA_DEBUG_UNDEF").is_some() {
                eprintln!(
                    "mana: make_fun miss {}:{}/{}",
                    String::from_utf8_lossy(atom_bytes(m)),
                    String::from_utf8_lossy(atom_bytes(f)),
                    a
                );
            }
            make_fun_undef_code()
        });
    let p = alloc_nursery(ctx, 2);
    unsafe {
        *p = (a << 8) | KIND_FUN; // The fun has zero captures.
        *p.add(1) = code as u64;
    }
    p as u64
}
