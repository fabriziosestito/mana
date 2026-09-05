//! System BIFs: environment, hashing, process and system flags, memory and
//! statistics reports, time, `system_info/1`, external commands, and timers.
//! Values that BEAM computes from VM internals are approximations here. The
//! doc of each function states where the value diverges from BEAM. The
//! timer thread runs outside the stop-the-world protocol. It never touches
//! process or scheduler state. It only enqueues deliveries that schedulers
//! drain at a safepoint.

use super::*;

/// os:getenv/1. In os.erl this is a nif_error stub. On BEAM it is a real BIF.
#[no_mangle]
pub extern "C" fn mana_rt_os_getenv(ctx: *mut ProcCtx, name: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut bytes = Vec::new();
    if chardata_flatten(name, &mut bytes).is_err() {
        return raise_badarg(ctx);
    }
    let Ok(name) = String::from_utf8(bytes) else {
        return raise_badarg(ctx);
    };
    match std::env::var(&name) {
        Ok(v) => bytes_to_byte_list(ctx, v.as_bytes()),
        Err(_) => known().false_a,
    }
}

/// erlang:iolist_size/1.
#[no_mangle]
pub extern "C" fn mana_rt_iolist_size(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut out = Vec::new();
    if iolist_flatten(t, &mut out).is_err() {
        return raise_badarg(ctx);
    }
    ((out.len() as i64) << 3) as u64 | TAG_SMALL
}

/// erlang:phash2/1,2: a structural term hash. Values are stable for this
/// runtime. They do not match the phash2 values of BEAM. This is a documented
/// divergence. Callers use the hash for sharding and ids, not for persisted
/// values.
pub(crate) fn phash2_term(t: u64, h: &mut u64) {
    fn mix(h: &mut u64, v: u64) {
        *h = (*h ^ v).wrapping_mul(0x100000001b3); // FNV-style mix
    }
    match t & TAG_MASK {
        TAG_SMALL => mix(h, t),
        TAG_ATOM => {
            mix(h, 2);
            for &b in atom_bytes(t) {
                mix(h, b as u64);
            }
        }
        _ if t == NIL => mix(h, 3),
        TAG_CONS => {
            let mut cur = t;
            while cur & TAG_MASK == TAG_CONS {
                let p = (cur & !TAG_MASK) as *const u64;
                phash2_term(unsafe { *p }, h);
                cur = unsafe { *p.add(1) };
            }
            mix(h, 4);
            if cur != NIL {
                phash2_term(cur, h);
            }
        }
        TAG_BOXED if t != 0 => unsafe {
            let p = t as *const u64;
            let kind = *p & 0xff;
            // Views hash as binaries. Equal bytes must hash equal.
            mix(h, 5 + if kind == KIND_SUBBIN { KIND_BIN } else { kind });
            match kind {
                KIND_TUPLE | KIND_MAP => {
                    let words = payload_words(*p);
                    for i in 1..=words {
                        phash2_term(*p.add(i), h);
                    }
                }
                KIND_FLOAT => mix(h, *p.add(1)),
                KIND_BIN | KIND_SUBBIN => {
                    for &b in bin_bytes(t) {
                        mix(h, b as u64);
                    }
                }
                KIND_BIGNUM => {
                    let (neg, mag) = bignum_parts(t).unwrap();
                    mix(h, neg as u64);
                    for &l in mag {
                        mix(h, l);
                    }
                }
                _ => mix(h, *p),
            }
        },
        _ => mix(h, t), // pids and other immediates hash by identity word
    }
}

#[no_mangle]
pub extern "C" fn mana_rt_phash2(ctx: *mut ProcCtx, t: u64, range: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let modulus = if range == 0 {
        1u64 << 27 // the default range of phash2/1
    } else {
        if range & TAG_MASK != TAG_SMALL || (range as i64 >> 3) <= 0 {
            return raise_badarg(ctx);
        }
        (range as i64 >> 3) as u64
    };
    let mut h: u64 = 0xcbf29ce484222325;
    phash2_term(t, &mut h);
    (((h % modulus) as i64) << 3) as u64 | TAG_SMALL
}

/// erlang:unique_integer/0,1: a global counter. It gives uniqueness only. A
/// counter that counts up also satisfies the positive and monotonic option
/// atoms.
pub(crate) static UNIQUE_INTEGER: std::sync::atomic::AtomicI64 = std::sync::atomic::AtomicI64::new(1);

#[no_mangle]
pub extern "C" fn mana_rt_unique_integer(_ctx: *mut ProcCtx) -> u64 {
    let v = UNIQUE_INTEGER.fetch_add(1, Ordering::Relaxed);
    ((v << 3) as u64) | TAG_SMALL
}

/// erlang:is_record/3: true for a tuple of arity Size whose first element is
/// Tag.
#[no_mangle]
pub extern "C" fn mana_rt_is_record(t: u64, tag: u64, size: u64) -> u64 {
    if size & TAG_MASK != TAG_SMALL || t & TAG_MASK != TAG_BOXED || t == 0 {
        return known().false_a;
    }
    let want = (size as i64 >> 3) as usize;
    unsafe {
        let p = t as *const u64;
        if *p & 0xff != KIND_TUPLE || (*p >> 8) as usize != want || want == 0 {
            return known().false_a;
        }
        if *p.add(1) == tag {
            known().true_a
        } else {
            known().false_a
        }
    }
}

/// erlang:process_flag/2. The trap_exit flag is real. The scheduler tuning
/// flags are accepted no-ops that return plausible old values. Unknown flags
/// raise badarg.
#[no_mangle]
pub extern "C" fn mana_rt_process_flag(ctx: *mut ProcCtx, flag: u64, value: u64) -> u64 {
    let ctxp = ctx;
    let ctx = unsafe { &mut *ctx };
    if flag & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    match atom_bytes(flag) {
        b"trap_exit" => mana_rt_trap_exit(ctxp, value),
        b"priority" => atom_intern(b"normal"),
        b"message_queue_data" => atom_intern(b"off_heap"),
        b"min_heap_size" | b"min_bin_vheap_size" | b"max_heap_size"
        | b"fullsweep_after" => (0 << 3) | TAG_SMALL,
        b"sensitive" | b"error_handler" => known().false_a,
        _ => raise_badarg(ctx),
    }
}

/// erlang:system_flag/2: accepted no-ops that return plausible old values.
/// These VM tuning knobs have no meaning in this runtime. Phoenix sets
/// backtrace_depth at application start.
#[no_mangle]
pub extern "C" fn mana_rt_system_flag(ctx: *mut ProcCtx, flag: u64, _value: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if flag & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    match atom_bytes(flag) {
        b"backtrace_depth" | b"fullsweep_after" | b"min_heap_size"
        | b"min_bin_vheap_size" | b"max_heap_size" => (8 << 3) | TAG_SMALL,
        _ => raise_badarg(ctx),
    }
}

/// persistent_term:info/0: returns #{count => N, memory => Bytes}. The memory
/// value is an estimate.
#[no_mangle]
pub extern "C" fn mana_rt_pt_info(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let count = PERSISTENT_TERMS
        .lock()
        .unwrap()
        .as_ref()
        .map(|m| m.len() as u64)
        .unwrap_or(0);
    let t = alloc_nursery(ctx, 5);
    unsafe {
        *t = (2 << 8) | KIND_MAP;
        // A flatmap is sorted. Atoms sort by name, so count comes before memory.
        *t.add(1) = atom_intern(b"count");
        *t.add(2) = (count << 3) | TAG_SMALL;
        *t.add(3) = atom_intern(b"memory");
        *t.add(4) = ((count * 64) << 3) | TAG_SMALL;
    }
    t as u64
}

/// erlang:memory/0: allocator statistics mapped onto the key set of BEAM.
/// The values come from the heaps of this runtime (old space plus nurseries).
/// The absolute numbers diverge from BEAM. This is documented. Consumers
/// chart trends, not identities.
#[no_mangle]
pub extern "C" fn mana_rt_memory(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let g = ctx.global;
    let old_bytes = g.old_used.load(Ordering::Relaxed) as u64 * 8;
    let nursery_bytes = g.n_scheds as u64 * ctx.nursery_words as u64 * 8;
    let processes = old_bytes + nursery_bytes;
    let atom = interned_atom_count() * 64;
    let system = atom + 1_048_576;
    let total = processes + system;
    let pairs: [(&[u8], u64); 9] = [
        (b"total", total),
        (b"processes", processes),
        (b"processes_used", processes),
        (b"system", system),
        (b"atom", atom),
        (b"atom_used", atom),
        (b"binary", 0),
        (b"code", 0),
        (b"ets", 0),
    ];
    // Build [{k, v} | ...] back to front. Both the list and the fresh tuple
    // must be frame-rooted across the cons allocation. A Rust local is not a
    // GC root, and the cons allocation can move the tuple.
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for (k, v) in pairs.iter().rev() {
        let t = alloc_nursery(ctx, 3);
        unsafe {
            *t = (2 << 8) | KIND_TUPLE;
            *t.add(1) = atom_intern(k);
            *t.add(2) = (v << 3) | TAG_SMALL;
        }
        fr[3] = t as u64;
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = fr[3];
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
        fr[3] = NIL;
    }
    ctx.roots_head = saved;
    fr[2]
}

/// erlang:statistics/1: only the keys that telemetry_poller reads.
#[no_mangle]
pub extern "C" fn mana_rt_statistics(ctx: *mut ProcCtx, item: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if item & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    match atom_bytes(item) {
        // Run queues drain at safepoints. A snapshot of 0 is accurate enough
        // for poller charts.
        b"total_run_queue_lengths" | b"total_run_queue_lengths_all" | b"run_queue" => TAG_SMALL,
        _ => raise_badarg(ctx),
    }
}

// Time

pub(crate) fn monotonic_epoch() -> std::time::Instant {
    static EPOCH: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
    *EPOCH.get_or_init(std::time::Instant::now)
}

/// Converts nanoseconds to the requested unit. The unit is an atom or an
/// integer in hertz.
pub(crate) fn in_time_unit(ctx: &mut ProcCtx, nanos: i128, unit: u64) -> u64 {
    let v: i128 = if unit & TAG_MASK == TAG_SMALL {
        let hz = unit as i64 >> 3;
        if hz <= 0 {
            return raise_badarg(ctx);
        }
        nanos * hz as i128 / 1_000_000_000
    } else if unit & TAG_MASK == TAG_ATOM {
        match atom_bytes(unit) {
            b"native" | b"nanosecond" | b"nano_seconds" => nanos,
            b"microsecond" | b"micro_seconds" => nanos / 1_000,
            b"millisecond" | b"milli_seconds" => nanos / 1_000_000,
            b"second" | b"seconds" => nanos / 1_000_000_000,
            b"perf_counter" => nanos,
            _ => return raise_badarg(ctx),
        }
    } else {
        return raise_badarg(ctx);
    };
    let neg = v < 0;
    let uv = v.unsigned_abs();
    let mag = bigint::normalize(vec![uv as u64, (uv >> 64) as u64]);
    make_int_mag(ctx, neg && !mag.is_empty(), &mag)
}

/// erlang:fun_info/2. Closures carry no module or name metadata. The arity
/// and env items answer truthfully. Every other item is undefined. Callers
/// only pass the {Item, Value} shape through, for example the initial_call
/// bookkeeping of Agent.
#[no_mangle]
pub extern "C" fn mana_rt_fun_info(ctx: *mut ProcCtx, fun: u64, item: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if fun & TAG_MASK != TAG_BOXED || fun == 0 || item & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let header = unsafe { *(fun as *const u64) };
    if header & 0xff != KIND_FUN {
        return raise_badarg(ctx);
    }
    let value = match atom_bytes(item) {
        b"arity" => ((((header >> 8) & 0xff) << 3) as u64) | TAG_SMALL,
        b"env" => NIL,
        // Closures carry no MFA metadata, so every fun reports as local.
        // telemetry:attach warns and proceeds on local. BEAM answers external
        // for `fun M:F/A` captures. This is a documented divergence.
        b"type" => atom_intern(b"local"),
        _ => known().undefined,
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, item, value];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let t = alloc_nursery(ctx, 3);
    ctx.roots_head = saved;
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = fr[2];
        *t.add(2) = fr[3];
    }
    t as u64
}

/// erlang:fun_info_mfa/1. Closures carry no MFA metadata. The arity is real.
/// The module and the name are undefined. Callers only display them.
#[no_mangle]
pub extern "C" fn mana_rt_fun_info_mfa(ctx: *mut ProcCtx, fun: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if fun & TAG_MASK != TAG_BOXED || fun == 0 {
        return raise_badarg(ctx);
    }
    let header = unsafe { *(fun as *const u64) };
    if header & 0xff != KIND_FUN {
        return raise_badarg(ctx);
    }
    let arity = (header >> 8) & 0xff;
    let t = alloc_nursery(ctx, 4);
    unsafe {
        *t = (3 << 8) | KIND_TUPLE;
        *t.add(1) = known().undefined;
        *t.add(2) = known().undefined;
        *t.add(3) = (arity << 3) | TAG_SMALL;
    }
    t as u64
}

/// erlang:is_process_alive/1.
#[no_mangle]
pub extern "C" fn mana_rt_is_process_alive(ctx: *mut ProcCtx, pid: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if pid & 0xF != PID_TAG4 {
        return raise_badarg(ctx);
    }
    if proc_ref(ctx.global, (pid >> 4) as usize).is_some() {
        known().true_a
    } else {
        known().false_a
    }
}

/// erlang:monotonic_time/1. The unit 'native' is one nanosecond here.
#[no_mangle]
pub extern "C" fn mana_rt_monotonic_time(ctx: *mut ProcCtx, unit: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let nanos = monotonic_epoch().elapsed().as_nanos() as i128;
    in_time_unit(ctx, nanos, unit)
}

/// erlang:system_time/1: the true Unix epoch. Nanosecond magnitudes come back
/// as bignums.
#[no_mangle]
pub extern "C" fn mana_rt_system_time(ctx: *mut ProcCtx, unit: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    // Absolute nanoseconds since the Unix epoch exceed the small range. They
    // come back as bignums. An earlier 2020 offset put every absolute wall
    // clock reading 50 years in the past. That caused the 1976 Date header.
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos() as i128)
        .unwrap_or(0);
    in_time_unit(ctx, nanos, unit)
}

/// erlang:convert_time_unit/3. The from and to arguments are unit terms.
#[no_mangle]
pub extern "C" fn mana_rt_convert_time_unit(
    ctx: *mut ProcCtx,
    t: u64,
    from: u64,
    to: u64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let v: i128 = if t & TAG_MASK == TAG_SMALL {
        (t as i64 >> 3) as i128
    } else if let Some((neg, mag)) = bignum_parts(t) {
        // Wall clock magnitudes fit in two limbs.
        if mag.len() > 2 {
            return raise_badarg(ctx);
        }
        let uv = mag[0] as i128
            | ((*mag.get(1).unwrap_or(&0) as i128) << 64);
        if neg { -uv } else { uv }
    } else {
        return raise_badarg(ctx);
    };
    let nanos: i128 = if from & TAG_MASK == TAG_SMALL {
        let hz = from as i64 >> 3;
        if hz <= 0 {
            return raise_badarg(ctx);
        }
        v * 1_000_000_000 / hz as i128
    } else {
        match atom_bytes(from) {
            b"native" | b"nanosecond" | b"nano_seconds" => v,
            b"microsecond" | b"micro_seconds" => v * 1_000,
            b"millisecond" | b"milli_seconds" => v * 1_000_000,
            b"second" | b"seconds" => v * 1_000_000_000,
            _ => return raise_badarg(ctx),
        }
    };
    in_time_unit(ctx, nanos, to)
}

/// erlang:system_info/1: the closed-world answer sheet. Extend it when new
/// callers appear. An unknown item raises badarg, so a gap is loud.
#[no_mangle]
pub extern "C" fn mana_rt_system_info(ctx: *mut ProcCtx, item: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if item & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let cpus = || {
        std::thread::available_parallelism()
            .map(|n| n.get() as u64)
            .unwrap_or(1)
    };
    match atom_bytes(item) {
        b"endian" => find_atom("little").unwrap_or(NIL),
        b"otp_release" => bytes_to_charlist(ctx, b"26"),
        b"system_version" => bytes_to_charlist(ctx, b"mana\n"),
        b"version" => bytes_to_charlist(ctx, b"14.0"),
        b"emu_flavor" => atom_intern(b"emu"),
        b"os_type" => {
            let t = alloc_nursery(ctx, 3);
            unsafe {
                *t = (2 << 8) | KIND_TUPLE;
                *t.add(1) = atom_intern(b"unix");
                *t.add(2) = atom_intern(b"linux");
            }
            t as u64
        }
        b"logical_processors" | b"logical_processors_available"
        | b"logical_processors_online" => ((cpus() << 3) as u64) | TAG_SMALL,
        b"schedulers" | b"schedulers_online" => {
            let n = ctx.global.n_scheds as u64;
            ((n << 3) as u64) | TAG_SMALL
        }
        // The system_counts of telemetry_poller. The counts are real where
        // they are cheap. The BEAM-only limits are plausible constants.
        b"process_count" => {
            let n = ctx.global.procs.read().iter().filter(|s| s.is_some()).count() as u64;
            ((n << 3) as u64) | TAG_SMALL
        }
        b"atom_count" => ((interned_atom_count() << 3) as u64) | TAG_SMALL,
        b"port_count" => TAG_SMALL, // 0
        b"process_limit" => ((262_144u64 << 3) as u64) | TAG_SMALL,
        b"atom_limit" => ((1_048_576u64 << 3) as u64) | TAG_SMALL,
        b"port_limit" => ((65_536u64 << 3) as u64) | TAG_SMALL,
        b"os_monotonic_time_source" => {
            // A property list. The repeated_measurement of benchee reads it.
            let cell = alloc_nursery(ctx, 2);
            let t = alloc_nursery(ctx, 3);
            unsafe {
                *t = (2 << 8) | KIND_TUPLE;
                *t.add(1) = atom_intern(b"resolution");
                *t.add(2) = ((1_000_000_000u64) << 3) | TAG_SMALL;
                *cell = t as u64;
                *cell.add(1) = NIL;
            }
            cell as u64 | TAG_CONS
        }
        _ => raise_badarg(ctx),
    }
}

/// Elixir.System.cmd/2,3 (native override). Runs a command, captures stdout,
/// and returns {Output, ExitCode}. The call is synchronous on the scheduler
/// thread of the caller. This is acceptable for system probing. Real port
/// support is TODO(port).
#[no_mangle]
pub extern "C" fn mana_rt_system_cmd(ctx: *mut ProcCtx, cmd: u64, args: u64, _opts: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some(cmd_b) = term_to_source(cmd) else {
        return raise_badarg(ctx);
    };
    let Ok(cmd_s) = String::from_utf8(cmd_b) else {
        return raise_badarg(ctx);
    };
    let mut argv: Vec<String> = Vec::new();
    let mut cur = args;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return raise_badarg(ctx);
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        let Some(b) = term_to_source(h) else {
            return raise_badarg(ctx);
        };
        let Ok(s) = String::from_utf8(b) else {
            return raise_badarg(ctx);
        };
        argv.push(s);
        cur = unsafe { *p.add(1) };
    }
    let out = std::process::Command::new(&cmd_s).args(&argv).output();
    let (bytes, code): (Vec<u8>, i64) = match out {
        Ok(o) => (o.stdout, o.status.code().unwrap_or(1) as i64),
        Err(_) => (Vec::new(), 127),
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, 0];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    fr[2] = bytes_to_new_bin(ctx, &bytes);
    let t = alloc_nursery(ctx, 3);
    ctx.roots_head = saved;
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = fr[2];
        *t.add(2) = ((code << 3) as u64) | TAG_SMALL;
    }
    t as u64
}

/// timer:tc. Times a fun application in microseconds and returns
/// {Us, Result}.
#[no_mangle]
pub extern "C" fn mana_rt_timer_tc(ctx: *mut ProcCtx, fun: u64, args: u64) -> u64 {
    let ctxr = unsafe { &mut *ctx };
    let t0 = monotonic_epoch().elapsed();
    let v = mana_rt_apply_fun(ctx, fun, args);
    if v == EXC_SENTINEL {
        return v;
    }
    let us = (monotonic_epoch().elapsed() - t0).as_micros() as i64;
    let ctxr = unsafe { &mut *ctx };
    let saved = ctxr.roots_head;
    let mut fr = [0u64, 1, v];
    fr[0] = saved;
    ctxr.roots_head = fr.as_ptr() as u64;
    let t = alloc_nursery(ctxr, 3);
    ctxr.roots_head = saved;
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = ((us << 3) as u64) | TAG_SMALL;
        *t.add(2) = fr[2];
    }
    let _ = ctxr;
    t as u64
}

// Timers (send_after / start_timer / cancel_timer)
//
// A dedicated timer thread sleeps until the nearest deadline. To deliver, it
// pushes to the ingress of the target and wakes its scheduler. This is the
// same cross-thread path that sends use. Messages are eternal deep copies.
// They are immortal, so the timer heap needs no GC integration. Timer volume
// is low on our paths. TODO(timer-gc): GC integration for the timer heap.

pub(crate) struct TimerEntry {
    pub(crate) deadline: std::time::Instant,
    pub(crate) ref_id: u64,
    pub(crate) dest_pid: Option<usize>,
    pub(crate) dest_name: Option<u64>, // a registered-name atom, resolved at fire time
    pub(crate) msg: u64,               // an eternal copy
}

pub(crate) struct Timers {
    pub(crate) entries: Vec<TimerEntry>,
    pub(crate) global: &'static Global,
    pub(crate) thread_started: bool,
}

pub(crate) static TIMERS: std::sync::Mutex<Option<Timers>> = std::sync::Mutex::new(None);

pub(crate) static TIMER_CV: std::sync::Condvar = std::sync::Condvar::new();

/// The timer thread is outside the STW protocol. It must not change process
/// or scheduler state directly. A state flip in the middle of a major GC
/// corrupts the run queues. The thread only enqueues (pid, msg) here and
/// wakes a scheduler. Schedulers drain the queue at their loop top, which is
/// a safepoint.
pub(crate) static TIMER_DELIVERIES: SegQueue<(usize, u64)> = SegQueue::new();

pub(crate) fn deliver_cross_thread(g: &'static Global, id: usize, msg: u64) {
    TIMER_DELIVERIES.push((id, msg));
    for s in 0..g.n_scheds {
        wake_sched(g, s);
    }
}

/// The scheduler loop calls this next to a safepoint.
pub(crate) fn drain_timer_deliveries(ctx: &mut ProcCtx) {
    while let Some((id, msg)) = TIMER_DELIVERIES.pop() {
        push_and_wake(ctx, id, msg);
    }
}

pub(crate) fn timer_thread() {
    loop {
        let mut guard = TIMERS.lock().unwrap();
        loop {
            let now = std::time::Instant::now();
            let t = guard.as_mut().unwrap();
            let g = t.global;
            let mut i = 0;
            while i < t.entries.len() {
                if t.entries[i].deadline <= now {
                    let e = t.entries.swap_remove(i);
                    let pid = e.dest_pid.or_else(|| {
                        e.dest_name.and_then(|name| {
                            NAME_REGISTRY
                                .lock()
                                .unwrap()
                                .as_ref()
                                .and_then(|m| m.get(&name).copied())
                        })
                    });
                    if let Some(pid) = pid {
                        deliver_cross_thread(g, pid, e.msg);
                    }
                } else {
                    i += 1;
                }
            }
            let next = t.entries.iter().map(|e| e.deadline).min();
            match next {
                Some(dl) => {
                    let wait = dl.saturating_duration_since(std::time::Instant::now());
                    let (g2, _) = TIMER_CV.wait_timeout(guard, wait).unwrap();
                    guard = g2;
                }
                None => {
                    guard = TIMER_CV.wait(guard).unwrap();
                }
            }
        }
    }
}

/// send_after/start_timer. If `wrap != 0`, the message is wrapped as
/// {timeout, Ref, Msg}. This is the start_timer behavior. Returns the timer
/// ref.
#[no_mangle]
pub extern "C" fn mana_rt_send_after(
    ctx: *mut ProcCtx,
    ms: u64,
    dest: u64,
    msg: u64,
    wrap: u64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if ms & TAG_MASK != TAG_SMALL || (ms as i64 >> 3) < 0 {
        return raise_badarg(ctx);
    }
    let millis = (ms as i64 >> 3) as u64;
    let (dest_pid, dest_name) = if dest & 0xF == PID_TAG4 {
        (Some((dest >> 4) as usize), None)
    } else if dest & TAG_MASK == TAG_ATOM {
        (None, Some(dest))
    } else {
        return raise_badarg(ctx);
    };
    let r = mana_rt_make_ref(ctx as *mut ProcCtx);
    let payload = if wrap != 0 {
        let m = eternal_deep_copy(msg);
        let p = alloc_space(4);
        unsafe {
            *p = (3 << 8) | KIND_TUPLE;
            *p.add(1) = atom_intern(b"timeout");
            *p.add(2) = r;
            *p.add(3) = m;
        }
        p as u64
    } else {
        eternal_deep_copy(msg)
    };
    let mut guard = TIMERS.lock().unwrap();
    let t = guard.get_or_insert_with(|| Timers {
        entries: Vec::new(),
        global: ctx.global,
        thread_started: false,
    });
    if !t.thread_started {
        t.thread_started = true;
        std::thread::Builder::new()
            .name("mana-timers".into())
            .spawn(timer_thread)
            .expect("timer thread");
    }
    t.entries.push(TimerEntry {
        deadline: std::time::Instant::now() + std::time::Duration::from_millis(millis),
        ref_id: r >> 4,
        dest_pid,
        dest_name,
        msg: payload,
    });
    drop(guard);
    TIMER_CV.notify_one();
    r
}

/// cancel_timer/1,2. Returns the remaining milliseconds, or false.
#[no_mangle]
pub extern "C" fn mana_rt_cancel_timer(ctx: *mut ProcCtx, r: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if r & 0xF != REF_TAG4 {
        return raise_badarg(ctx);
    }
    let ref_id = r >> 4;
    let mut guard = TIMERS.lock().unwrap();
    let Some(t) = guard.as_mut() else {
        return known().false_a;
    };
    match t.entries.iter().position(|e| e.ref_id == ref_id) {
        Some(i) => {
            let e = t.entries.swap_remove(i);
            let rem = e
                .deadline
                .saturating_duration_since(std::time::Instant::now())
                .as_millis() as u64;
            ((rem << 3) as u64) | TAG_SMALL
        }
        None => known().false_a,
    }
}
