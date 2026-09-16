//! gen_tcp and inet for the native runtime. OTP's inet stack is never
//! compiled.
//!
//! All syscalls are NONBLOCKING and run on the scheduler thread. On
//! WouldBlock the operation arms a waiter slot, registers the socket with
//! the reactor, and parks the process (Waiting). The reactor wakes it
//! through IO_WAKES. `reactor.rs` documents the lost-wakeup protocol. Every
//! term argument is converted to a native value BEFORE any park. The Rust
//! locals of a suspended coroutine are not GC roots, so a term pointer must
//! never live across a suspend.

use super::*;

pub(crate) fn sock_handle(ctx: &mut ProcCtx, idx: usize) -> u64 {
    let p = alloc_nursery(ctx, 3);
    unsafe {
        *p = (2 << 8) | KIND_TUPLE;
        *p.add(1) = atom_intern(b"mana_socket");
        *p.add(2) = ((idx as u64) << 3) | TAG_SMALL;
    }
    p as u64
}

pub(crate) fn sock_resolve(t: u64) -> Option<usize> {
    if t & TAG_MASK != TAG_BOXED || t == 0 {
        return None;
    }
    unsafe {
        let p = t as *const u64;
        if *p != (2 << 8) | KIND_TUPLE {
            return None;
        }
        let tag = *p.add(1);
        if tag & TAG_MASK != TAG_ATOM || atom_bytes(tag) != b"mana_socket" {
            return None;
        }
        let idx = *p.add(2);
        if idx & TAG_MASK != TAG_SMALL {
            return None;
        }
        Some((idx as i64 >> 3) as usize)
    }
}

/// Options that both connect and listen accept.
#[derive(Clone, Copy)]
pub(crate) struct TcpOpts {
    pub(crate) binary: bool,
    pub(crate) active: ActiveMode,
}

pub(crate) fn parse_tcp_opts(mut cur: u64) -> Result<TcpOpts, ()> {
    let mut o = TcpOpts {
        binary: false,
        active: ActiveMode::Always,
    };
    while cur & TAG_MASK == TAG_CONS {
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK == TAG_ATOM {
            match atom_bytes(h) {
                b"binary" => o.binary = true,
                b"list" => o.binary = false,
                _ => {} // Other bare atoms, for example reuseaddr, are accepted.
            }
        } else if h & TAG_MASK == TAG_BOXED && h != 0 {
            unsafe {
                let t = h as *const u64;
                if *t == (2 << 8) | KIND_TUPLE && *t.add(1) & TAG_MASK == TAG_ATOM {
                    let v = *t.add(2);
                    match atom_bytes(*t.add(1)) {
                        b"mode" => {
                            if v & TAG_MASK == TAG_ATOM {
                                match atom_bytes(v) {
                                    b"binary" => o.binary = true,
                                    b"list" => o.binary = false,
                                    _ => return Err(()),
                                }
                            }
                        }
                        b"active" => {
                            o.active = if v & TAG_MASK == TAG_ATOM {
                                match atom_bytes(v) {
                                    b"false" => ActiveMode::Passive,
                                    b"once" => ActiveMode::Once,
                                    b"true" => ActiveMode::Always,
                                    _ => return Err(()),
                                }
                            } else {
                                return Err(());
                            }
                        }
                        b"packet" => {
                            // Only raw and 0 are accepted. TODO(packet): other packet modes.
                            let raw = (v & TAG_MASK == TAG_SMALL && v >> 3 == 0)
                                || (v & TAG_MASK == TAG_ATOM
                                    && matches!(atom_bytes(v), b"raw" | b"0"));
                            if !raw {
                                return Err(());
                            }
                        }
                        // Other options, for example reuseaddr, backlog, and
                        // nodelay, are accepted and ignored.
                        _ => {}
                    }
                }
            }
        }
        cur = unsafe { *p.add(1) };
    }
    Ok(o)
}

/// Converts an address term to an IpAddr. The term is an {A,B,C,D} tuple, a
/// binary, a charlist, or the atom 'localhost'.
pub(crate) fn ip_of(t: u64) -> Result<std::net::IpAddr, ()> {
    use std::net::{IpAddr, Ipv4Addr};
    if t & TAG_MASK == TAG_BOXED && t != 0 {
        unsafe {
            let p = t as *const u64;
            if *p == (4 << 8) | KIND_TUPLE {
                let mut o = [0u8; 4];
                for (i, b) in o.iter_mut().enumerate() {
                    let v = *p.add(1 + i);
                    if v & TAG_MASK != TAG_SMALL {
                        return Err(());
                    }
                    let v = v as i64 >> 3;
                    if !(0..=255).contains(&v) {
                        return Err(());
                    }
                    *b = v as u8;
                }
                return Ok(IpAddr::V4(Ipv4Addr::new(o[0], o[1], o[2], o[3])));
            }
        }
    }
    // A hostname as chardata or an atom: only a numeric address or localhost
    // stays nonblocking. A general getaddrinfo call blocks, so it is not
    // supported.
    let mut bytes = Vec::new();
    if t & TAG_MASK == TAG_ATOM {
        bytes.extend_from_slice(atom_bytes(t));
    } else if chardata_flatten(t, &mut bytes).is_err() {
        return Err(());
    }
    let s = std::str::from_utf8(&bytes).map_err(|_| ())?;
    if s == "localhost" {
        return Ok(IpAddr::V4(Ipv4Addr::LOCALHOST));
    }
    s.parse().map_err(|_| ())
}

pub(crate) fn timeout_deadline(t: u64) -> Result<Option<std::time::Instant>, ()> {
    if t & TAG_MASK == TAG_ATOM && atom_bytes(t) == b"infinity" {
        return Ok(None);
    }
    if t & TAG_MASK == TAG_SMALL && (t as i64 >> 3) >= 0 {
        let ms = (t as i64 >> 3) as u64;
        return Ok(Some(
            std::time::Instant::now() + std::time::Duration::from_millis(ms),
        ));
    }
    Err(())
}

pub(crate) fn closed_err(ctx: &mut ProcCtx) -> u64 {
    pair_term(ctx, b"error", atom_intern(b"closed"))
}

/// Arms the read or write waiter and the reactor registration, then parks the
/// process. The reactor wakes it, or idle_wait wakes it at the deadline.
/// Returns false on timeout. The caller must NOT hold the SOCKETS lock.
pub(crate) fn park_on_socket(
    ctx: &mut ProcCtx,
    idx: usize,
    want_read: bool,
    deadline: Option<std::time::Instant>,
) -> bool {
    let pid = ctx.current;
    {
        let mut tab = SOCKETS.lock().unwrap();
        let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
            return true; // The socket closed under us. The caller's retry observes it.
        };
        if want_read {
            entry.read_waiter = Some(pid);
        } else {
            entry.write_waiter = Some(pid);
        }
        if !entry.registered {
            entry.registered = true;
            REACTOR_CMDS.push(idx);
        }
    }
    ensure_reactor(ctx.global);
    reactor_wake();
    if let Some(dl) = deadline {
        if std::time::Instant::now() >= dl {
            clear_waiter(idx, pid, want_read);
            return false;
        }
    }
    {
        // Publish Waiting, then check the mailbox again under the lock. A
        // sender that saw us Running pushed to ingress and did not enqueue
        // us for a run. A message is not what this park waits for. But if
        // the message waits until the process next blocks in `receive`, that
        // is a lost wakeup (Bandit's connection loop: tcp op, then gen_server
        // receive). Instead, return spuriously. The op retries and parks
        // again.
        let p = cur_proc(ctx);
        let mut st = p.state.lock();
        *st = PState::Waiting(deadline);
        if !p.ingress.is_empty() {
            *st = PState::Running;
            drop(st);
            clear_waiter(idx, pid, want_read);
            return true;
        }
    }
    suspend_current(ctx);
    if let Some(dl) = deadline {
        if std::time::Instant::now() >= dl {
            clear_waiter(idx, pid, want_read);
            return false;
        }
    }
    true
}

pub(crate) fn clear_waiter(idx: usize, pid: usize, want_read: bool) {
    let mut tab = SOCKETS.lock().unwrap();
    if let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) {
        if want_read && entry.read_waiter == Some(pid) {
            entry.read_waiter = None;
        }
        if !want_read && entry.write_waiter == Some(pid) {
            entry.write_waiter = None;
        }
    }
}

// TCP op codes. The codegen compile dispatch mirrors these values.

/// file:sendfile/5 (RawFile, Socket, Offset, Bytes, _Opts). Reads the file at
/// an offset and sends with a parking send loop. Bytes == 0 streams to EOF.
/// Returns {ok, Sent}.
#[no_mangle]
pub extern "C" fn mana_rt_sendfile(
    ctx: *mut ProcCtx,
    fd_t: u64,
    sock: u64,
    off_t: u64,
    len_t: u64,
    _opts: u64,
) -> u64 {
    use std::os::unix::fs::FileExt;
    let ctx = unsafe { &mut *ctx };
    let Some(fidx) = file_resolve(fd_t) else {
        return raise_badarg(ctx);
    };
    let Some(sidx) = sock_resolve(sock) else {
        return raise_badarg(ctx);
    };
    if off_t & TAG_MASK != TAG_SMALL
        || len_t & TAG_MASK != TAG_SMALL
        || (off_t as i64 >> 3) < 0
        || (len_t as i64 >> 3) < 0
    {
        return raise_badarg(ctx);
    }
    let base = (off_t as i64 >> 3) as u64;
    let want = (len_t as i64 >> 3) as u64; // 0 means: stream to EOF.
    let mut sent = 0u64;
    let mut buf = vec![0u8; 64 * 1024];
    loop {
        if want > 0 && sent == want {
            break;
        }
        let cap = if want > 0 {
            std::cmp::min(buf.len() as u64, want - sent) as usize
        } else {
            buf.len()
        };
        let n = {
            let tab = FILES.lock().unwrap();
            let Some(entry) = tab.slots.get(fidx).and_then(|s| s.as_ref()) else {
                return pair_term(ctx, b"error", atom_intern(b"ebadf"));
            };
            match entry.file.read_at(&mut buf[..cap], base + sent) {
                Ok(n) => n,
                Err(e) => {
                    drop(tab);
                    return err_tuple(ctx, &e);
                }
            }
        };
        if n == 0 {
            break; // EOF: return {ok, Sent} with the real count, like BEAM.
        }
        // Socket send with partial-write parking, the same discipline as T_SEND.
        let mut off = 0usize;
        while off < n {
            let step: Result<Option<usize>, std::io::Error> = {
                let mut tab = SOCKETS.lock().unwrap();
                let Some(entry) = tab.slots.get_mut(sidx).and_then(|s| s.as_mut()) else {
                    drop(tab);
                    return closed_err(ctx);
                };
                let SockSource::Stream(st) = &mut entry.source else {
                    drop(tab);
                    return raise_badarg(ctx);
                };
                match st.write(&buf[off..n]) {
                    Ok(k) => {
                        entry.send_oct += k as u64;
                        Ok(Some(k))
                    }
                    Err(e)
                        if e.kind() == std::io::ErrorKind::WouldBlock
                            || e.kind() == std::io::ErrorKind::Interrupted =>
                    {
                        Ok(None)
                    }
                    Err(e) => Err(e),
                }
            };
            match step {
                Ok(Some(k)) => off += k,
                Ok(None) => {
                    park_on_socket(ctx, sidx, false, None);
                }
                Err(e) => {
                    clear_waiter(sidx, ctx.current, false);
                    if e.kind() == std::io::ErrorKind::BrokenPipe
                        || e.kind() == std::io::ErrorKind::ConnectionReset
                    {
                        return closed_err(ctx);
                    }
                    return err_tuple(ctx, &e);
                }
            }
        }
        clear_waiter(sidx, ctx.current, false);
        sent += n as u64;
    }
    let t = alloc_nursery(ctx, 3);
    unsafe {
        *t = (2 << 8) | KIND_TUPLE;
        *t.add(1) = atom_intern(b"ok");
        *t.add(2) = ((sent << 3) as u64) | TAG_SMALL;
    }
    t as u64
}

pub(crate) fn addr_tuple(ctx: &mut ProcCtx, addr: std::net::SocketAddr) -> u64 {
    let small = |v: i64| ((v << 3) as u64) | TAG_SMALL;
    let ip = match addr.ip() {
        std::net::IpAddr::V4(v4) => v4.octets(),
        std::net::IpAddr::V6(_) => [0, 0, 0, 0], // TODO(ipv6): return the real IPv6 address.
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let a = alloc_nursery(ctx, 5);
    unsafe {
        *a = (4 << 8) | KIND_TUPLE;
        for (i, o) in ip.iter().enumerate() {
            *a.add(1 + i) = small(*o as i64);
        }
    }
    fr[2] = a as u64;
    let pair = alloc_nursery(ctx, 3);
    unsafe {
        *pair = (2 << 8) | KIND_TUPLE;
        *pair.add(1) = fr[2];
        *pair.add(2) = small(addr.port() as i64);
    }
    ctx.roots_head = saved;
    pair as u64
}

#[no_mangle]
pub extern "C" fn mana_rt_tcp(ctx: *mut ProcCtx, op: u64, a: u64, b: u64, c: u64, d: u64) -> u64 {
    use std::io::{Read, Write};
    let ctx = unsafe { &mut *ctx };
    match op {
        T_CONNECT => {
            // Arguments: a is addr, b is port, c is opts, d is timeout.
            let Ok(ip) = ip_of(a) else {
                return raise_badarg(ctx);
            };
            if b & TAG_MASK != TAG_SMALL {
                return raise_badarg(ctx);
            }
            let port = (b as i64 >> 3) as u16;
            let Ok(opts) = parse_tcp_opts(c) else {
                return raise_badarg(ctx);
            };
            let Ok(deadline) = timeout_deadline(d) else {
                return raise_badarg(ctx);
            };
            let addr = std::net::SocketAddr::new(ip, port);
            let stream = match mio::net::TcpStream::connect(addr) {
                Ok(s) => s,
                Err(e) => return err_tuple(ctx, &e),
            };
            let idx = SOCKETS.lock().unwrap().insert(SockEntry {
                source: SockSource::Stream(stream),
                read_waiter: None,
                write_waiter: None,
                registered: false,
                owner: ctx.current,
                active: opts.active,
                binary: opts.binary,
                rbuf: Vec::new(),
                recv_oct: 0,
                send_oct: 0,
            });
            // Wait for writability, then check SO_ERROR.
            loop {
                {
                    let mut tab = SOCKETS.lock().unwrap();
                    let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                        drop(tab);
                        return closed_err(ctx);
                    };
                    let SockSource::Stream(s) = &mut entry.source else {
                        drop(tab);
                        return raise_badarg(ctx);
                    };
                    match s.peer_addr() {
                        Ok(_) => {
                            drop(tab);
                            ensure_registered_active(ctx, idx);
                            let h = sock_handle(ctx, idx);
                            return pair_term(ctx, b"ok", h);
                        }
                        Err(e)
                            if e.kind() == std::io::ErrorKind::NotConnected
                                || e.raw_os_error() == Some(libc_einprogress()) =>
                        {
                            // A refused connect also reports NotConnected
                            // from peer_addr. The verdict lives in SO_ERROR.
                            if let Ok(Some(err)) = s.take_error() {
                                tab.slots[idx] = None;
                                tab.free.push(idx);
                                drop(tab);
                                return pair_term(
                                    ctx,
                                    b"error",
                                    if err.raw_os_error() == Some(111) {
                                        atom_intern(b"econnrefused")
                                    } else {
                                        posix_atom(&err)
                                    },
                                );
                            }
                        }
                        Err(_) => {
                            let e =
                                s.take_error().ok().flatten().unwrap_or_else(|| {
                                    std::io::Error::from(std::io::ErrorKind::Other)
                                });
                            tab.slots[idx] = None;
                            tab.free.push(idx);
                            drop(tab);
                            return pair_term(
                                ctx,
                                b"error",
                                if e.raw_os_error() == Some(111) {
                                    atom_intern(b"econnrefused")
                                } else {
                                    posix_atom(&e)
                                },
                            );
                        }
                    }
                }
                if !park_on_socket(ctx, idx, false, deadline) {
                    let mut tab = SOCKETS.lock().unwrap();
                    tab.slots[idx] = None;
                    tab.free.push(idx);
                    drop(tab);
                    return pair_term(ctx, b"error", atom_intern(b"timeout"));
                }
            }
        }
        T_LISTEN => {
            // Arguments: a is port, b is opts.
            if a & TAG_MASK != TAG_SMALL {
                return raise_badarg(ctx);
            }
            let port = (a as i64 >> 3) as u16;
            let Ok(opts) = parse_tcp_opts(b) else {
                return raise_badarg(ctx);
            };
            let addr = std::net::SocketAddr::new(
                std::net::IpAddr::V4(std::net::Ipv4Addr::UNSPECIFIED),
                port,
            );
            match mio::net::TcpListener::bind(addr) {
                Ok(l) => {
                    let idx = SOCKETS.lock().unwrap().insert(SockEntry {
                        source: SockSource::Listener(l),
                        read_waiter: None,
                        write_waiter: None,
                        registered: false,
                        owner: ctx.current,
                        active: opts.active,
                        binary: opts.binary,
                        rbuf: Vec::new(),
                        recv_oct: 0,
                        send_oct: 0,
                    });
                    let h = sock_handle(ctx, idx);
                    pair_term(ctx, b"ok", h)
                }
                Err(e) => err_tuple(ctx, &e),
            }
        }
        T_ACCEPT => {
            // Arguments: a is lsock, b is timeout.
            let Some(idx) = sock_resolve(a) else {
                return raise_badarg(ctx);
            };
            let Ok(deadline) = timeout_deadline(b) else {
                return raise_badarg(ctx);
            };
            loop {
                let accepted = {
                    let mut tab = SOCKETS.lock().unwrap();
                    let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                        drop(tab);
                        return closed_err(ctx);
                    };
                    let opts = TcpOpts {
                        binary: entry.binary,
                        active: entry.active,
                    };
                    let SockSource::Listener(l) = &mut entry.source else {
                        drop(tab);
                        return raise_badarg(ctx);
                    };
                    match l.accept() {
                        Ok((stream, _)) => {
                            let owner = ctx.current;
                            let i = tab.insert(SockEntry {
                                source: SockSource::Stream(stream),
                                read_waiter: None,
                                write_waiter: None,
                                registered: false,
                                owner,
                                active: opts.active,
                                binary: opts.binary,
                                rbuf: Vec::new(),
                                recv_oct: 0,
                                send_oct: 0,
                            });
                            Some(Ok(i))
                        }
                        Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => None,
                        Err(e) => Some(Err(e)),
                    }
                };
                match accepted {
                    Some(Ok(i)) => {
                        clear_waiter(idx, ctx.current, true);
                        ensure_registered_active(ctx, i);
                        let h = sock_handle(ctx, i);
                        return pair_term(ctx, b"ok", h);
                    }
                    Some(Err(e)) => {
                        clear_waiter(idx, ctx.current, true);
                        return err_tuple(ctx, &e);
                    }
                    None => {
                        if !park_on_socket(ctx, idx, true, deadline) {
                            return pair_term(ctx, b"error", atom_intern(b"timeout"));
                        }
                    }
                }
            }
        }
        T_RECV => {
            // Arguments: a is sock, b is len, c is timeout.
            let Some(idx) = sock_resolve(a) else {
                return raise_badarg(ctx);
            };
            if b & TAG_MASK != TAG_SMALL || (b as i64 >> 3) < 0 {
                return raise_badarg(ctx);
            }
            let want = (b as i64 >> 3) as usize;
            let Ok(deadline) = timeout_deadline(c) else {
                return raise_badarg(ctx);
            };
            loop {
                enum Step {
                    Done(Vec<u8>, bool),
                    Closed(bool),
                    Park,
                    Err(std::io::Error),
                }
                let step = {
                    let mut tab = SOCKETS.lock().unwrap();
                    let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                        drop(tab);
                        return closed_err(ctx);
                    };
                    let binary = entry.binary;
                    if want > 0 && entry.rbuf.len() >= want {
                        let rest = entry.rbuf.split_off(want);
                        let data = std::mem::replace(&mut entry.rbuf, rest);
                        Step::Done(data, binary)
                    } else if want == 0 && !entry.rbuf.is_empty() {
                        let data = std::mem::take(&mut entry.rbuf);
                        Step::Done(data, binary)
                    } else {
                        let SockSource::Stream(s) = &mut entry.source else {
                            drop(tab);
                            return raise_badarg(ctx);
                        };
                        match with_recv_scratch(|chunk| {
                            s.read(chunk).map(|k| {
                                entry.recv_oct += k as u64;
                                entry.rbuf.extend_from_slice(&chunk[..k]);
                                k
                            })
                        }) {
                            Ok(0) => Step::Closed(binary),
                            Ok(_) => {
                                if want == 0 || entry.rbuf.len() >= want {
                                    let take = if want == 0 { entry.rbuf.len() } else { want };
                                    let rest = entry.rbuf.split_off(take);
                                    let data = std::mem::replace(&mut entry.rbuf, rest);
                                    Step::Done(data, binary)
                                } else {
                                    Step::Park
                                }
                            }
                            Err(e)
                                if e.kind() == std::io::ErrorKind::WouldBlock
                                    || e.kind() == std::io::ErrorKind::Interrupted =>
                            {
                                Step::Park
                            }
                            Err(e) => Step::Err(e),
                        }
                    }
                };
                match step {
                    Step::Done(data, binary) => {
                        clear_waiter(idx, ctx.current, true);
                        let term = if binary {
                            bytes_to_new_bin(ctx, &data)
                        } else {
                            bytes_to_byte_list(ctx, &data)
                        };
                        return pair_term(ctx, b"ok", term);
                    }
                    Step::Closed(_) => {
                        clear_waiter(idx, ctx.current, true);
                        return closed_err(ctx);
                    }
                    Step::Err(e) => {
                        clear_waiter(idx, ctx.current, true);
                        return err_tuple(ctx, &e);
                    }
                    Step::Park => {
                        if !park_on_socket(ctx, idx, true, deadline) {
                            return pair_term(ctx, b"error", atom_intern(b"timeout"));
                        }
                    }
                }
            }
        }
        T_SEND => {
            // Arguments: a is sock, b is iodata.
            let Some(idx) = sock_resolve(a) else {
                return raise_badarg(ctx);
            };
            let mut data = Vec::new();
            if iolist_flatten(b, &mut data).is_err() {
                return raise_badarg(ctx);
            }
            let mut off = 0usize;
            loop {
                let step: Result<Option<usize>, std::io::Error> = {
                    let mut tab = SOCKETS.lock().unwrap();
                    let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                        drop(tab);
                        return closed_err(ctx);
                    };
                    let SockSource::Stream(s) = &mut entry.source else {
                        drop(tab);
                        return raise_badarg(ctx);
                    };
                    match s.write(&data[off..]) {
                        Ok(k) => {
                            entry.send_oct += k as u64;
                            Ok(Some(k))
                        }
                        Err(e)
                            if e.kind() == std::io::ErrorKind::WouldBlock
                                || e.kind() == std::io::ErrorKind::Interrupted =>
                        {
                            Ok(None)
                        }
                        Err(e) => Err(e),
                    }
                };
                match step {
                    Ok(Some(k)) => {
                        off += k;
                        if off == data.len() {
                            clear_waiter(idx, ctx.current, false);
                            return atom_intern(b"ok");
                        }
                    }
                    Ok(None) => {
                        park_on_socket(ctx, idx, false, None);
                    }
                    Err(e) => {
                        clear_waiter(idx, ctx.current, false);
                        if e.kind() == std::io::ErrorKind::BrokenPipe
                            || e.kind() == std::io::ErrorKind::ConnectionReset
                        {
                            return closed_err(ctx);
                        }
                        return err_tuple(ctx, &e);
                    }
                }
            }
        }
        T_CLOSE => {
            let Some(idx) = sock_resolve(a) else {
                return raise_badarg(ctx);
            };
            let entry = {
                let mut tab = SOCKETS.lock().unwrap();
                let e = tab.slots.get_mut(idx).and_then(|s| s.take());
                if e.is_some() {
                    tab.free.push(idx);
                }
                e
            };
            if let Some(e) = entry {
                // Waiters retry, see the missing entry, and return {error, closed}.
                if let Some(pid) = e.read_waiter {
                    IO_WAKES.push((pid, idx, true));
                }
                if let Some(pid) = e.write_waiter {
                    IO_WAKES.push((pid, idx, false));
                }
                for s in 0..ctx.global.n_scheds {
                    wake_sched(ctx.global, s);
                }
                // The drop of the source closes the fd. epoll deregisters it
                // on close.
            }
            atom_intern(b"ok")
        }
        T_SHUTDOWN => {
            let Some(idx) = sock_resolve(a) else {
                return raise_badarg(ctx);
            };
            let how = if b & TAG_MASK == TAG_ATOM {
                match atom_bytes(b) {
                    b"read" => std::net::Shutdown::Read,
                    b"write" => std::net::Shutdown::Write,
                    b"read_write" => std::net::Shutdown::Both,
                    _ => return raise_badarg(ctx),
                }
            } else {
                return raise_badarg(ctx);
            };
            let mut tab = SOCKETS.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                drop(tab);
                return closed_err(ctx);
            };
            let SockSource::Stream(s) = &mut entry.source else {
                drop(tab);
                return raise_badarg(ctx);
            };
            let res = s.shutdown(how);
            drop(tab);
            match res {
                Ok(()) => atom_intern(b"ok"),
                Err(e) => err_tuple(ctx, &e),
            }
        }
        T_SETOPTS => {
            let Some(idx) = sock_resolve(a) else {
                return raise_badarg(ctx);
            };
            let Ok(opts) = parse_tcp_opts(b) else {
                return raise_badarg(ctx);
            };
            let has_mode_opt = |mut cur: u64, name: &[u8]| -> bool {
                while cur & TAG_MASK == TAG_CONS {
                    let p = (cur & !TAG_MASK) as *const u64;
                    let h = unsafe { *p };
                    if h & TAG_MASK == TAG_ATOM && atom_bytes(h) == name {
                        return true;
                    }
                    if h & TAG_MASK == TAG_BOXED && h != 0 {
                        unsafe {
                            let t = h as *const u64;
                            if *t == (2 << 8) | KIND_TUPLE
                                && *t.add(1) & TAG_MASK == TAG_ATOM
                                && atom_bytes(*t.add(1)) == name
                            {
                                return true;
                            }
                        }
                    }
                    cur = unsafe { *p.add(1) };
                }
                false
            };
            let mut tab = SOCKETS.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                drop(tab);
                return closed_err(ctx);
            };
            let mut activated = false;
            if has_mode_opt(b, b"active") {
                let was = entry.active;
                entry.active = opts.active;
                activated = was == ActiveMode::Passive && opts.active != ActiveMode::Passive;
            }
            if has_mode_opt(b, b"binary") {
                entry.binary = true;
            }
            if has_mode_opt(b, b"list") {
                entry.binary = false;
            }
            drop(tab);
            if activated {
                // Deliver data that is already buffered, or an edge that the
                // kernel already reported. If the socket is quiet, the pump
                // does nothing.
                ensure_registered_active(ctx, idx);
                IO_ACTIVE.push(idx);
                for s in 0..ctx.global.n_scheds {
                    wake_sched(ctx.global, s);
                }
            }
            atom_intern(b"ok")
        }
        T_CONTROLLING => {
            let Some(idx) = sock_resolve(a) else {
                return raise_badarg(ctx);
            };
            if b & 0xF != PID_TAG4 {
                return raise_badarg(ctx);
            }
            let pid = (b >> 4) as usize;
            let mut tab = SOCKETS.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                drop(tab);
                return closed_err(ctx);
            };
            entry.owner = pid;
            atom_intern(b"ok")
        }
        T_PEERNAME | T_SOCKNAME | T_PORT => {
            let Some(idx) = sock_resolve(a) else {
                return raise_badarg(ctx);
            };
            let addr = {
                let mut tab = SOCKETS.lock().unwrap();
                let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                    drop(tab);
                    return closed_err(ctx);
                };
                match (&entry.source, op) {
                    (SockSource::Stream(s), T_PEERNAME) => s.peer_addr(),
                    (SockSource::Stream(s), _) => s.local_addr(),
                    (SockSource::Listener(_), T_PEERNAME) => {
                        drop(tab);
                        return raise_badarg(ctx);
                    }
                    (SockSource::Listener(l), _) => l.local_addr(),
                }
            };
            match addr {
                Ok(sa) => {
                    if op == T_PORT {
                        let small = ((sa.port() as i64) << 3) as u64 | TAG_SMALL;
                        pair_term(ctx, b"ok", small)
                    } else {
                        let t = addr_tuple(ctx, sa);
                        pair_term(ctx, b"ok", t)
                    }
                }
                Err(e) => err_tuple(ctx, &e),
            }
        }
        T_GETSTAT => {
            let Some(idx) = sock_resolve(a) else {
                return raise_badarg(ctx);
            };
            let (recv_oct, send_oct) = {
                let tab = SOCKETS.lock().unwrap();
                let Some(entry) = tab.slots.get(idx).and_then(|s| s.as_ref()) else {
                    drop(tab);
                    return closed_err(ctx);
                };
                (entry.recv_oct, entry.send_oct)
            };
            let stats: [(&[u8], u64); 8] = [
                (b"recv_oct", recv_oct),
                (b"recv_cnt", 0),
                (b"recv_max", 0),
                (b"recv_avg", 0),
                (b"send_oct", send_oct),
                (b"send_cnt", 0),
                (b"send_max", 0),
                (b"send_avg", 0),
            ];
            let saved = ctx.roots_head;
            let mut fr = [0u64, 2, NIL, NIL];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            for (name, v) in stats.iter().rev() {
                let t = alloc_nursery(ctx, 3);
                unsafe {
                    *t = (2 << 8) | KIND_TUPLE;
                    *t.add(1) = atom_intern(name);
                    *t.add(2) = ((*v as i64) << 3) as u64 | TAG_SMALL;
                }
                fr[3] = t as u64;
                let cell = alloc_nursery(ctx, 2);
                unsafe {
                    *cell = fr[3];
                    *cell.add(1) = fr[2];
                }
                fr[2] = cell as u64 | TAG_CONS;
            }
            let list = fr[2];
            ctx.roots_head = saved;
            pair_term(ctx, b"ok", list)
        }
        T_GETOPTS => {
            let Some(idx) = sock_resolve(a) else {
                return raise_badarg(ctx);
            };
            let (active, binary) = {
                let tab = SOCKETS.lock().unwrap();
                let Some(entry) = tab.slots.get(idx).and_then(|s| s.as_ref()) else {
                    drop(tab);
                    return closed_err(ctx);
                };
                (entry.active, entry.binary)
            };
            // Answer only the requested option names that the runtime models.
            // Skip unknown names.
            let mut wanted: Vec<&'static [u8]> = Vec::new();
            let mut cur = b;
            while cur & TAG_MASK == TAG_CONS {
                let p = (cur & !TAG_MASK) as *const u64;
                let o = unsafe { *p };
                if o & TAG_MASK == TAG_ATOM {
                    match atom_bytes(o) {
                        b"active" => wanted.push(b"active"),
                        b"mode" => wanted.push(b"mode"),
                        b"packet" => wanted.push(b"packet"),
                        b"nodelay" => wanted.push(b"nodelay"),
                        b"keepalive" => wanted.push(b"keepalive"),
                        b"reuseaddr" => wanted.push(b"reuseaddr"),
                        _ => {}
                    }
                }
                cur = unsafe { *p.add(1) };
            }
            let saved = ctx.roots_head;
            let mut fr = [0u64, 2, NIL, NIL];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            for name in wanted.iter().rev() {
                let val = match *name {
                    b"active" => match active {
                        ActiveMode::Passive => known().false_a,
                        ActiveMode::Once => atom_intern(b"once"),
                        ActiveMode::Always => known().true_a,
                    },
                    b"mode" => {
                        if binary {
                            atom_intern(b"binary")
                        } else {
                            atom_intern(b"list")
                        }
                    }
                    b"packet" => TAG_SMALL, // The small integer 0.
                    _ => known().true_a,    // nodelay, keepalive, and reuseaddr always report true.
                };
                let t = alloc_nursery(ctx, 3);
                unsafe {
                    *t = (2 << 8) | KIND_TUPLE;
                    *t.add(1) = atom_intern(name);
                    *t.add(2) = val;
                }
                fr[3] = t as u64;
                let cell = alloc_nursery(ctx, 2);
                unsafe {
                    *cell = fr[3];
                    *cell.add(1) = fr[2];
                }
                fr[2] = cell as u64 | TAG_CONS;
            }
            let list = fr[2];
            ctx.roots_head = saved;
            pair_term(ctx, b"ok", list)
        }
        _ => raise_badarg(ctx),
    }
}

pub(crate) fn libc_einprogress() -> i32 {
    115 // Linux EINPROGRESS.
}

// Active mode ({active, once | true})

/// Queue of active sockets that have a readable event and no parked reader.
/// The reactor never reads sockets. It pushes the socket index here. A
/// scheduler drains the queue at its loop top, performs the nonblocking
/// reads, and delivers {tcp, Sock, Data} and {tcp_closed, Sock} messages to
/// the owner. The messages are built in the shared old space, because
/// push_and_wake requires shared-safe terms.
pub(crate) static IO_ACTIVE: SegQueue<usize> = SegQueue::new();

pub(crate) fn shared_bin(ctx: &mut ProcCtx, bytes: &[u8]) -> u64 {
    let words = 1 + bytes.len().div_ceil(8);
    let p = alloc_shared(ctx, words);
    unsafe {
        *p = ((bytes.len() as u64) << 8) | KIND_BIN;
        if words > 1 {
            *p.add(words - 1) = 0; // The padding tail word must be zero.
        }
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), p.add(1) as *mut u8, bytes.len());
    }
    p as u64
}

pub(crate) fn shared_byte_list(ctx: &mut ProcCtx, bytes: &[u8]) -> u64 {
    let mut tail = NIL;
    for &b in bytes.iter().rev() {
        let cell = alloc_shared(ctx, 2);
        unsafe {
            *cell = ((b as u64) << 3) | TAG_SMALL;
            *cell.add(1) = tail;
        }
        tail = cell as u64 | TAG_CONS;
    }
    tail
}

pub(crate) fn shared_sock_handle(ctx: &mut ProcCtx, idx: usize) -> u64 {
    shared_tuple(
        ctx,
        &[atom_intern(b"mana_socket"), ((idx as u64) << 3) | TAG_SMALL],
    )
}

/// Registers an active socket with the reactor if it is not registered yet.
/// Without this, a socket that never parks never gets events.
pub(crate) fn ensure_registered_active(ctx: &mut ProcCtx, idx: usize) {
    let mut need = false;
    {
        let mut tab = SOCKETS.lock().unwrap();
        if let Some(e) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) {
            if e.active != ActiveMode::Passive {
                if !e.registered {
                    e.registered = true;
                    need = true;
                }
            }
        }
    }
    if need {
        REACTOR_CMDS.push(idx);
        ensure_reactor(ctx.global);
        reactor_wake();
    }
}

/// Drains the pending active-mode sockets. The scheduler calls this at its
/// loop top, which is a safepoint.
pub(crate) fn drain_io_active(ctx: &mut ProcCtx) {
    let n = IO_ACTIVE.len();
    for _ in 0..n {
        let Some(idx) = IO_ACTIVE.pop() else { break };
        active_pump(ctx, idx);
    }
}

pub(crate) fn active_pump(ctx: &mut ProcCtx, idx: usize) {
    use std::io::Read;
    loop {
        enum Ev {
            Data(Vec<u8>, usize, bool, bool), // Fields: bytes, owner, binary, once.
            Closed(usize),
            Quiet,
        }
        // Read and change state under the lock. Deliver outside the lock.
        // push_and_wake takes state locks. Never nest them under SOCKETS.
        let ev = {
            let mut tab = SOCKETS.lock().unwrap();
            let Some(entry) = tab.slots.get_mut(idx).and_then(|s| s.as_mut()) else {
                return;
            };
            if entry.active == ActiveMode::Passive {
                return; // The socket is passive now, or tcp_closed was already sent.
            }
            let owner = entry.owner;
            let binary = entry.binary;
            let once = entry.active == ActiveMode::Once;
            if !entry.rbuf.is_empty() {
                let data = std::mem::take(&mut entry.rbuf);
                if once {
                    entry.active = ActiveMode::Passive;
                }
                Ev::Data(data, owner, binary, once)
            } else {
                let SockSource::Stream(s) = &mut entry.source else {
                    return; // A listener has no active data.
                };
                match with_recv_scratch(|chunk| s.read(chunk).map(|k| chunk[..k].to_vec())) {
                    Ok(data) if data.is_empty() => {
                        entry.active = ActiveMode::Passive; // Send tcp_closed only once.
                        Ev::Closed(owner)
                    }
                    Ok(data) => {
                        entry.recv_oct += data.len() as u64;
                        if once {
                            entry.active = ActiveMode::Passive;
                        }
                        Ev::Data(data, owner, binary, once)
                    }
                    Err(e)
                        if e.kind() == std::io::ErrorKind::WouldBlock
                            || e.kind() == std::io::ErrorKind::Interrupted =>
                    {
                        Ev::Quiet
                    }
                    Err(_) => {
                        entry.active = ActiveMode::Passive;
                        Ev::Closed(owner)
                    }
                }
            }
        };
        match ev {
            Ev::Data(bytes, owner, binary, once) => {
                let handle = shared_sock_handle(ctx, idx);
                let payload = if binary {
                    shared_bin(ctx, &bytes)
                } else {
                    shared_byte_list(ctx, &bytes)
                };
                let msg = shared_tuple(ctx, &[atom_intern(b"tcp"), handle, payload]);
                push_and_wake(ctx, owner, msg);
                if once {
                    return;
                }
            }
            Ev::Closed(owner) => {
                let handle = shared_sock_handle(ctx, idx);
                let msg = shared_tuple(ctx, &[atom_intern(b"tcp_closed"), handle]);
                push_and_wake(ctx, owner, msg);
                return;
            }
            Ev::Quiet => return,
        }
    }
}
