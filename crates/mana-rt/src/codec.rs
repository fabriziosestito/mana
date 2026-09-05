use super::*;

// ---------------------------------------------------------------------------
// crypto (native cut: crypto.erl's NIF stubs are never compiled) — the
// subset Plug.Crypto/Phoenix sessions need.

pub const C_RAND: u64 = 0;

pub const C_HASH: u64 = 1;

pub const C_MAC: u64 = 2;

pub const C_EXOR: u64 = 3;

pub const C_PBKDF2: u64 = 4;

pub(crate) const C_HASH_EQUALS: u64 = 5;

pub(crate) fn crypto_bin_arg(t: u64) -> Result<Vec<u8>, ()> {
    let mut out = Vec::new();
    iolist_flatten(t, &mut out).map(|_| out)
}

pub(crate) fn crypto_hash(alg: &[u8], data: &[u8]) -> Option<Vec<u8>> {
    use sha1::Digest;
    match alg {
        b"sha" => Some(sha1::Sha1::digest(data).to_vec()),
        b"sha224" => Some(sha2::Sha224::digest(data).to_vec()),
        b"sha256" => Some(sha2::Sha256::digest(data).to_vec()),
        b"sha384" => Some(sha2::Sha384::digest(data).to_vec()),
        b"sha512" => Some(sha2::Sha512::digest(data).to_vec()),
        _ => None,
    }
}

pub(crate) fn crypto_hmac(alg: &[u8], key: &[u8], data: &[u8]) -> Option<Vec<u8>> {
    use hmac::{Hmac, Mac};
    macro_rules! mac {
        ($t:ty) => {{
            let mut m = <Hmac<$t> as Mac>::new_from_slice(key).ok()?;
            m.update(data);
            Some(m.finalize().into_bytes().to_vec())
        }};
    }
    match alg {
        b"sha" => mac!(sha1::Sha1),
        b"sha224" => mac!(sha2::Sha224),
        b"sha256" => mac!(sha2::Sha256),
        b"sha384" => mac!(sha2::Sha384),
        b"sha512" => mac!(sha2::Sha512),
        _ => None,
    }
}

/// RFC 2898 PBKDF2 over our HMAC.
pub(crate) fn crypto_pbkdf2(
    alg: &[u8],
    pass: &[u8],
    salt: &[u8],
    iters: u64,
    keylen: usize,
) -> Option<Vec<u8>> {
    let hlen = crypto_hmac(alg, pass, b"")?.len();
    let blocks = keylen.div_ceil(hlen);
    let mut out = Vec::with_capacity(blocks * hlen);
    for i in 1..=blocks as u32 {
        let mut block_in = salt.to_vec();
        block_in.extend_from_slice(&i.to_be_bytes());
        let mut u = crypto_hmac(alg, pass, &block_in)?;
        let mut t = u.clone();
        for _ in 1..iters {
            u = crypto_hmac(alg, pass, &u)?;
            for (ti, ui) in t.iter_mut().zip(u.iter()) {
                *ti ^= ui;
            }
        }
        out.extend_from_slice(&t);
    }
    out.truncate(keylen);
    Some(out)
}

#[no_mangle]
pub extern "C" fn mana_rt_crypto(
    ctx: *mut ProcCtx,
    op: u64,
    a: u64,
    b: u64,
    c: u64,
    d: u64,
    e: u64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    match op {
        C_HASH_EQUALS => {
            // constant-time equality on equal-size binaries; badarg on
            // size mismatch or non-binaries, like OTP
            let (Some((ap, an)), Some((bp, bn))) = (bin_parts(a), bin_parts(b)) else {
                return raise_badarg(ctx);
            };
            if an != bn {
                return raise_badarg(ctx);
            }
            let (asl, bsl) = unsafe {
                (
                    std::slice::from_raw_parts(ap, an),
                    std::slice::from_raw_parts(bp, bn),
                )
            };
            let mut acc = 0u8;
            for i in 0..an {
                acc |= asl[i] ^ bsl[i];
            }
            if acc == 0 {
                known().true_a
            } else {
                known().false_a
            }
        }
        C_RAND => {
            if a & TAG_MASK != TAG_SMALL || (a as i64 >> 3) < 0 {
                return raise_badarg(ctx);
            }
            let n = (a as i64 >> 3) as usize;
            let mut buf = vec![0u8; n];
            if getrandom::getrandom(&mut buf).is_err() {
                return raise_badarg(ctx);
            }
            bytes_to_new_bin(ctx, &buf)
        }
        C_HASH => {
            if a & TAG_MASK != TAG_ATOM {
                return raise_badarg(ctx);
            }
            let Ok(data) = crypto_bin_arg(b) else { return raise_badarg(ctx) };
            match crypto_hash(atom_bytes(a), &data) {
                Some(h) => bytes_to_new_bin(ctx, &h),
                None => raise_badarg(ctx),
            }
        }
        C_MAC => {
            // mac(hmac, Alg, Key, Data)
            if a & TAG_MASK != TAG_ATOM
                || atom_bytes(a) != b"hmac"
                || b & TAG_MASK != TAG_ATOM
            {
                return raise_badarg(ctx);
            }
            let (Ok(key), Ok(data)) = (crypto_bin_arg(c), crypto_bin_arg(d)) else {
                return raise_badarg(ctx);
            };
            match crypto_hmac(atom_bytes(b), &key, &data) {
                Some(h) => bytes_to_new_bin(ctx, &h),
                None => raise_badarg(ctx),
            }
        }
        C_EXOR => {
            let (Ok(x), Ok(y)) = (crypto_bin_arg(a), crypto_bin_arg(b)) else {
                return raise_badarg(ctx);
            };
            if x.len() != y.len() {
                return raise_badarg(ctx);
            }
            let out: Vec<u8> = x.iter().zip(y.iter()).map(|(p, q)| p ^ q).collect();
            bytes_to_new_bin(ctx, &out)
        }
        C_PBKDF2 => {
            // pbkdf2_hmac(Alg, Pass, Salt, Iterations, KeyLen)
            if a & TAG_MASK != TAG_ATOM
                || d & TAG_MASK != TAG_SMALL
                || e & TAG_MASK != TAG_SMALL
            {
                return raise_badarg(ctx);
            }
            let (Ok(pass), Ok(salt)) = (crypto_bin_arg(b), crypto_bin_arg(c)) else {
                return raise_badarg(ctx);
            };
            let iters = (d as i64 >> 3).max(1) as u64;
            let keylen = (e as i64 >> 3).max(0) as usize;
            match crypto_pbkdf2(atom_bytes(a), &pass, &salt, iters, keylen) {
                Some(k) => bytes_to_new_bin(ctx, &k),
                None => raise_badarg(ctx),
            }
        }
        _ => raise_badarg(ctx),
    }
}

/// IEEE CRC-32 (gzip's checksum), table-driven.
pub(crate) fn crc32(bytes: &[u8]) -> u32 {
    static TABLE: std::sync::OnceLock<[u32; 256]> = std::sync::OnceLock::new();
    let table = TABLE.get_or_init(|| {
        let mut t = [0u32; 256];
        for (i, e) in t.iter_mut().enumerate() {
            let mut c = i as u32;
            for _ in 0..8 {
                c = if c & 1 != 0 { 0xedb8_8320 ^ (c >> 1) } else { c >> 1 };
            }
            *e = c;
        }
        t
    });
    let mut c = 0xffff_ffffu32;
    for &b in bytes {
        c = table[((c ^ b as u32) & 0xff) as usize] ^ (c >> 8);
    }
    !c
}

/// zlib:gzip/1 — a real gzip container (RFC 1952) over DEFLATE-compressed
/// data (miniz_oxide). gunzip/1 inverts it and verifies the CRC32 + ISIZE
/// trailer.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_gzip(ctx: *mut ProcCtx, data: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut input = Vec::new();
    if iolist_flatten(data, &mut input).is_err() {
        return raise_badarg(ctx);
    }
    let body = miniz_oxide::deflate::compress_to_vec(&input, 6);
    let mut out = Vec::with_capacity(body.len() + 18);
    // header: magic, CM=8 (deflate), no flags, no mtime, XFL=0, OS=unknown
    out.extend_from_slice(&[0x1f, 0x8b, 0x08, 0x00, 0, 0, 0, 0, 0x00, 0xff]);
    out.extend_from_slice(&body);
    out.extend_from_slice(&crc32(&input).to_le_bytes());
    out.extend_from_slice(&(input.len() as u32).to_le_bytes());
    bytes_to_new_bin(ctx, &out)
}

/// zlib:gunzip/1 — parse a gzip container, inflate, verify CRC32 + ISIZE.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_gunzip(ctx: *mut ProcCtx, data: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut input = Vec::new();
    if iolist_flatten(data, &mut input).is_err() {
        return raise_badarg(ctx);
    }
    match gunzip_bytes(&input) {
        Some(out) => bytes_to_new_bin(ctx, &out),
        None => raise_badarg(ctx),
    }
}

pub(crate) fn gunzip_bytes(input: &[u8]) -> Option<Vec<u8>> {
    if input.len() < 18 || input[0] != 0x1f || input[1] != 0x8b || input[2] != 0x08 {
        return None;
    }
    let flg = input[3];
    let mut off = 10usize;
    if flg & 0x04 != 0 {
        // FEXTRA: 2-byte length then that many bytes
        if off + 2 > input.len() {
            return None;
        }
        let xlen = u16::from_le_bytes([input[off], input[off + 1]]) as usize;
        off += 2 + xlen;
    }
    if flg & 0x08 != 0 {
        // FNAME: null-terminated
        off = skip_cstr(input, off)?;
    }
    if flg & 0x10 != 0 {
        // FCOMMENT: null-terminated
        off = skip_cstr(input, off)?;
    }
    if flg & 0x02 != 0 {
        off += 2; // FHCRC
    }
    if off + 8 > input.len() {
        return None;
    }
    let body = &input[off..input.len() - 8];
    let out = miniz_oxide::inflate::decompress_to_vec(body).ok()?;
    let n = input.len();
    let crc = u32::from_le_bytes([input[n - 8], input[n - 7], input[n - 6], input[n - 5]]);
    let isize = u32::from_le_bytes([input[n - 4], input[n - 3], input[n - 2], input[n - 1]]);
    if crc32(&out) != crc || out.len() as u32 != isize {
        return None;
    }
    Some(out)
}

pub(crate) fn skip_cstr(input: &[u8], mut off: usize) -> Option<usize> {
    while off < input.len() {
        let b = input[off];
        off += 1;
        if b == 0 {
            return Some(off);
        }
    }
    None
}

/// zlib:compress/1 (zlib wrapper) and zlib:zip/1 (raw deflate).
#[no_mangle]
pub extern "C" fn mana_rt_zlib_compress(ctx: *mut ProcCtx, data: u64, raw: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut input = Vec::new();
    if iolist_flatten(data, &mut input).is_err() {
        return raise_badarg(ctx);
    }
    let out = if (raw as i64 >> 3) != 0 {
        miniz_oxide::deflate::compress_to_vec(&input, 6)
    } else {
        miniz_oxide::deflate::compress_to_vec_zlib(&input, 6)
    };
    bytes_to_new_bin(ctx, &out)
}

/// zlib:uncompress/1 (zlib wrapper) and zlib:unzip/1 (raw inflate).
#[no_mangle]
pub extern "C" fn mana_rt_zlib_uncompress(ctx: *mut ProcCtx, data: u64, raw: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut input = Vec::new();
    if iolist_flatten(data, &mut input).is_err() {
        return raise_badarg(ctx);
    }
    let res = if (raw as i64 >> 3) != 0 {
        miniz_oxide::inflate::decompress_to_vec(&input)
    } else {
        miniz_oxide::inflate::decompress_to_vec_zlib(&input)
    };
    match res {
        Ok(out) => bytes_to_new_bin(ctx, &out),
        Err(_) => raise_badarg(ctx),
    }
}

// ---------------------------------------------------------------------------
// zlib streams (miniz_oxide): opaque {mana_zlib, N} handles over a global
// slot table, mirroring the {mana_socket, N} pattern. A stream is created
// Idle by open/0 and switched to inflate or deflate mode by init. Bandit's
// permessage-deflate uses raw (negative-windowBits) streams with sync
// flush; browsers use the one-shot gzip/gunzip above.

pub(crate) enum ZStream {
    Idle,
    Inflate {
        state: Box<miniz_oxide::inflate::stream::InflateState>,
        window_bits: i32,
        pending: Vec<u8>,
    },
    Deflate {
        comp: Box<miniz_oxide::deflate::core::CompressorOxide>,
        flags: u32,
    },
}

pub(crate) static ZLIB_STREAMS: std::sync::Mutex<Vec<Option<std::sync::Arc<std::sync::Mutex<ZStream>>>>> =
    std::sync::Mutex::new(Vec::new());

pub(crate) fn zlib_handle(ctx: &mut ProcCtx, idx: usize) -> u64 {
    let p = alloc_nursery(ctx, 3);
    unsafe {
        *p = (2 << 8) | KIND_TUPLE;
        *p.add(1) = atom_intern(b"mana_zlib");
        *p.add(2) = ((idx as u64) << 3) | TAG_SMALL;
    }
    p as u64
}

pub(crate) fn zlib_resolve(t: u64) -> Option<(usize, std::sync::Arc<std::sync::Mutex<ZStream>>)> {
    if t & TAG_MASK != TAG_BOXED || t == 0 {
        return None;
    }
    let idx = unsafe {
        let p = t as *const u64;
        if *p != (2 << 8) | KIND_TUPLE {
            return None;
        }
        if *p.add(1) & TAG_MASK != TAG_ATOM || atom_bytes(*p.add(1)) != b"mana_zlib" {
            return None;
        }
        let i = *p.add(2);
        if i & TAG_MASK != TAG_SMALL {
            return None;
        }
        (i as i64 >> 3) as usize
    };
    let streams = ZLIB_STREAMS.lock().unwrap();
    streams.get(idx).and_then(|s| s.clone()).map(|a| (idx, a))
}

/// zlib:open/0 — a fresh Idle stream handle.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_open(ctx: *mut ProcCtx) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let idx = {
        let mut streams = ZLIB_STREAMS.lock().unwrap();
        let cell = Some(std::sync::Arc::new(std::sync::Mutex::new(ZStream::Idle)));
        match streams.iter().position(|s| s.is_none()) {
            Some(i) => {
                streams[i] = cell;
                i
            }
            None => {
                streams.push(cell);
                streams.len() - 1
            }
        }
    };
    zlib_handle(ctx, idx)
}

/// zlib:close/1 — free the slot.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_close(ctx: *mut ProcCtx, z: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    match zlib_resolve(z) {
        Some((idx, _)) => {
            let mut streams = ZLIB_STREAMS.lock().unwrap();
            if idx < streams.len() {
                streams[idx] = None;
            }
            known().ok
        }
        None => raise_badarg(ctx),
    }
}

pub(crate) fn zlib_window_bits(t: u64) -> i32 {
    if t & TAG_MASK == TAG_SMALL {
        (t as i64 >> 3) as i32
    } else {
        15 // default
    }
}

/// zlib:inflateInit/1,2 — switch the stream to inflate mode. Negative
/// windowBits selects the raw (headerless) format used by permessage-
/// deflate; the window magnitude is ignored (miniz always uses 32K, a
/// superset that decodes any smaller-window stream).
#[no_mangle]
pub extern "C" fn mana_rt_zlib_inflate_init(ctx: *mut ProcCtx, z: u64, window_bits: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, arc)) = zlib_resolve(z) else {
        return raise_badarg(ctx);
    };
    let wb = zlib_window_bits(window_bits);
    let mut s = arc.lock().unwrap();
    *s = ZStream::Inflate {
        state: miniz_oxide::inflate::stream::InflateState::new_boxed_with_window_bits(wb),
        window_bits: wb,
        pending: Vec::new(),
    };
    known().ok
}

/// zlib:deflateInit/2,6 — switch the stream to deflate mode. level and
/// strategy are honored, windowBits sign selects raw vs zlib (magnitude
/// ignored — output window is always 15), method and memLevel are ignored.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_deflate_init(
    ctx: *mut ProcCtx,
    z: u64,
    level: u64,
    window_bits: u64,
    strategy: u64,
) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, arc)) = zlib_resolve(z) else {
        return raise_badarg(ctx);
    };
    let lvl = if level & TAG_MASK == TAG_SMALL {
        let v = level as i64 >> 3;
        if (0..=9).contains(&v) {
            v as i32
        } else {
            6 // default / -1
        }
    } else {
        6
    };
    let wb = zlib_window_bits(window_bits);
    let strat = if strategy & TAG_MASK == TAG_ATOM {
        match atom_bytes(strategy) {
            b"filtered" => 1,
            b"huffman_only" => 2,
            b"rle" => 3,
            _ => 0,
        }
    } else {
        0
    };
    let flags =
        miniz_oxide::deflate::core::create_comp_flags_from_zip_params(lvl, wb, strat);
    let mut s = arc.lock().unwrap();
    *s = ZStream::Deflate {
        comp: Box::new(miniz_oxide::deflate::core::CompressorOxide::new(flags)),
        flags,
    };
    known().ok
}

pub(crate) fn zlib_flush(t: u64) -> miniz_oxide::MZFlush {
    use miniz_oxide::MZFlush;
    if t & TAG_MASK == TAG_ATOM {
        match atom_bytes(t) {
            b"sync" => MZFlush::Sync,
            b"full" => MZFlush::Full,
            b"finish" => MZFlush::Finish,
            _ => MZFlush::None,
        }
    } else {
        MZFlush::None
    }
}

/// zlib:deflate/2,3 — compress a chunk with the given flush; returns the
/// output as a single binary (valid iodata — Bandit does iodata_to_binary).
#[no_mangle]
pub extern "C" fn mana_rt_zlib_deflate(ctx: *mut ProcCtx, z: u64, data: u64, flush: u64) -> u64 {
    use miniz_oxide::{MZFlush, MZStatus};
    let ctx = unsafe { &mut *ctx };
    let mut input = Vec::new();
    if iolist_flatten(data, &mut input).is_err() {
        return raise_badarg(ctx);
    }
    let Some((_, arc)) = zlib_resolve(z) else {
        return raise_badarg(ctx);
    };
    let fl = zlib_flush(flush);
    let mut s = arc.lock().unwrap();
    let ZStream::Deflate { comp, .. } = &mut *s else {
        return raise_badarg(ctx);
    };
    let mut out = Vec::with_capacity(input.len() / 2 + 64);
    let mut scratch = vec![0u8; 32 * 1024];
    let mut inbuf = &input[..];
    loop {
        let res = miniz_oxide::deflate::stream::deflate(comp, inbuf, &mut scratch, fl);
        out.extend_from_slice(&scratch[..res.bytes_written]);
        inbuf = &inbuf[res.bytes_consumed..];
        match res.status {
            Ok(MZStatus::StreamEnd) => break,
            Ok(_) => {
                let filled = res.bytes_written == scratch.len();
                if inbuf.is_empty() && !filled {
                    break;
                }
            }
            Err(_) => return raise_badarg(ctx),
        }
        // Finish must loop to StreamEnd; others stop when drained above
        if fl != MZFlush::Finish && inbuf.is_empty() && res.bytes_written == 0 {
            break;
        }
    }
    drop(s);
    bytes_to_new_bin(ctx, &out)
}

/// zlib:safeInflate/2 — one bounded inflate round over the accumulated
/// input; returns `{continue, Bin}` when more output may follow (the
/// output chunk filled) or `{finished, Bin}` when the input is drained.
/// Bandit re-calls with `[]` until it sees `finished`.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_safe_inflate(ctx: *mut ProcCtx, z: u64, data: u64) -> u64 {
    use miniz_oxide::{MZFlush, MZStatus};
    let ctx = unsafe { &mut *ctx };
    let mut newdata = Vec::new();
    if iolist_flatten(data, &mut newdata).is_err() {
        return raise_badarg(ctx);
    }
    let Some((_, arc)) = zlib_resolve(z) else {
        return raise_badarg(ctx);
    };
    const CHUNK: usize = 16 * 1024;
    let mut s = arc.lock().unwrap();
    let ZStream::Inflate { state, pending, .. } = &mut *s else {
        return raise_badarg(ctx);
    };
    pending.extend_from_slice(&newdata);
    let mut scratch = vec![0u8; CHUNK];
    let res = miniz_oxide::inflate::stream::inflate(state, pending, &mut scratch, MZFlush::None);
    let consumed = res.bytes_consumed;
    let written = res.bytes_written;
    pending.drain(..consumed);
    let done = matches!(res.status, Ok(MZStatus::StreamEnd)) || written < CHUNK;
    let out = scratch[..written].to_vec();
    drop(s);
    // build {tag, Bin} — root the binary across the tuple alloc
    let bin = bytes_to_new_bin(ctx, &out);
    let mut fr = [ctx.roots_head, 1, bin];
    ctx.roots_head = fr.as_ptr() as u64;
    let tag = atom_intern(if done { b"finished" } else { b"continue" });
    let p = alloc_nursery(ctx, 3);
    unsafe {
        *p = (2 << 8) | KIND_TUPLE;
        *p.add(1) = tag;
        *p.add(2) = fr[2];
    }
    ctx.roots_head = fr[0];
    let _ = &mut fr;
    p as u64
}

/// zlib:inflateReset/1 and deflateReset/1 — restore the stream to its
/// post-init state, keeping the same mode and parameters.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_reset(ctx: *mut ProcCtx, z: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, arc)) = zlib_resolve(z) else {
        return raise_badarg(ctx);
    };
    let mut s = arc.lock().unwrap();
    match &mut *s {
        ZStream::Inflate {
            state,
            window_bits,
            pending,
        } => {
            state.reset(miniz_oxide::DataFormat::from_window_bits(*window_bits));
            pending.clear();
        }
        ZStream::Deflate { comp, flags } => {
            *comp = Box::new(miniz_oxide::deflate::core::CompressorOxide::new(*flags));
        }
        ZStream::Idle => {}
    }
    known().ok
}

/// zlib:inflateEnd/1 and deflateEnd/1 — return the stream to Idle.
#[no_mangle]
pub extern "C" fn mana_rt_zlib_end(ctx: *mut ProcCtx, z: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Some((_, arc)) = zlib_resolve(z) else {
        return raise_badarg(ctx);
    };
    *arc.lock().unwrap() = ZStream::Idle;
    known().ok
}
