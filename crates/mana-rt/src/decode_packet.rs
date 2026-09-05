//! erlang:decode_packet/3 for the http_bin and httph_bin packet types only.
//! The HTTP/1 parser of Bandit uses these types. Each call is stateless. The
//! result shapes match the erts packet_parser. The Conf.DecodePacket
//! conformance program checks every shape against BEAM.

use super::*;

/// The known-header table of erts. Each entry holds the atom text. The
/// position of an entry gives the index in the second element of the
/// http_header tuple.
pub(crate) const HTTP_FIELDS: &[&str] = &[
    "Cache-Control",
    "Connection",
    "Date",
    "Pragma",
    "Transfer-Encoding",
    "Upgrade",
    "Via",
    "Accept",
    "Accept-Charset",
    "Accept-Encoding",
    "Accept-Language",
    "Authorization",
    "From",
    "Host",
    "If-Modified-Since",
    "If-Match",
    "If-None-Match",
    "If-Range",
    "If-Unmodified-Since",
    "Max-Forwards",
    "Proxy-Authorization",
    "Range",
    "Referer",
    "User-Agent",
    "Age",
    "Location",
    "Proxy-Authenticate",
    "Public",
    "Retry-After",
    "Server",
    "Vary",
    "Warning",
    "Www-Authenticate",
    "Allow",
    "Content-Base",
    "Content-Encoding",
    "Content-Language",
    "Content-Length",
    "Content-Location",
    "Content-Md5",
    "Content-Range",
    "Content-Type",
    "Etag",
    "Expires",
    "Last-Modified",
    "Accept-Ranges",
    "Set-Cookie",
    "Set-Cookie2",
    "X-Forwarded-For",
    "Cookie",
    "Keep-Alive",
    "Proxy-Connection",
];

pub(crate) const HTTP_METHODS: &[&str] =
    &["OPTIONS", "GET", "HEAD", "POST", "PUT", "DELETE", "TRACE"];

/// Convert a header name to canonical case the way erts does. The function
/// capitalizes the first letter of every dash-separated token. It lowercases
/// the other letters.
pub(crate) fn canonical_field(name: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(name.len());
    let mut start_of_token = true;
    for &b in name {
        if b == b'-' {
            out.push(b'-');
            start_of_token = true;
        } else if start_of_token {
            out.push(b.to_ascii_uppercase());
            start_of_token = false;
        } else {
            out.push(b.to_ascii_lowercase());
        }
    }
    out
}

pub(crate) fn small_of(v: i64) -> u64 {
    ((v << 3) as u64) | TAG_SMALL
}

#[no_mangle]
pub extern "C" fn mana_rt_decode_packet(ctx: *mut ProcCtx, ty: u64, bin: u64, _opts: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    if ty & TAG_MASK != TAG_ATOM {
        return raise_badarg(ctx);
    }
    let Some((bp, blen)) = bin_parts(bin) else {
        return raise_badarg(ctx);
    };
    let bytes: Vec<u8> = unsafe { std::slice::from_raw_parts(bp, blen) }.to_vec();
    // Root the input binary across the parse. dp_ok slices the REST out of
    // the input. For a large tail, the slice is a view, not a copy. Bandit
    // feeds a shorter buffer on every call. A copy of every rest made header
    // parsing O(lines x buffer).
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, bin];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let slot = &fr[2] as *const u64;
    let base = bytes.as_ptr();
    let r = match atom_bytes(ty) {
        b"http_bin" => dp_http(ctx, slot, base, &bytes),
        b"httph_bin" => dp_httph(ctx, slot, base, &bytes),
        _ => {
            ctx.roots_head = saved;
            return raise_badarg(ctx);
        }
    };
    ctx.roots_head = saved;
    r
}

pub(crate) fn dp_more(ctx: &mut ProcCtx) -> u64 {
    pair_term(ctx, b"more", atom_intern(b"undefined"))
}

/// Build {ok, Packet, Rest}. Packet stays rooted across the Rest allocation.
/// `bin_slot` points at the GC-rooted original input term. `base` is the
/// start of the scratch copy. Rest becomes a slice of the ORIGINAL binary.
/// For a large tail, the slice is a zero-copy view.
pub(crate) fn dp_ok(
    ctx: &mut ProcCtx,
    packet: u64,
    bin_slot: *const u64,
    base: *const u8,
    rest: &[u8],
) -> u64 {
    let off = rest.as_ptr() as usize - base as usize;
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, NIL];
    fr[0] = saved;
    fr[2] = packet;
    ctx.roots_head = fr.as_ptr() as u64;
    let r = mana_rt_bin_slice(
        ctx as *mut ProcCtx,
        unsafe { *bin_slot },
        off as u64,
        rest.len() as i64,
    );
    let ctx = unsafe { &mut *(ctx as *mut ProcCtx) };
    fr[3] = r;
    let p = alloc_nursery(ctx, 4);
    unsafe {
        *p = (3 << 8) | KIND_TUPLE;
        *p.add(1) = atom_intern(b"ok");
        *p.add(2) = fr[2];
        *p.add(3) = fr[3];
    }
    ctx.roots_head = saved;
    p as u64
}

pub(crate) fn dp_http_error(
    ctx: &mut ProcCtx,
    bin_slot: *const u64,
    base: *const u8,
    line: &[u8],
    rest: &[u8],
) -> u64 {
    let lb = bytes_to_new_bin(ctx, line);
    let err = pair_term(ctx, b"http_error", lb); // pair_term roots lb internally
    dp_ok(ctx, err, bin_slot, base, rest)
}

/// Take one line, up to and including \r\n or \n. The function returns
/// (line_without terminator, rest_index). If the line is incomplete, it
/// returns None.
pub(crate) fn dp_line(bytes: &[u8]) -> Option<(&[u8], usize)> {
    let nl = bytes.iter().position(|&b| b == b'\n')?;
    let line = if nl > 0 && bytes[nl - 1] == b'\r' {
        &bytes[..nl - 1]
    } else {
        &bytes[..nl]
    };
    Some((line, nl + 1))
}

pub(crate) fn dp_http(
    ctx: &mut ProcCtx,
    bin_slot: *const u64,
    base: *const u8,
    bytes: &[u8],
) -> u64 {
    let Some((line, rest_at)) = dp_line(bytes) else {
        return dp_more(ctx);
    };
    let rest = &bytes[rest_at..];
    let full_line = &bytes[..rest_at];
    if line.starts_with(b"HTTP/") {
        return dp_response(ctx, bin_slot, base, line, full_line, rest);
    }
    // Request line: METHOD SP URI [SP HTTP/x.y]
    let mut parts = line.splitn(3, |&b| b == b' ');
    let method = parts.next().unwrap_or(b"");
    let Some(uri) = parts.next() else {
        return dp_http_error(ctx, bin_slot, base, full_line, rest);
    };
    let version = parts.next();
    if method.is_empty() || uri.is_empty() {
        return dp_http_error(ctx, bin_slot, base, full_line, rest);
    }
    let ver = match version {
        None => (0i64, 9i64),
        Some(v) => match dp_version(v) {
            Some(v) => v,
            None => return dp_http_error(ctx, bin_slot, base, full_line, rest),
        },
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 3, NIL, NIL, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    fr[2] = if let Some(name) = HTTP_METHODS.iter().find(|&&m| m.as_bytes() == method) {
        atom_intern(name.as_bytes())
    } else {
        bytes_to_new_bin(ctx, method)
    };
    fr[3] = dp_uri(ctx, uri);
    let vt = alloc_nursery(ctx, 3);
    unsafe {
        *vt = (2 << 8) | KIND_TUPLE;
        *vt.add(1) = small_of(ver.0);
        *vt.add(2) = small_of(ver.1);
    }
    fr[4] = vt as u64;
    let req = alloc_nursery(ctx, 5);
    unsafe {
        *req = (4 << 8) | KIND_TUPLE;
        *req.add(1) = atom_intern(b"http_request");
        *req.add(2) = fr[2];
        *req.add(3) = fr[3];
        *req.add(4) = fr[4];
    }
    ctx.roots_head = saved;
    dp_ok(ctx, req as u64, bin_slot, base, rest)
}

pub(crate) fn dp_version(v: &[u8]) -> Option<(i64, i64)> {
    let v = v.strip_prefix(b"HTTP/")?;
    let dot = v.iter().position(|&b| b == b'.')?;
    let major = std::str::from_utf8(&v[..dot]).ok()?.parse::<i64>().ok()?;
    let minor = std::str::from_utf8(&v[dot + 1..])
        .ok()?
        .parse::<i64>()
        .ok()?;
    Some((major, minor))
}

pub(crate) fn dp_response(
    ctx: &mut ProcCtx,
    bin_slot: *const u64,
    base: *const u8,
    line: &[u8],
    full_line: &[u8],
    rest: &[u8],
) -> u64 {
    let mut parts = line.splitn(3, |&b| b == b' ');
    let ver = parts.next().unwrap_or(b"");
    let Some(vt) = dp_version(ver) else {
        return dp_http_error(ctx, bin_slot, base, full_line, rest);
    };
    let Some(status) = parts.next() else {
        return dp_http_error(ctx, bin_slot, base, full_line, rest);
    };
    let Ok(code) = std::str::from_utf8(status).unwrap_or("x").parse::<i64>() else {
        return dp_http_error(ctx, bin_slot, base, full_line, rest);
    };
    let phrase = parts.next().unwrap_or(b"");
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    let vtt = alloc_nursery(ctx, 3);
    unsafe {
        *vtt = (2 << 8) | KIND_TUPLE;
        *vtt.add(1) = small_of(vt.0);
        *vtt.add(2) = small_of(vt.1);
    }
    fr[2] = vtt as u64;
    fr[3] = bytes_to_new_bin(ctx, phrase);
    let resp = alloc_nursery(ctx, 5);
    unsafe {
        *resp = (4 << 8) | KIND_TUPLE;
        *resp.add(1) = atom_intern(b"http_response");
        *resp.add(2) = fr[2];
        *resp.add(3) = small_of(code);
        *resp.add(4) = fr[3];
    }
    ctx.roots_head = saved;
    dp_ok(ctx, resp as u64, bin_slot, base, rest)
}

pub(crate) fn dp_uri(ctx: &mut ProcCtx, uri: &[u8]) -> u64 {
    if uri == b"*" {
        return atom_intern(b"*");
    }
    let lower: Vec<u8> = uri.to_ascii_lowercase();
    for (scheme, name) in [
        (b"http://".as_slice(), &b"http"[..]),
        (b"https://", b"https"),
    ] {
        if lower.starts_with(scheme) {
            let after = &uri[scheme.len()..];
            let path_at = after.iter().position(|&b| b == b'/').unwrap_or(after.len());
            let hostport = &after[..path_at];
            let path: &[u8] = if path_at == after.len() {
                b"/"
            } else {
                &after[path_at..]
            };
            let (host, port) = match hostport.iter().position(|&b| b == b':') {
                Some(c) => {
                    let p = std::str::from_utf8(&hostport[c + 1..])
                        .ok()
                        .and_then(|s| s.parse::<i64>().ok());
                    (&hostport[..c], p)
                }
                None => (hostport, None),
            };
            let saved = ctx.roots_head;
            let mut fr = [0u64, 2, NIL, NIL];
            fr[0] = saved;
            ctx.roots_head = fr.as_ptr() as u64;
            fr[2] = bytes_to_new_bin(ctx, host);
            fr[3] = bytes_to_new_bin(ctx, path);
            let t = alloc_nursery(ctx, 6);
            unsafe {
                *t = (5 << 8) | KIND_TUPLE;
                *t.add(1) = atom_intern(b"absoluteURI");
                *t.add(2) = atom_intern(name);
                *t.add(3) = fr[2];
                *t.add(4) = match port {
                    Some(p) => small_of(p),
                    None => atom_intern(b"undefined"),
                };
                *t.add(5) = fr[3];
            }
            ctx.roots_head = saved;
            return t as u64;
        }
    }
    if let Some(pos) = uri.windows(3).position(|w| w == b"://") {
        let saved = ctx.roots_head;
        let mut fr = [0u64, 2, NIL, NIL];
        fr[0] = saved;
        ctx.roots_head = fr.as_ptr() as u64;
        fr[2] = bytes_to_new_bin(ctx, &uri[..pos]);
        fr[3] = bytes_to_new_bin(ctx, &uri[pos + 3..]);
        let t = alloc_nursery(ctx, 4);
        unsafe {
            *t = (3 << 8) | KIND_TUPLE;
            *t.add(1) = atom_intern(b"scheme");
            *t.add(2) = fr[2];
            *t.add(3) = fr[3];
        }
        ctx.roots_head = saved;
        return t as u64;
    }
    if uri.first() == Some(&b'/') {
        let p = bytes_to_new_bin(ctx, uri);
        return pair_term(ctx, b"abs_path", p);
    }
    // Any other URI form, for example the token of an unknown method, is the
    // bare binary.
    bytes_to_new_bin(ctx, uri)
}

pub(crate) fn dp_httph(
    ctx: &mut ProcCtx,
    bin_slot: *const u64,
    base: *const u8,
    bytes: &[u8],
) -> u64 {
    let Some((line, mut rest_at)) = dp_line(bytes) else {
        return dp_more(ctx);
    };
    if line.is_empty() {
        return dp_ok(
            ctx,
            atom_intern(b"http_eoh"),
            bin_slot,
            base,
            &bytes[rest_at..],
        );
    }
    if rest_at == bytes.len() {
        // An obs-fold continuation can still extend a complete header line.
        // BEAM waits for at least one more byte.
        return dp_more(ctx);
    }
    let full_line = &bytes[..rest_at];
    let Some(colon) = line.iter().position(|&b| b == b':') else {
        return dp_http_error(ctx, bin_slot, base, full_line, &bytes[rest_at..]);
    };
    let name = &line[..colon];
    let mut value: Vec<u8> = line[colon + 1..]
        .iter()
        .copied()
        .skip_while(|&b| b == b' ' || b == b'\t')
        .collect();
    // obs-fold: a continuation line starts with SP or HT and extends the value
    // RAW. BEAM keeps the CRLF and the leading whitespace unchanged.
    while rest_at < bytes.len() && (bytes[rest_at] == b' ' || bytes[rest_at] == b'\t') {
        let Some((cont, next_at)) = dp_line(&bytes[rest_at..]) else {
            return dp_more(ctx);
        };
        value.extend_from_slice(b"\r\n");
        value.extend_from_slice(cont);
        rest_at += next_at;
    }
    let rest = &bytes[rest_at..];
    let canon = canonical_field(name);
    let (idx, field_term_is_atom) = match HTTP_FIELDS
        .iter()
        .position(|&f| f.as_bytes() == canon.as_slice())
    {
        Some(i) => (i as i64 + 1, true),
        None => (0, false),
    };
    let saved = ctx.roots_head;
    let mut fr = [0u64, 2, NIL, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    fr[2] = if field_term_is_atom {
        atom_intern(HTTP_FIELDS[(idx - 1) as usize].as_bytes())
    } else {
        bytes_to_new_bin(ctx, &canon)
    };
    fr[3] = bytes_to_new_bin(ctx, &value);
    // The 4th element is the field name as received, in the original case
    // (OTP 26+).
    let orig = bytes_to_new_bin(ctx, name);
    let mut fr2 = [0u64, 1, orig];
    fr2[0] = ctx.roots_head;
    ctx.roots_head = fr2.as_ptr() as u64;
    let h = alloc_nursery(ctx, 6);
    unsafe {
        *h = (5 << 8) | KIND_TUPLE;
        *h.add(1) = atom_intern(b"http_header");
        *h.add(2) = small_of(idx);
        *h.add(3) = fr[2];
        *h.add(4) = fr2[2];
        *h.add(5) = fr[3];
    }
    ctx.roots_head = saved;
    dp_ok(ctx, h as u64, bin_slot, base, rest)
}
