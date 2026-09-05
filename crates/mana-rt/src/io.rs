//! Term output and the native `io` BIFs.
//!
//! This module holds `erlang:display/1`, the uncaught-exception printer,
//! the `io` and `io_lib` format engine, the `unicode` conversions, and the
//! term writer. The runtime never compiles the OTP `io.erl` or the
//! group-leader protocol. The BIFs write to stdout directly. The term writer
//! must print terms in the same form as BEAM.

use super::*;

// Term output

/// `erlang:display/1`. Prints a term and then a newline.
#[no_mangle]
pub extern "C" fn mana_rt_display(term: u64) {
    let mut out = String::new();
    write_term(term, &mut out);
    out.push('\n');
    let _ = std::io::stdout().write_all(out.as_bytes());
}

/// Reports an exception that unwound past the entry function. The process
/// exits with status 1.
#[no_mangle]
pub extern "C" fn mana_rt_uncaught(ctx: *mut ProcCtx) -> ! {
    let ctx = unsafe { &*ctx };
    let mut class = String::new();
    let mut reason = String::new();
    write_term(ctx.exc_class, &mut class);
    write_term(ctx.exc_reason, &mut reason);
    eprintln!("** exception {}: {}", class, reason);
    std::process::exit(1);
}

// io BIFs

/// `io:put_chars/1`. Writes iodata to stdout and returns `ok`. The chardata
/// is restricted to bytes. TODO(unicode): code points beyond latin-1.
#[no_mangle]
pub extern "C" fn mana_rt_io_put_chars(ctx: *mut ProcCtx, data: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut out = Vec::new();
    if iolist_flatten(data, &mut out).is_err() {
        return raise_badarg(ctx);
    }
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut lock = stdout.lock();
    if lock.write_all(&out).and_then(|_| lock.flush()).is_err() {
        return raise_badarg(ctx);
    }
    known().ok
}

/// Flattens chardata. The walk is like an iolist walk, but each integer is a
/// Unicode code point and is written as utf8, not as a byte. Binaries are
/// copied raw. The function assumes that binaries hold utf8.
pub(crate) fn chardata_flatten(t: u64, out: &mut Vec<u8>) -> Result<(), ()> {
    if let Some((p, n)) = bin_parts(t) {
        out.extend_from_slice(unsafe { std::slice::from_raw_parts(p, n) });
        return Ok(());
    }
    let mut cur = t;
    loop {
        if cur == NIL {
            return Ok(());
        }
        if cur & TAG_MASK != TAG_CONS {
            if bin_parts(cur).is_some() {
                return chardata_flatten(cur, out);
            }
            return Err(());
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK == TAG_SMALL {
            let cp = h as i64 >> 3;
            let c = u32::try_from(cp).ok().and_then(char::from_u32).ok_or(())?;
            let mut buf = [0u8; 4];
            out.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
        } else {
            chardata_flatten(h, out)?;
        }
        cur = unsafe { *p.add(1) };
    }
}

/// `unicode:characters_to_nfc_list/1`. Returns the NFC-normalized code point
/// list. `String.Tokenizer` validates identifiers through this BIF.
#[no_mangle]
pub extern "C" fn mana_rt_unicode_to_nfc_list(ctx: *mut ProcCtx, t: u64) -> u64 {
    use unicode_normalization::UnicodeNormalization;
    let ctx = unsafe { &mut *ctx };
    let mut bytes = Vec::new();
    if chardata_flatten(t, &mut bytes).is_err() {
        return raise_badarg(ctx);
    }
    let Ok(s) = std::str::from_utf8(&bytes) else {
        return raise_badarg(ctx);
    };
    let nfc: String = s.nfc().collect();
    utf8_to_codepoint_list(ctx, nfc.as_bytes())
}

/// `unicode:characters_to_binary/1`. The input is utf8 and the output is utf8.
#[no_mangle]
pub extern "C" fn mana_rt_unicode_to_binary(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut out = Vec::new();
    match chardata_flatten(t, &mut out) {
        Ok(()) => bytes_to_new_bin(ctx, &out),
        Err(()) => raise_badarg(ctx),
    }
}

/// `unicode:characters_to_list/1`. Returns the code point list of utf8 chardata.
#[no_mangle]
pub extern "C" fn mana_rt_unicode_to_list(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut bytes = Vec::new();
    if chardata_flatten(t, &mut bytes).is_err() {
        return raise_badarg(ctx);
    }
    let Ok(s) = std::str::from_utf8(&bytes) else {
        return raise_badarg(ctx);
    };
    let cps: Vec<u64> = s.chars().map(|c| ((c as u64) << 3) | TAG_SMALL).collect();
    // The loop builds the list from the tail to the head. The code points are
    // immediates. Only the partial list needs a GC root.
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &cp in cps.iter().rev() {
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = cp;
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[2]
}

/// The `io_lib` format engine. It accepts `~[F][.P][t]C` for `C` in
/// `s f e p w n ~`. A `*` width or precision takes its value from the
/// argument list. A negative width means left alignment. This is the subset
/// that the benchee console uses. Unknown directives print their raw text.
pub(crate) fn format_engine(fmt: u64, args: u64) -> Result<Vec<u8>, ()> {
    let mut fbytes = Vec::new();
    chardata_flatten(fmt, &mut fbytes)?;
    let mut argv = Vec::new();
    let mut cur = args;
    while cur != NIL {
        if cur & TAG_MASK != TAG_CONS {
            return Err(());
        }
        let p = (cur & !TAG_MASK) as *const u64;
        unsafe {
            argv.push(*p);
            cur = *p.add(1);
        }
    }
    let mut out = Vec::new();
    let mut ai = 0;
    let mut i = 0;
    let mut next_arg = |ai: &mut usize| -> u64 {
        let v = argv.get(*ai).copied().unwrap_or(NIL);
        *ai += 1;
        v
    };
    while i < fbytes.len() {
        let b = fbytes[i];
        if b != b'~' || i + 1 >= fbytes.len() {
            out.push(b);
            i += 1;
            continue;
        }
        let mut j = i + 1;
        // Field width: `[-]digits` or `*`.
        let mut width: Option<i64> = None;
        let mut neg = false;
        if fbytes.get(j) == Some(&b'-') {
            neg = true;
            j += 1;
        }
        if fbytes.get(j) == Some(&b'*') {
            let w = next_arg(&mut ai);
            if w & TAG_MASK == TAG_SMALL {
                width = Some(w as i64 >> 3);
            }
            j += 1;
        } else {
            let mut digits = 0i64;
            let mut any = false;
            while let Some(&d) = fbytes.get(j) {
                if d.is_ascii_digit() {
                    digits = digits * 10 + (d - b'0') as i64;
                    any = true;
                    j += 1;
                } else {
                    break;
                }
            }
            if any {
                width = Some(if neg { -digits } else { digits });
            }
        }
        // Precision: `.digits` or `.*`.
        let mut prec: Option<usize> = None;
        if fbytes.get(j) == Some(&b'.') {
            j += 1;
            if fbytes.get(j) == Some(&b'*') {
                let p = next_arg(&mut ai);
                if p & TAG_MASK == TAG_SMALL {
                    prec = Some((p as i64 >> 3).max(0) as usize);
                }
                j += 1;
            } else {
                let mut digits = 0usize;
                while let Some(&d) = fbytes.get(j) {
                    if d.is_ascii_digit() {
                        digits = digits * 10 + (d - b'0') as usize;
                        j += 1;
                    } else {
                        break;
                    }
                }
                prec = Some(digits);
            }
        }
        // The `t` and `l` modifiers are accepted and ignored.
        while matches!(fbytes.get(j), Some(b't') | Some(b'l')) {
            j += 1;
        }
        let pad = |out: &mut Vec<u8>, piece: Vec<u8>, width: Option<i64>| match width {
            Some(w) => {
                let w_abs = w.unsigned_abs() as usize;
                let fill = w_abs.saturating_sub(piece.len());
                if w < 0 {
                    out.extend_from_slice(&piece);
                    out.extend(std::iter::repeat(b' ').take(fill));
                } else {
                    out.extend(std::iter::repeat(b' ').take(fill));
                    out.extend_from_slice(&piece);
                }
            }
            None => out.extend_from_slice(&piece),
        };
        match fbytes.get(j) {
            Some(b'n') => out.push(b'\n'),
            Some(b'~') => out.push(b'~'),
            Some(b's') => {
                let a = next_arg(&mut ai);
                let mut piece = Vec::new();
                if a & TAG_MASK == TAG_ATOM {
                    piece.extend_from_slice(atom_bytes(a));
                } else {
                    chardata_flatten(a, &mut piece)?;
                }
                pad(&mut out, piece, width);
            }
            Some(b'f') => {
                let a = next_arg(&mut ai);
                let Some((x, _)) = num_of(a) else {
                    return Err(());
                };
                let piece = format!("{:.*}", prec.unwrap_or(6), x).into_bytes();
                pad(&mut out, piece, width);
            }
            Some(b'e') => {
                let a = next_arg(&mut ai);
                let Some((x, _)) = num_of(a) else {
                    return Err(());
                };
                let piece = display_float(x).into_bytes();
                pad(&mut out, piece, width);
            }
            Some(b'p') | Some(b'w') => {
                let a = next_arg(&mut ai);
                let mut s = String::new();
                write_term(a, &mut s);
                pad(&mut out, s.into_bytes(), width);
            }
            Some(&other) => {
                out.push(b'~');
                out.push(other);
            }
            None => out.push(b'~'),
        }
        i = j + 1;
    }
    Ok(out)
}

/// `io:format/2`.
#[no_mangle]
pub extern "C" fn mana_rt_io_format(ctx: *mut ProcCtx, fmt: u64, args: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Ok(out) = format_engine(fmt, args) else {
        return raise_badarg(ctx);
    };
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut lock = stdout.lock();
    if lock.write_all(&out).and_then(|_| lock.flush()).is_err() {
        return raise_badarg(ctx);
    }
    known().ok
}

/// Builds a charlist of bytes in the nursery. The caller must copy the bytes
/// off the heap first.
pub(crate) fn bytes_to_charlist(ctx: &mut ProcCtx, bytes: &[u8]) -> u64 {
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &b in bytes.iter().rev() {
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = ((b as u64) << 3) | TAG_SMALL;
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[2]
}

/// Builds a charlist of code points from utf8 bytes. This is the `io_lib`
/// behavior. The byte behavior of `binary_to_list` is in `bytes_to_charlist`.
pub(crate) fn utf8_to_codepoint_list(ctx: &mut ProcCtx, bytes: &[u8]) -> u64 {
    let s = String::from_utf8_lossy(bytes);
    let cps: Vec<u64> = s.chars().map(|c| ((c as u64) << 3) | TAG_SMALL).collect();
    let saved = ctx.roots_head;
    let mut fr = [0u64, 1, NIL];
    fr[0] = saved;
    ctx.roots_head = fr.as_ptr() as u64;
    for &cp in cps.iter().rev() {
        let cell = alloc_nursery(ctx, 2);
        unsafe {
            *cell = cp;
            *cell.add(1) = fr[2];
        }
        fr[2] = cell as u64 | TAG_CONS;
    }
    ctx.roots_head = saved;
    fr[2]
}

/// `io_lib:format/2`. Returns the formatted text as a code point charlist.
#[no_mangle]
pub extern "C" fn mana_rt_io_lib_format(ctx: *mut ProcCtx, fmt: u64, args: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let Ok(out) = format_engine(fmt, args) else {
        return raise_badarg(ctx);
    };
    utf8_to_codepoint_list(ctx, &out)
}

/// `io_lib:write/1`. Returns the display text of a term. `io_lib:write/2`
/// also maps here and ignores the depth argument.
#[no_mangle]
pub extern "C" fn mana_rt_io_lib_write(ctx: *mut ProcCtx, t: u64) -> u64 {
    let ctx = unsafe { &mut *ctx };
    let mut s = String::new();
    write_term(t, &mut s);
    utf8_to_codepoint_list(ctx, s.as_bytes())
}

pub(crate) fn write_term(t: u64, out: &mut String) {
    match t & TAG_MASK {
        TAG_SMALL => {
            out.push_str(&((t as i64) >> 3).to_string());
        }
        TAG_ATOM => unsafe {
            let p = (t & !TAG_MASK) as *const u64;
            let len = *p as usize;
            let bytes = std::slice::from_raw_parts(p.add(1) as *const u8, len);
            write_atom(&String::from_utf8_lossy(bytes), out);
        },
        _ if t == NIL => out.push_str("[]"),
        TAG_PID => {
            if t & 0xF == PID_TAG4 {
                out.push_str(&format!("<0.{}.0>", t >> 4));
            } else {
                out.push_str(&format!("#Ref<0.{}>", t >> 4));
            }
        }
        TAG_CONS => {
            // BEAM prints a proper list of printable characters as a string.
            if let Some(s) = printable_list(t) {
                out.push('"');
                out.push_str(&s);
                out.push('"');
                return;
            }
            out.push('[');
            let mut cur = t;
            loop {
                unsafe {
                    let p = (cur & !TAG_MASK) as *const u64;
                    write_term(*p, out);
                    let tail = *p.add(1);
                    if tail == NIL {
                        break;
                    } else if tail & TAG_MASK == TAG_CONS {
                        out.push(',');
                        cur = tail;
                    } else {
                        out.push('|');
                        write_term(tail, out);
                        break;
                    }
                }
            }
            out.push(']');
        }
        TAG_BOXED => unsafe {
            let p = t as *const u64;
            let header = *p;
            match header & 0xff {
                KIND_TUPLE => {
                    let arity = (header >> 8) as usize;
                    out.push('{');
                    for i in 0..arity {
                        if i > 0 {
                            out.push(',');
                        }
                        write_term(*p.add(1 + i), out);
                    }
                    out.push('}');
                }
                KIND_FLOAT => {
                    let f = f64::from_bits(*p.add(1));
                    out.push_str(&display_float(f));
                }
                KIND_FUN => out.push_str("#Fun<mana>"),
                KIND_MAP => {
                    let n = (header >> 8) as usize;
                    out.push_str("#{");
                    for i in 0..n {
                        if i > 0 {
                            out.push(',');
                        }
                        write_term(*p.add(1 + i), out);
                        out.push_str("=>");
                        write_term(*p.add(1 + n + i), out);
                    }
                    out.push('}');
                }
                KIND_BIGNUM => {
                    let (neg, mag) = bignum_parts(t).unwrap();
                    if neg {
                        out.push('-');
                    }
                    out.push_str(&bigint::mag_to_decimal(mag));
                }
                KIND_BIN | KIND_SUBBIN => {
                    let bytes = bin_bytes(t);
                    out.push_str("<<");
                    // A binary of printable ASCII bytes prints as a string.
                    // Control characters do not qualify here. This differs
                    // from the rule for charlists.
                    if !bytes.is_empty() && bytes.iter().all(|&b| (0x20..=0x7e).contains(&b)) {
                        out.push('"');
                        for &b in bytes {
                            // Only the quote gets an escape. A backslash prints raw.
                            if b == b'"' {
                                out.push('\\');
                            }
                            out.push(b as char);
                        }
                        out.push('"');
                    } else {
                        for (i, b) in bytes.iter().enumerate() {
                            if i > 0 {
                                out.push(',');
                            }
                            out.push_str(&b.to_string());
                        }
                    }
                    out.push_str(">>");
                }
                _ => out.push_str("#<unknown-boxed>"),
            }
        },
        _ => out.push_str("#<unknown>"),
    }
}

/// Writes an atom in the form that BEAM uses. BEAM quotes an atom that is not
/// a plain identifier (`[a-z][a-zA-Z0-9_@]*`). BEAM also quotes an atom that
/// is an Erlang reserved word. `'` and `\` get an escape. Other characters
/// print raw. This matches `display`, not `~p`.
pub(crate) fn write_atom(name: &str, out: &mut String) {
    const RESERVED: &[&str] = &[
        "after", "and", "andalso", "band", "begin", "bnot", "bor", "bsl", "bsr", "bxor", "case",
        "catch", "cond", "div", "end", "fun", "if", "let", "maybe", "not", "of", "or", "orelse",
        "receive", "rem", "try", "when", "xor",
    ];
    let plain = !name.is_empty()
        && name.as_bytes()[0].is_ascii_lowercase()
        && name
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'@')
        && !RESERVED.contains(&name);
    if plain {
        out.push_str(name);
        return;
    }
    out.push('\'');
    for c in name.chars() {
        if c == '\'' || c == '\\' {
            out.push('\\');
        }
        out.push(c);
    }
    out.push('\'');
}

/// The display rule of BEAM for lists. A proper list of printable latin-1
/// characters, or of their escapes, prints as a quoted string. Returns the
/// escaped body of the string, or `None` if the list does not qualify.
pub(crate) fn printable_list(t: u64) -> Option<String> {
    let mut s = String::new();
    let mut cur = t;
    loop {
        if cur == NIL {
            return if s.is_empty() { None } else { Some(s) };
        }
        if cur & TAG_MASK != TAG_CONS {
            return None;
        }
        let p = (cur & !TAG_MASK) as *const u64;
        let h = unsafe { *p };
        if h & TAG_MASK != TAG_SMALL {
            return None;
        }
        let c = (h as i64) >> 3;
        match c {
            32..=126 => {
                let ch = c as u8 as char;
                if ch == '"' || ch == '\\' {
                    s.push('\\');
                }
                s.push(ch);
            }
            // BEAM writes these characters raw inside the quotes.
            8..=13 | 27 => s.push(c as u8 as char),
            _ => return None,
        }
        cur = unsafe { *p.add(1) };
    }
}
