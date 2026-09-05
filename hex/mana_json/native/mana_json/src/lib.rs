//! Native JSON for apps that mana compiles. This is the `native/` crate of
//! the `mana_json` hex package. Two BIFs back `ManaJSON`:
//! `mana_json_native:encode/1` and `decode/1`. They convert between terms
//! and JSON with serde_json.
//!
//! Term <-> JSON correspondence:
//!   - atom :nil / :null  -> JSON null. JSON null -> :nil on decode.
//!   - :true / :false     -> JSON booleans
//!   - other atoms        -> their name as a JSON string
//!   - integer / float    -> JSON number. Decode gives i64, else float.
//!                           Encode keeps bignums exact.
//!   - binary             -> JSON string (UTF-8)
//!   - proper list / nil  -> JSON array. An improper list -> {:error, ...}.
//!   - map                -> JSON object. Keys must be atom, binary, or
//!                           integer. Object keys decode to binaries.
//!   - tuple              -> {:error, :unsupported}

use mana_native::{Env, ProcCtx, Term, H};
use serde_json::Value;

#[no_mangle]
pub extern "C" fn mana_json_native_encode_1(ctx: *mut ProcCtx, term: u64) -> u64 {
    // The walk writes the term straight into a byte buffer. There is no
    // serde_json::Value tree and no second serialization pass. The walk is
    // read-only over the process heap. No mana allocation happens until the
    // result is built below.
    let mut out = Vec::new();
    if let Err(reason) = encode_term(Term(term), &mut out) {
        return build_error(ctx, reason);
    }
    let mut env = unsafe { Env::new(ctx) };
    let bin = env.binary(&out);
    let ok = env.atom(b"ok");
    let t = env.tuple(&[ok, bin]);
    env.get(t)
}

#[no_mangle]
pub extern "C" fn mana_json_native_decode_1(ctx: *mut ProcCtx, input: u64) -> u64 {
    // The slice borrows the process heap. serde parses into a Value on the
    // Rust heap with no mana allocation. The borrow stays valid until the
    // result build starts.
    let bytes = match Term(input).binary_bytes() {
        Some(b) => b,
        None => return build_error(ctx, b"badarg"),
    };
    let value: Value = match serde_json::from_slice(bytes) {
        Ok(v) => v,
        Err(_) => return build_error(ctx, b"decode_error"),
    };
    let mut env = unsafe { Env::new(ctx) };
    let h = value_to_term(&mut env, &value);
    let ok = env.atom(b"ok");
    let t = env.tuple(&[ok, h]);
    env.get(t)
}

fn build_error(ctx: *mut ProcCtx, reason: &[u8]) -> u64 {
    let mut env = unsafe { Env::new(ctx) };
    let err = env.atom(b"error");
    let r = env.atom(reason);
    let t = env.tuple(&[err, r]);
    env.get(t)
}

// Term -> JSON bytes. The walk is read-only. It makes no mana allocation and
// no Value tree.

fn encode_term(t: Term, out: &mut Vec<u8>) -> Result<(), &'static [u8]> {
    if t.is_nil() {
        out.extend_from_slice(b"[]");
        return Ok(());
    }
    if t.is_small() || t.is_bignum() {
        write_int(t, out);
        return Ok(());
    }
    if t.is_float() {
        let f = t.as_float();
        if !f.is_finite() {
            return Err(b"non_finite_float");
        }
        // ryu is the float formatter of serde_json. It gives the shortest
        // round-trip form. The output always has a '.' or an exponent, so
        // decode reads it back as a float.
        let mut buf = ryu::Buffer::new();
        out.extend_from_slice(buf.format(f).as_bytes());
        return Ok(());
    }
    if t.is_atom() {
        match t.atom_name() {
            b"null" | b"nil" => out.extend_from_slice(b"null"),
            b"true" => out.extend_from_slice(b"true"),
            b"false" => out.extend_from_slice(b"false"),
            name => write_json_string(name, out),
        }
        return Ok(());
    }
    if let Some(bytes) = t.binary_bytes() {
        write_json_string(bytes, out);
        return Ok(());
    }
    if t.is_cons() {
        out.push(b'[');
        let mut cur = t;
        let mut first = true;
        loop {
            if cur.is_nil() {
                break;
            }
            if !cur.is_cons() {
                return Err(b"improper_list");
            }
            if !first {
                out.push(b',');
            }
            first = false;
            encode_term(cur.cons_head(), out)?;
            cur = cur.cons_tail();
        }
        out.push(b']');
        return Ok(());
    }
    if t.is_map() {
        out.push(b'{');
        let n = t.map_size();
        for i in 0..n {
            if i > 0 {
                out.push(b',');
            }
            write_key(t.map_key(i), out)?;
            out.push(b':');
            encode_term(t.map_val(i), out)?;
        }
        out.push(b'}');
        return Ok(());
    }
    Err(b"unsupported")
}

/// Write any integer term as its decimal digits. Bignums stay exact.
fn write_int(t: Term, out: &mut Vec<u8>) {
    let mut buf = [0u8; 64];
    let n = t.int_decimal(&mut buf).unwrap();
    if n <= buf.len() {
        out.extend_from_slice(&buf[..n]);
    } else {
        let mut v = vec![0u8; n];
        t.int_decimal(&mut v);
        out.extend_from_slice(&v);
    }
}

/// Write a map key as a JSON string. A key must be an atom, a binary, or an
/// integer. An integer key becomes its decimal digits as a string. Any other
/// key is a bad key.
fn write_key(k: Term, out: &mut Vec<u8>) -> Result<(), &'static [u8]> {
    if k.is_atom() {
        write_json_string(k.atom_name(), out);
    } else if let Some(kb) = k.binary_bytes() {
        write_json_string(kb, out);
    } else if k.is_small() || k.is_bignum() {
        out.push(b'"');
        write_int(k, out);
        out.push(b'"');
    } else {
        return Err(b"bad_key");
    }
    Ok(())
}

/// Write a JSON string for arbitrary bytes. Valid UTF-8 is escaped in place.
/// Invalid UTF-8 sequences are replaced with U+FFFD. This replacement is
/// lossy.
fn write_json_string(bytes: &[u8], out: &mut Vec<u8>) {
    match std::str::from_utf8(bytes) {
        Ok(s) => escape_str(s.as_bytes(), out),
        Err(_) => {
            let s = String::from_utf8_lossy(bytes);
            escape_str(s.as_bytes(), out)
        }
    }
}

/// The default string escaping of serde_json. The function escapes `"`, `\`,
/// and the C0 control characters. It uses the short escapes \b \t \n \f \r
/// where they exist, and \u00XX otherwise. Non-ASCII bytes and `/` pass
/// through without an escape.
fn escape_str(bytes: &[u8], out: &mut Vec<u8>) {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    out.push(b'"');
    let mut start = 0;
    for (i, &b) in bytes.iter().enumerate() {
        let short: &[u8] = match b {
            b'"' => b"\\\"",
            b'\\' => b"\\\\",
            0x08 => b"\\b",
            0x0c => b"\\f",
            b'\n' => b"\\n",
            b'\r' => b"\\r",
            b'\t' => b"\\t",
            0x00..=0x1f => {
                out.extend_from_slice(&bytes[start..i]);
                out.extend_from_slice(b"\\u00");
                out.push(HEX[(b >> 4) as usize]);
                out.push(HEX[(b & 0xf) as usize]);
                start = i + 1;
                continue;
            }
            _ => continue,
        };
        out.extend_from_slice(&bytes[start..i]);
        out.extend_from_slice(short);
        start = i + 1;
    }
    out.extend_from_slice(&bytes[start..]);
    out.push(b'"');
}

fn value_to_term(env: &mut Env, v: &Value) -> H {
    match v {
        Value::Null => env.atom(b"nil"),
        Value::Bool(true) => env.atom(b"true"),
        Value::Bool(false) => env.atom(b"false"),
        Value::Number(n) => {
            // With arbitrary_precision, the number literal is available as a
            // string.
            let s = n.as_str();
            if s.bytes().any(|c| c == b'.' || c == b'e' || c == b'E') {
                env.float(s.parse::<f64>().unwrap_or(0.0))
            } else if let Ok(i) = s.parse::<i64>() {
                env.int(i)
            } else {
                // The integer is out of the i64 range. A float is the
                // fallback. The other paths are lossy and cannot round-trip.
                env.float(s.parse::<f64>().unwrap_or(0.0))
            }
        }
        Value::String(s) => env.binary(s.as_bytes()),
        Value::Array(items) => {
            let hs: Vec<H> = items.iter().map(|it| value_to_term(env, it)).collect();
            env.list(&hs)
        }
        Value::Object(map) => {
            let pairs: Vec<(H, H)> = map
                .iter()
                .map(|(k, val)| {
                    let kh = env.binary(k.as_bytes());
                    let vh = value_to_term(env, val);
                    (kh, vh)
                })
                .collect();
            env.map(&pairs)
        }
    }
}
