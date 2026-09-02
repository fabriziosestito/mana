//! Native JSON for apps compiled with mana — the `native/` crate of the
//! `mana_json` hex package. Two BIFs back `ManaJSON`:
//! `mana_json_native:encode/1` and `decode/1`, term <-> JSON via serde_json.
//!
//! Term <-> JSON correspondence (mirrors the reference Go mana_json):
//!   - atom :nil / :null  -> JSON null ; JSON null -> :nil on decode
//!   - :true / :false     -> JSON booleans
//!   - other atoms        -> their name as a JSON string
//!   - integer / float    -> JSON number (decode: i64, else float, like the
//!                           Go reference; encode preserves bignums exactly)
//!   - binary             -> JSON string (UTF-8)
//!   - proper list / nil  -> JSON array (improper list -> {:error, ...})
//!   - map                -> JSON object; keys must be atom/binary/integer;
//!                           object keys decode to binaries
//!   - tuple              -> {:error, :unsupported}

use mana_native::{Env, ProcCtx, Term, H};
use serde_json::Value;

#[no_mangle]
pub extern "C" fn mana_json_native_encode_1(ctx: *mut ProcCtx, term: u64) -> u64 {
    let value = match term_to_value(Term(term)) {
        Ok(v) => v,
        Err(reason) => return build_error(ctx, reason),
    };
    let bytes = match serde_json::to_vec(&value) {
        Ok(b) => b,
        Err(_) => return build_error(ctx, b"encode_error"),
    };
    let mut env = unsafe { Env::new(ctx) };
    let bin = env.binary(&bytes);
    let ok = env.atom(b"ok");
    let t = env.tuple(&[ok, bin]);
    env.get(t)
}

#[no_mangle]
pub extern "C" fn mana_json_native_decode_1(ctx: *mut ProcCtx, input: u64) -> u64 {
    // borrows the process heap; serde parses into a Rust-heap Value with no
    // mana allocation, so the borrow stays valid until we start building
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

// -- term -> serde_json::Value (read-only walk; no mana allocation) --

fn term_to_value(t: Term) -> Result<Value, &'static [u8]> {
    if t.is_nil() {
        return Ok(Value::Array(Vec::new()));
    }
    if t.is_small() || t.is_bignum() {
        return Ok(int_to_value(t));
    }
    if t.is_float() {
        return match serde_json::Number::from_f64(t.as_float()) {
            Some(n) => Ok(Value::Number(n)),
            None => Err(b"non_finite_float"),
        };
    }
    if t.is_atom() {
        return Ok(match t.atom_name() {
            b"null" | b"nil" => Value::Null,
            b"true" => Value::Bool(true),
            b"false" => Value::Bool(false),
            name => Value::String(String::from_utf8_lossy(name).into_owned()),
        });
    }
    if let Some(bytes) = t.binary_bytes() {
        return Ok(Value::String(String::from_utf8_lossy(bytes).into_owned()));
    }
    if t.is_cons() {
        let mut arr = Vec::new();
        let mut cur = t;
        loop {
            if cur.is_nil() {
                return Ok(Value::Array(arr));
            }
            if !cur.is_cons() {
                return Err(b"improper_list");
            }
            arr.push(term_to_value(cur.cons_head())?);
            cur = cur.cons_tail();
        }
    }
    if t.is_map() {
        let n = t.map_size();
        let mut obj = serde_json::Map::new();
        for i in 0..n {
            let k = t.map_key(i);
            let key = if k.is_atom() {
                String::from_utf8_lossy(k.atom_name()).into_owned()
            } else if let Some(kb) = k.binary_bytes() {
                String::from_utf8_lossy(kb).into_owned()
            } else if k.is_small() || k.is_bignum() {
                let mut buf = [0u8; 64];
                let len = k.int_decimal(&mut buf).unwrap_or(0).min(buf.len());
                String::from_utf8_lossy(&buf[..len]).into_owned()
            } else {
                return Err(b"bad_key");
            };
            obj.insert(key, term_to_value(t.map_val(i))?);
        }
        return Ok(Value::Object(obj));
    }
    Err(b"unsupported")
}

/// Any integer term -> a JSON number, preserving bignums exactly via their
/// decimal digits (serde_json's arbitrary_precision keeps the literal).
fn int_to_value(t: Term) -> Value {
    let mut buf = [0u8; 64];
    let n = t.int_decimal(&mut buf).unwrap();
    if n <= buf.len() {
        serde_json::from_slice(&buf[..n]).unwrap()
    } else {
        let mut v = vec![0u8; n];
        t.int_decimal(&mut v);
        serde_json::from_slice(&v).unwrap()
    }
}

// -- serde_json::Value -> term (rooted build through the Env) --

fn value_to_term(env: &mut Env, v: &Value) -> H {
    match v {
        Value::Null => env.atom(b"nil"),
        Value::Bool(true) => env.atom(b"true"),
        Value::Bool(false) => env.atom(b"false"),
        Value::Number(n) => {
            // arbitrary_precision: the literal is available as a string
            let s = n.as_str();
            if s.bytes().any(|c| c == b'.' || c == b'e' || c == b'E') {
                env.float(s.parse::<f64>().unwrap_or(0.0))
            } else if let Ok(i) = s.parse::<i64>() {
                env.int(i)
            } else {
                // out of i64 range: match the Go reference (fall back to
                // float) rather than a lossy path we can't round-trip
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
