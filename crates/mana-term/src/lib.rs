//! Term representation constants and pure term formatting, shared by every
//! runtime flavor (mana-rt, mana-rt-mmtk). No `#[no_mangle]` symbols here —
//! runtimes wrap these in their own extern "C" surface.
//!
//! See mana-rt's crate docs for the full tag/header contract.

pub const TAG_MASK: u64 = 0b111;
pub const TAG_BOXED: u64 = 0b000;
pub const TAG_SMALL: u64 = 0b001;
pub const TAG_ATOM: u64 = 0b010;
pub const NIL: u64 = 0b011;
pub const TAG_FORWARD: u64 = 0b111;

pub const KIND_TUPLE: u64 = 0;
pub const KIND_FLOAT: u64 = 1;
pub const KIND_FUN: u64 = 2;
pub const KIND_CONS: u64 = 3;
pub const CONS_HEADER: u64 = (2 << 8) | KIND_CONS;

pub fn payload_words(header: u64) -> usize {
    match header & 0xff {
        KIND_TUPLE => (header >> 8) as usize,
        KIND_FLOAT => 1,
        KIND_FUN => 1 + (header >> 16) as usize,
        KIND_CONS => 2,
        _ => 0,
    }
}

/// Format a term the way `erlang:display/1` prints it.
///
/// # Safety
/// `t` must be a valid term whose heap objects are readable.
pub unsafe fn write_term(t: u64, out: &mut String) {
    match t & TAG_MASK {
        TAG_SMALL => {
            out.push_str(&((t as i64) >> 3).to_string());
        }
        TAG_ATOM => unsafe {
            let p = (t & !TAG_MASK) as *const u64;
            let len = *p as usize;
            let bytes = std::slice::from_raw_parts(p.add(1) as *const u8, len);
            out.push_str(&String::from_utf8_lossy(bytes));
        },
        _ if t == NIL => out.push_str("[]"),
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
                    out.push_str(&format!("{:?}", f));
                }
                KIND_FUN => out.push_str("#Fun<mana>"),
                KIND_CONS => {
                    out.push('[');
                    let mut q = p;
                    loop {
                        write_term(*q.add(1), out);
                        let tail = *q.add(2);
                        if tail == NIL {
                            break;
                        } else if tail & TAG_MASK == TAG_BOXED
                            && tail != 0
                            && *(tail as *const u64) & 0xff == KIND_CONS
                        {
                            out.push(',');
                            q = tail as *const u64;
                        } else {
                            out.push('|');
                            write_term(tail, out);
                            break;
                        }
                    }
                    out.push(']');
                }
                _ => out.push_str("#<unknown-boxed>"),
            }
        },
        _ => out.push_str("#<unknown>"),
    }
}
