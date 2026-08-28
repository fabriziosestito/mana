//! mana runtime — milestone 1: sequential programs, no GC (allocations leak).
//!
//! # Term representation (contract with mana-codegen)
//!
//! Terms are 64-bit words. The low 3 bits are the primary tag:
//!
//! | tag   | meaning                                                        |
//! |-------|----------------------------------------------------------------|
//! | 0b000 | boxed pointer (8-aligned). First word is a header (see below)  |
//! | 0b001 | small integer, value = word >> 3 (arithmetic)                  |
//! | 0b010 | atom: pointer to `{ len: u64, bytes: [u8; len] }` (static)     |
//! | 0b011 | nil `[]` (the whole word is 3)                                 |
//! | 0b100 | cons cell: pointer to `[head, tail]`                           |
//!
//! Boxed header word: low 8 bits = kind (0 = tuple, 1 = float),
//! remaining bits = arity / payload size in words.
//!
//! Atom identity is per-compilation-unit (pointer equality). A global atom
//! table replaces this in the multi-module milestone.
//!
//! TODO(gc): replace malloc with per-process heaps + Cheney copying collector.
//! TODO(bignum): small-int arithmetic currently wraps into the tag space.

use std::io::Write;

pub const TAG_MASK: u64 = 0b111;
pub const TAG_BOXED: u64 = 0b000;
pub const TAG_SMALL: u64 = 0b001;
pub const TAG_ATOM: u64 = 0b010;
pub const NIL: u64 = 0b011;
pub const TAG_CONS: u64 = 0b100;

pub const KIND_TUPLE: u64 = 0;
pub const KIND_FLOAT: u64 = 1;

/// Bump allocation straight from malloc; leaks by design until the GC lands.
#[no_mangle]
pub extern "C" fn mana_rt_alloc(words: u64) -> *mut u64 {
    let layout =
        std::alloc::Layout::from_size_align(words as usize * 8, 8).expect("bad alloc size");
    unsafe {
        let p = std::alloc::alloc(layout) as *mut u64;
        if p.is_null() {
            eprintln!("mana: out of memory");
            std::process::exit(70);
        }
        p
    }
}

/// `erlang:display/1` — print a term followed by newline.
#[no_mangle]
pub extern "C" fn mana_rt_display(term: u64) {
    let mut out = String::new();
    write_term(term, &mut out);
    out.push('\n');
    let _ = std::io::stdout().write_all(out.as_bytes());
}

/// A pattern match failed and no clause handled it. Exceptions proper are a
/// later milestone; for now this terminates the program.
#[no_mangle]
pub extern "C" fn mana_rt_match_fail(reason: u64) -> ! {
    let mut out = String::new();
    write_term(reason, &mut out);
    eprintln!("mana: no matching clause / exception: {}", out);
    std::process::exit(1);
}

fn write_term(t: u64, out: &mut String) {
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
        TAG_CONS => {
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
            let kind = header & 0xff;
            let arity = (header >> 8) as usize;
            match kind {
                KIND_TUPLE => {
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
                _ => out.push_str("#<unknown-boxed>"),
            }
        },
        _ => out.push_str("#<unknown>"),
    }
}
