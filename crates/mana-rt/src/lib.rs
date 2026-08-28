//! mana runtime — per-process heap with a Cheney copying collector.
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
//! | 0b111 | GC forwarding marker (never visible to compiled code)          |
//!
//! Boxed header word: low 8 bits = kind (0 tuple, 1 float, 2 fun); tuples
//! keep arity in bits 8+, funs keep arity in bits 8-15 and capture count in
//! bits 16+ (payload: code pointer, then captures).
//!
//! Atoms are `linkonce_odr` statics deduplicated by the linker — never heap
//! allocated, never collected.
//!
//! # Process context (ABI contract with mana-codegen)
//!
//! Every compiled function takes `ctx: *mut ProcCtx` as its first argument.
//! Codegen reads/writes these fields by fixed word offset:
//!
//! * word 0: `heap_top`
//! * word 1: `heap_end`
//! * word 2: `roots_head` — a chain of GC root frames on the native stack,
//!   each laid out `[prev_frame, len, slot0, ..., slot(len-1)]`. Every slot
//!   always holds a valid term (frames are NIL-initialized).
//!
//! Collection may move every heap object; compiled code must not hold heap
//! terms in registers across a potential GC point unless rooted in a frame
//! slot (mana-codegen's spill discipline enforces this).
//!
//! TODO(bignum): small-int arithmetic currently wraps into the tag space.

use std::io::Write;

pub const TAG_MASK: u64 = 0b111;
pub const TAG_BOXED: u64 = 0b000;
pub const TAG_SMALL: u64 = 0b001;
pub const TAG_ATOM: u64 = 0b010;
pub const NIL: u64 = 0b011;
pub const TAG_CONS: u64 = 0b100;
pub const TAG_FORWARD: u64 = 0b111;

pub const KIND_TUPLE: u64 = 0;
pub const KIND_FLOAT: u64 = 1;
/// Fun object: `[header | code_ptr | captured terms...]`.
/// Header: bits 0-7 kind, bits 8-15 arity, bits 16+ number of captures.
pub const KIND_FUN: u64 = 2;

const INITIAL_HEAP_WORDS: usize = 1024;

#[repr(C)]
pub struct ProcCtx {
    pub heap_top: *mut u64,  // word offset 0 — codegen contract
    pub heap_end: *mut u64,  // word offset 1 — codegen contract
    pub roots_head: u64,     // word offset 2 — codegen contract
    heap_start: *mut u64,
    heap_words: usize,
}

fn alloc_space(words: usize) -> *mut u64 {
    let layout = std::alloc::Layout::from_size_align(words * 8, 8).expect("bad heap size");
    let p = unsafe { std::alloc::alloc(layout) } as *mut u64;
    if p.is_null() {
        eprintln!("mana: out of memory");
        std::process::exit(70);
    }
    p
}

unsafe fn free_space(p: *mut u64, words: usize) {
    let layout = std::alloc::Layout::from_size_align(words * 8, 8).unwrap();
    unsafe { std::alloc::dealloc(p as *mut u8, layout) };
}

/// Create the root process context. Leaked: lives for the program.
#[no_mangle]
pub extern "C" fn mana_rt_init() -> *mut ProcCtx {
    let heap = alloc_space(INITIAL_HEAP_WORDS);
    Box::into_raw(Box::new(ProcCtx {
        heap_top: heap,
        heap_end: unsafe { heap.add(INITIAL_HEAP_WORDS) },
        roots_head: 0,
        heap_start: heap,
        heap_words: INITIAL_HEAP_WORDS,
    }))
}

/// Bump-allocate `words` from the process heap, collecting when full.
#[no_mangle]
pub extern "C" fn mana_rt_alloc(ctx: *mut ProcCtx, words: u64) -> *mut u64 {
    let ctx = unsafe { &mut *ctx };
    let words = words as usize;
    unsafe {
        if ctx.heap_top.add(words) > ctx.heap_end {
            collect(ctx, words);
        }
        let p = ctx.heap_top;
        ctx.heap_top = ctx.heap_top.add(words);
        p
    }
}

/// Cheney copying collection into a fresh space sized for `need` more words.
fn collect(ctx: &mut ProcCtx, need: usize) {
    let to_words = usize::max(ctx.heap_words * 2, ctx.heap_words + need);
    let to_space = alloc_space(to_words);
    let mut top = to_space;
    let mut worklist: Vec<u64> = Vec::new();

    unsafe {
        // roots: every slot of every frame in the chain
        let mut frame = ctx.roots_head as *mut u64;
        while !frame.is_null() {
            let len = *frame.add(1) as usize;
            for i in 0..len {
                let slot = frame.add(2 + i);
                *slot = forward(*slot, &mut top, &mut worklist);
            }
            frame = *frame as *mut u64;
        }

        // transitive closure
        while let Some(t) = worklist.pop() {
            scan(t, &mut top, &mut worklist);
        }

        free_space(ctx.heap_start, ctx.heap_words);
    }

    let live = (top as usize - to_space as usize) / 8;
    if live + need > to_words {
        eprintln!("mana: heap corruption during collection");
        std::process::exit(70);
    }
    if std::env::var_os("MANA_GC_LOG").is_some() {
        eprintln!(
            "mana: gc {} -> {} words, {} live",
            ctx.heap_words, to_words, live
        );
    }
    ctx.heap_start = to_space;
    ctx.heap_top = top;
    ctx.heap_end = unsafe { to_space.add(to_words) };
    ctx.heap_words = to_words;
}

/// Copy the object behind `t` to to-space (if heap-allocated and not yet
/// moved) and return the updated term.
unsafe fn forward(t: u64, top: &mut *mut u64, worklist: &mut Vec<u64>) -> u64 {
    match t & TAG_MASK {
        TAG_SMALL | TAG_ATOM => t,
        _ if t == NIL => t,
        TAG_CONS => unsafe {
            let p = (t & !TAG_MASK) as *mut u64;
            if *p & TAG_MASK == TAG_FORWARD {
                return (*p & !TAG_MASK) | TAG_CONS;
            }
            let new = *top;
            *new = *p;
            *new.add(1) = *p.add(1);
            *top = top.add(2);
            *p = new as u64 | TAG_FORWARD;
            let nt = new as u64 | TAG_CONS;
            worklist.push(nt);
            nt
        },
        TAG_BOXED => unsafe {
            let p = t as *mut u64;
            if *p & TAG_MASK == TAG_FORWARD {
                return *p & !TAG_MASK; // boxed tag is 0
            }
            let header = *p;
            let words = 1 + payload_words(header);
            let new = *top;
            std::ptr::copy_nonoverlapping(p, new, words);
            *top = top.add(words);
            *p = new as u64 | TAG_FORWARD;
            let nt = new as u64;
            worklist.push(nt);
            nt
        },
        _ => {
            eprintln!("mana: invalid term {:#x} during collection", t);
            std::process::exit(70);
        }
    }
}

/// Forward the fields of an already-copied object.
unsafe fn scan(t: u64, top: &mut *mut u64, worklist: &mut Vec<u64>) {
    unsafe {
        match t & TAG_MASK {
            TAG_CONS => {
                let p = (t & !TAG_MASK) as *mut u64;
                *p = forward(*p, top, worklist);
                *p.add(1) = forward(*p.add(1), top, worklist);
            }
            TAG_BOXED => {
                let p = t as *mut u64;
                let header = *p;
                match header & 0xff {
                    KIND_TUPLE => {
                        let arity = (header >> 8) as usize;
                        for i in 0..arity {
                            let f = p.add(1 + i);
                            *f = forward(*f, top, worklist);
                        }
                    }
                    KIND_FUN => {
                        // word 1 is the code pointer — not a term
                        let ncaps = (header >> 16) as usize;
                        for i in 0..ncaps {
                            let f = p.add(2 + i);
                            *f = forward(*f, top, worklist);
                        }
                    }
                    _ => {} // float: no term fields
                }
            }
            _ => {}
        }
    }
}

fn payload_words(header: u64) -> usize {
    match header & 0xff {
        KIND_TUPLE => (header >> 8) as usize,
        KIND_FLOAT => 1,
        KIND_FUN => 1 + (header >> 16) as usize,
        _ => 0,
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

/// A fun was applied to the wrong number of arguments, or a non-fun value
/// was applied.
#[no_mangle]
pub extern "C" fn mana_rt_badfun(term: u64) -> ! {
    let mut out = String::new();
    write_term(term, &mut out);
    eprintln!("mana: bad fun application: {}", out);
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
            match kind {
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
                _ => out.push_str("#<unknown-boxed>"),
            }
        },
        _ => out.push_str("#<unknown>"),
    }
}
