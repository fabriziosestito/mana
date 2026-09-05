//! mana runtime — SMP scheduler with per-scheduler nurseries and a shared
//! old generation.
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
//! | 0b101 | exception sentinel (never a term; see codegen)                 |
//! | 0b110 | pid (process id << 3)                                          |
//! | 0b111 | GC forwarding marker (never visible to compiled code)          |
//!
//! Boxed header word: low 8 bits = kind (0 tuple, 1 float, 2 fun); tuples
//! keep arity in bits 8+, funs keep arity in bits 8-15 and capture count in
//! bits 16+ (payload: code pointer, then captures).
//!
//! # Process context (ABI contract with mana-codegen)
//!
//! One ProcCtx per scheduler thread; compiled code reads/writes fixed word
//! offsets: 0 `heap_top` (nursery bump, inline fast path), 1 `heap_end`,
//! 2 `roots_head` (frame chain `[prev, len, slots...]`, zero = empty slot),
//! 3 `exc_class`, 4 `exc_reason`, 5 `reductions`.
//!
//! # Heap organization (SMP)
//!
//! Each scheduler owns a private nursery; the old generation is shared,
//! chunked, and non-moving between majors. The invariants that make this
//! work without barriers or hot-path locks:
//!
//! * Terms are immutable and only reference older terms — no old→young
//!   pointers, so **minor collections are entirely scheduler-local**.
//! * Anything that crosses processes (message payloads, spawn closures) is
//!   **promoted to the shared old space at send time** (young parts copied
//!   once; a long-lived payload becomes old at the sender's next minor and
//!   then transfers zero-copy forever; old parts always pass by pointer).
//!   Hence no scheduler ever holds references into another's nursery.
//! * Major collections (old space over limit) stop the world: schedulers
//!   park at safepoints (scheduler loop, allocation slow path); the
//!   requester evacuates all nurseries, then compacts the old space.
//!
//! Processes are corosensei coroutines **pinned to their home scheduler**;
//! only the home thread touches a process's coroutine/cursor/saved state.
//! Cross-thread interaction is limited to mailbox pushes, state flips, and
//! condvar wakes.
//!
//! TODO(stacks): process stacks are fixed (root 32MB, spawned 1MB).
//! TODO(split): this file wants to become term.rs / gc.rs / sched.rs.

use std::cell::UnsafeCell;
use std::collections::VecDeque;
use std::io::Write;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use crossbeam_queue::SegQueue;
use parking_lot::{Condvar, Mutex, RwLock};

use corosensei::stack::DefaultStack;
use corosensei::{Coroutine, CoroutineResult, Yielder};

mod bigint;

mod term;
mod sched;
mod gc;
mod signals;
mod proc;
mod etf;
mod codec;
mod system;
mod arith;
mod re;
mod reactor;
mod tcp;
mod file;
mod decode_packet;
mod compare;
mod maps;
mod binary;
mod convert;
mod apply;
mod io;
mod ets;
mod native;

pub(crate) use term::*;
pub(crate) use sched::*;
pub(crate) use gc::*;
pub(crate) use signals::*;
pub(crate) use proc::*;
pub(crate) use system::*;
pub(crate) use arith::*;
pub(crate) use re::*;
pub(crate) use reactor::*;
pub(crate) use tcp::*;
pub(crate) use file::*;
pub(crate) use compare::*;
pub(crate) use maps::*;
pub(crate) use binary::*;
pub(crate) use convert::*;
pub(crate) use apply::*;
pub(crate) use io::*;
pub(crate) use ets::*;
