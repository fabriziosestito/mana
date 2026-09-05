//! The mana runtime. It is an SMP scheduler with one nursery per scheduler
//! and one shared old generation.
//!
//! # Term representation (contract with mana-codegen)
//!
//! A term is one 64-bit word. The low 3 bits are the primary tag:
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
//! The boxed header word holds the kind in its low 8 bits (0 tuple, 1 float,
//! 2 fun). A tuple keeps its arity in bits 8 and up. A fun keeps its arity
//! in bits 8-15 and its capture count in bits 16 and up. The fun payload is
//! the code pointer, then the captures. `term.rs` defines the full list of
//! kinds and their layouts.
//!
//! # Process context (ABI contract with mana-codegen)
//!
//! Each scheduler thread owns one ProcCtx. Compiled code reads and writes
//! these fixed word offsets:
//!
//! | word | field        | meaning                                                  |
//! |------|--------------|----------------------------------------------------------|
//! | 0    | `heap_top`   | nursery bump pointer (inline allocation fast path)       |
//! | 1    | `heap_end`   | nursery end                                              |
//! | 2    | `roots_head` | root frame chain `[prev, len, slots...]`, zero = empty slot |
//! | 3    | `exc_class`  | class of the pending exception                           |
//! | 4    | `exc_reason` | reason of the pending exception                          |
//! | 5    | `reductions` | reduction counter                                        |
//! | 6    | `argv_spill` | argument spill for calls of arity > 6, valid across one call edge only |
//!
//! # Heap organization (SMP)
//!
//! Each scheduler owns a private nursery. The old generation is shared and
//! chunked. It does not move between major collections. These invariants
//! make this work with no write barriers and no locks on the hot path:
//!
//! * Terms are immutable and reference only older terms. There are no
//!   old-to-young pointers. As a result, **a minor collection is local to
//!   one scheduler**.
//! * The sender **promotes every term that crosses processes to the shared
//!   old space at send time**. This covers message payloads and spawn
//!   closures. The runtime copies the young parts once. A long-lived payload
//!   becomes old at the next minor collection of the sender. After that, it
//!   transfers by pointer forever. Old parts always pass by pointer. As a
//!   result, no scheduler holds a reference into the nursery of another
//!   scheduler.
//! * A major collection (old space over its limit) stops the world. The
//!   schedulers park at safepoints (the scheduler loop, the allocation slow
//!   path). The requester evacuates all nurseries, then compacts the old
//!   space.
//!
//! A process is a corosensei coroutine **pinned to its home scheduler**.
//! Only the home thread touches the coroutine, the cursor, and the saved
//! state of a process. Only mailbox pushes, state flips, and condvar wakes
//! cross threads.
//!
//! # Modules
//!
//! * `term.rs` holds tags, kinds, atoms, allocation primitives, and error
//!   helpers.
//! * `sched.rs` holds `ProcCtx`, processes, and schedulers. `gc.rs` holds
//!   minor and major collection, and promotion.
//! * `signals.rs` holds links, monitors, and exit signals. `proc.rs` holds
//!   the spawn, send, and receive primops, the process dictionary, and the
//!   name registry.
//! * `arith.rs` holds numbers, and `bigint.rs` holds the limb math.
//!   `compare.rs` holds term order, equality, and the list and tuple BIFs.
//!   `maps.rs`, `binary.rs`, `convert.rs`, `io.rs`, `etf.rs`, `re.rs`, and
//!   `codec.rs` (crypto, zlib) hold the other data BIFs.
//! * `reactor.rs` holds the mio thread. `tcp.rs`, `file.rs`, and
//!   `decode_packet.rs` hold sockets, files, and packet decoding.
//! * `system.rs` holds time, timers, and system info. `ets.rs` holds ets,
//!   persistent_term, and the application env. `apply.rs` holds the export
//!   table, apply, and the code BIFs. `native.rs` holds the ABI for
//!   `Mana.Native` packages.
//!
//! TODO(stacks): process stacks are fixed (root 32MB, spawned 1MB).

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
