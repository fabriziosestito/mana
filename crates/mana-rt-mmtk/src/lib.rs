//! mana-rt-mmtk — spike: MMTk as the collector behind the same runtime
//! surface as mana-rt (drop-in replacement staticlib, selected at link
//! time).
//!
//! Status: VMBinding skeleton. Goal of the spike phase: NoGC plan
//! allocating end-to-end (conformance suite green with collection
//! effectively disabled), then GenCopy with real collection.
//!
//! Object model: every heap object carries a header (word 0) — kinds:
//! 0 tuple (arity in bits 8+), 1 float, 2 fun (arity bits 8-15, captures
//! bits 16+), 3 cons (payload 2). See mana-rt for the term tags.
//!
//! Root enumeration: walks the ProcCtx roots_head frame chain, same layout
//! as mana-rt (`[prev, len, slots...]`, slot 0 = empty).

use std::sync::OnceLock;

use mmtk::util::copy::{CopySemantics, GCWorkerCopyContext};
use mmtk::util::opaque_pointer::*;
use mmtk::util::{Address, ObjectReference};
use mmtk::vm::*;
use mmtk::{AllocationSemantics, MMTKBuilder, Mutator, MMTK};

pub const KIND_TUPLE: u64 = 0;
pub const KIND_FLOAT: u64 = 1;
pub const KIND_FUN: u64 = 2;
pub const KIND_CONS: u64 = 3;

use mana_term::write_term;

fn object_words(header: u64) -> usize {
    1 + mana_term::payload_words(header)
}

#[derive(Default)]
pub struct Mana;

impl VMBinding for Mana {
    type VMObjectModel = ManaObjectModel;
    type VMScanning = ManaScanning;
    type VMCollection = ManaCollection;
    type VMActivePlan = ManaActivePlan;
    type VMReferenceGlue = ManaReferenceGlue;
    type VMSlot = mmtk::vm::slot::SimpleSlot;
    type VMMemorySlice = mmtk::vm::slot::UnimplementedMemorySlice;

    const MIN_ALIGNMENT: usize = 8;
    const MAX_ALIGNMENT: usize = 8;
}

pub struct ManaObjectModel;

impl ObjectModel<Mana> for ManaObjectModel {
    const GLOBAL_LOG_BIT_SPEC: VMGlobalLogBitSpec = VMGlobalLogBitSpec::side_first();
    const LOCAL_FORWARDING_POINTER_SPEC: VMLocalForwardingPointerSpec =
        VMLocalForwardingPointerSpec::in_header(0);
    const LOCAL_FORWARDING_BITS_SPEC: VMLocalForwardingBitsSpec =
        VMLocalForwardingBitsSpec::side_first();
    const LOCAL_MARK_BIT_SPEC: VMLocalMarkBitSpec = VMLocalMarkBitSpec::side_after(
        Self::LOCAL_FORWARDING_BITS_SPEC.as_spec(),
    );
    const LOCAL_LOS_MARK_NURSERY_SPEC: VMLocalLOSMarkNurserySpec =
        VMLocalLOSMarkNurserySpec::side_after(Self::LOCAL_MARK_BIT_SPEC.as_spec());

    const OBJECT_REF_OFFSET_LOWER_BOUND: isize = 0;

    fn copy(
        from: ObjectReference,
        semantics: CopySemantics,
        copy_context: &mut GCWorkerCopyContext<Mana>,
    ) -> ObjectReference {
        let bytes = Self::get_current_size(from);
        let dst = copy_context.alloc_copy(from, bytes, 8, 0, semantics);
        unsafe {
            std::ptr::copy_nonoverlapping::<u8>(
                from.to_raw_address().to_ptr(),
                dst.to_mut_ptr(),
                bytes,
            );
        }
        let to_obj = unsafe { ObjectReference::from_raw_address_unchecked(dst) };
        copy_context.post_copy(to_obj, bytes, semantics);
        to_obj
    }

    fn copy_to(_from: ObjectReference, _to: ObjectReference, _region: Address) -> Address {
        unimplemented!("compacting plans are not used")
    }

    fn get_reference_when_copied_to(_from: ObjectReference, to: Address) -> ObjectReference {
        unsafe { ObjectReference::from_raw_address_unchecked(to) }
    }

    fn get_current_size(object: ObjectReference) -> usize {
        let header = unsafe { object.to_raw_address().load::<u64>() };
        object_words(header) * 8
    }

    fn get_size_when_copied(object: ObjectReference) -> usize {
        Self::get_current_size(object)
    }

    fn get_align_when_copied(_object: ObjectReference) -> usize {
        8
    }

    fn get_align_offset_when_copied(_object: ObjectReference) -> usize {
        0
    }

    fn get_type_descriptor(_reference: ObjectReference) -> &'static [i8] {
        &[]
    }

    fn ref_to_object_start(object: ObjectReference) -> Address {
        object.to_raw_address()
    }

    fn ref_to_header(object: ObjectReference) -> Address {
        object.to_raw_address()
    }

    fn dump_object(object: ObjectReference) {
        let header = unsafe { object.to_raw_address().load::<u64>() };
        eprintln!("mana object at {} header {:#x}", object, header);
    }
}

pub struct ManaScanning;

impl Scanning<Mana> for ManaScanning {
    fn scan_object<SV: SlotVisitor<mmtk::vm::slot::SimpleSlot>>(
        _tls: VMWorkerThread,
        object: ObjectReference,
        slot_visitor: &mut SV,
    ) {
        let base = object.to_raw_address();
        let header = unsafe { base.load::<u64>() };
        let visit = |word_index: usize, sv: &mut SV| {
            let addr = base + word_index * 8;
            let t = unsafe { addr.load::<u64>() };
            // only boxed (tag 000, non-zero) references are heap slots;
            // immediates/atoms/nil are skipped
            if t != 0 && t & 0b111 == 0 {
                sv.visit_slot(mmtk::vm::slot::SimpleSlot::from_address(addr));
            }
        };
        match header & 0xff {
            KIND_TUPLE => (1..=(header >> 8) as usize).for_each(|i| visit(i, slot_visitor)),
            KIND_CONS => [1usize, 2].iter().for_each(|i| visit(*i, slot_visitor)),
            KIND_FUN => {
                (2..2 + (header >> 16) as usize).for_each(|i| visit(i, slot_visitor))
            }
            _ => {}
        }
    }

    fn notify_initial_thread_scan_complete(_partial_scan: bool, _tls: VMWorkerThread) {}

    fn scan_roots_in_mutator_thread(
        _tls: VMWorkerThread,
        _mutator: &'static mut Mutator<Mana>,
        mut factory: impl RootsWorkFactory<mmtk::vm::slot::SimpleSlot>,
    ) {
        // Walk the ProcCtx frame chain: [prev, len, slots...]. A slot holds
        // a heap reference iff non-zero with tag 000 (headered cons made
        // every heap ref a plain address).
        let ctx = CTX_PTR.load(std::sync::atomic::Ordering::Acquire);
        assert!(!ctx.is_null(), "ProcCtx not registered");
        let mut slots = Vec::new();
        unsafe {
            let mut frame = (*ctx).roots_head as *mut u64;
            while !frame.is_null() {
                let len = *frame.add(1) as usize;
                for i in 0..len {
                    let slot = frame.add(2 + i);
                    let t = *slot;
                    if t != 0 && t & 0b111 == 0 {
                        slots.push(mmtk::vm::slot::SimpleSlot::from_address(
                            Address::from_mut_ptr(slot),
                        ));
                    }
                }
                frame = *frame as *mut u64;
            }
        }
        factory.create_process_roots_work(slots);
    }

    fn scan_vm_specific_roots(
        _tls: VMWorkerThread,
        _factory: impl RootsWorkFactory<mmtk::vm::slot::SimpleSlot>,
    ) {
    }

    fn supports_return_barrier() -> bool {
        false
    }

    fn prepare_for_roots_re_scanning() {}
}

pub struct ManaCollection;

impl Collection<Mana> for ManaCollection {
    fn stop_all_mutators<F>(_tls: VMWorkerThread, mut mutator_visitor: F)
    where
        F: FnMut(&'static mut Mutator<Mana>),
    {
        let mut s = GC_SYNC.lock().unwrap();
        while !s.parked {
            s = GC_CONDVAR.wait(s).unwrap();
        }
        drop(s);
        mutator_visitor(the_mutator());
    }

    fn resume_mutators(_tls: VMWorkerThread) {
        let mut s = GC_SYNC.lock().unwrap();
        s.epoch += 1;
        GC_CONDVAR.notify_all();
    }

    fn block_for_gc(_tls: VMMutatorThread) {
        let mut s = GC_SYNC.lock().unwrap();
        s.parked = true;
        GC_CONDVAR.notify_all();
        let epoch = s.epoch;
        while s.epoch == epoch {
            s = GC_CONDVAR.wait(s).unwrap();
        }
        s.parked = false;
    }

    fn spawn_gc_thread(_tls: VMThread, ctx: GCThreadContext<Mana>) {
        // Every worker needs a unique, non-null TLS opaque pointer.
        static WORKER_ID: std::sync::atomic::AtomicUsize =
            std::sync::atomic::AtomicUsize::new(1);
        let id = WORKER_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        std::thread::spawn(move || match ctx {
            GCThreadContext::Worker(w) => {
                let tls = VMWorkerThread(VMThread(OpaquePointer::from_address(unsafe {
                    Address::from_usize(id << 4)
                })));
                mmtk::memory_manager::start_worker(mmtk_instance(), tls, w)
            }
        });
    }
}

pub struct ManaActivePlan;

impl ActivePlan<Mana> for ManaActivePlan {
    fn number_of_mutators() -> usize {
        1
    }

    fn is_mutator(tls: VMThread) -> bool {
        // only the single mutator thread (TLS 0x8) — GC workers must not be
        // mistaken for mutators or MMTk's pause protocol breaks
        tls.0.to_address().as_usize() == 0x8
    }

    fn mutator(_tls: VMMutatorThread) -> &'static mut Mutator<Mana> {
        the_mutator()
    }

    fn mutators<'a>() -> Box<dyn Iterator<Item = &'a mut Mutator<Mana>> + 'a> {
        Box::new(std::iter::once(the_mutator()))
    }
}

pub struct ManaReferenceGlue;

impl ReferenceGlue<Mana> for ManaReferenceGlue {
    type FinalizableType = ObjectReference;

    fn set_referent(_reference: ObjectReference, _referent: ObjectReference) {
        unimplemented!("weak references are not supported")
    }

    fn get_referent(_object: ObjectReference) -> Option<ObjectReference> {
        unimplemented!("weak references are not supported")
    }

    fn clear_referent(_object: ObjectReference) {
        unimplemented!("weak references are not supported")
    }

    fn enqueue_references(_references: &[ObjectReference], _tls: VMWorkerThread) {}
}

// ---- global single-mutator state (GC workers access from other threads) ----

static MMTK_SINGLETON: OnceLock<MMTK<Mana>> = OnceLock::new();
static MUTATOR_PTR: std::sync::atomic::AtomicPtr<Mutator<Mana>> =
    std::sync::atomic::AtomicPtr::new(std::ptr::null_mut());
static CTX_PTR: std::sync::atomic::AtomicPtr<ProcCtx> =
    std::sync::atomic::AtomicPtr::new(std::ptr::null_mut());

/// Single-mutator stop-the-world with a proper handshake: the mutator
/// parks in `block_for_gc` and workers wait for it in `stop_all_mutators`
/// (otherwise a fast GC could resume before the mutator ever parked and
/// the wakeup would be lost). `epoch` guards against spurious wakeups.
struct GcSync {
    parked: bool,
    epoch: u64,
}
static GC_SYNC: std::sync::Mutex<GcSync> = std::sync::Mutex::new(GcSync {
    parked: false,
    epoch: 0,
});
static GC_CONDVAR: std::sync::Condvar = std::sync::Condvar::new();

/// Byte offsets of the Default-semantics bump allocator's cursor/limit
/// inside the Mutator, if the selected plan uses bump allocation. Compiled
/// code bumps ctx words 0/1 inline; the slow path flushes/re-syncs.
static BUMP_OFFSETS: OnceLock<Option<(usize, usize)>> = OnceLock::new();

unsafe fn bump_ptrs(mutator: *mut Mutator<Mana>) -> Option<(*mut usize, *mut usize)> {
    BUMP_OFFSETS.get().copied().flatten().map(|(c, l)| unsafe {
        (
            (mutator as *mut u8).add(c) as *mut usize,
            (mutator as *mut u8).add(l) as *mut usize,
        )
    })
}

fn mmtk_instance() -> &'static MMTK<Mana> {
    MMTK_SINGLETON.get().expect("mmtk not initialized")
}

fn the_mutator() -> &'static mut Mutator<Mana> {
    let p = MUTATOR_PTR.load(std::sync::atomic::Ordering::Acquire);
    assert!(!p.is_null(), "mutator not bound");
    unsafe { &mut *p }
}

/// ProcCtx mirror of mana-rt's contract: words 0/1 are made permanently
/// "full" so compiled code always takes the slow path into MMTk (spike:
/// correctness first; MMTk's bump cursor gets wired into words 0/1 later).
#[repr(C)]
pub struct ProcCtx {
    pub heap_top: u64,
    pub heap_end: u64,
    pub roots_head: u64,
    mutator: *mut Mutator<Mana>,
}

#[no_mangle]
pub extern "C" fn mana_rt_init() -> *mut ProcCtx {
    let mut builder = MMTKBuilder::new();
    // SemiSpace: real moving collection through MMTk. Plan/heap tunable via
    // env for the spike: MANA_MMTK_PLAN, MANA_MMTK_HEAP_MB.
    let plan = std::env::var("MANA_MMTK_PLAN").unwrap_or_else(|_| "SemiSpace".into());
    builder
        .options
        .plan
        .set(plan.parse().unwrap_or(mmtk::util::options::PlanSelector::SemiSpace));
    let heap_mb: usize = std::env::var("MANA_MMTK_HEAP_MB")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(64);
    builder.options.gc_trigger.set(
        mmtk::util::options::GCTriggerSelector::FixedHeapSize(heap_mb << 20),
    );
    let mmtk = MMTK_SINGLETON.get_or_init(|| builder.build());
    // the mutator TLS must also be a valid non-null opaque pointer
    let tls = VMMutatorThread(VMThread(OpaquePointer::from_address(unsafe {
        Address::from_usize(0x8)
    })));
    mmtk::memory_manager::initialize_collection(mmtk, VMThread::UNINITIALIZED);
    let mutator = mmtk::memory_manager::bind_mutator(mmtk, tls);
    let mutator = Box::into_raw(mutator);
    MUTATOR_PTR.store(mutator, std::sync::atomic::Ordering::Release);

    // discover the bump-pointer fast path layout for Default allocations
    let offsets = BUMP_OFFSETS.get_or_init(|| {
        let selector =
            mmtk::memory_manager::get_allocator_mapping(mmtk, AllocationSemantics::Default);
        match mmtk::util::alloc::AllocatorInfo::new::<Mana>(selector) {
            mmtk::util::alloc::AllocatorInfo::BumpPointer {
                bump_pointer_offset,
            } => {
                // BumpPointer { cursor: Address, limit: Address }
                Some((bump_pointer_offset, bump_pointer_offset + 8))
            }
            _ => None,
        }
    });
    if std::env::var_os("MANA_GC_LOG").is_some() {
        eprintln!("mana-mmtk: inline fast path: {:?}", offsets);
    }

    let ctx = Box::into_raw(Box::new(ProcCtx {
        heap_top: 8, // top > end: force slow path until first sync
        heap_end: 0,
        roots_head: 0,
        mutator,
    }));
    CTX_PTR.store(ctx, std::sync::atomic::Ordering::Release);
    ctx
}

#[no_mangle]
pub extern "C" fn mana_rt_alloc_slow(ctx: *mut ProcCtx, words: u64) -> *mut u64 {
    let ctx = unsafe { &mut *ctx };
    let mutator = unsafe { &mut *ctx.mutator };
    let bytes = words as usize * 8;
    let bump = unsafe { bump_ptrs(ctx.mutator) };
    // flush: MMTk must see what the inline fast path consumed
    if let Some((cursor, _)) = bump {
        if ctx.heap_top as usize > 8 {
            unsafe { *cursor = ctx.heap_top as usize };
        }
    }
    let addr = mmtk::memory_manager::alloc(mutator, bytes, 8, 0, AllocationSemantics::Default);
    let obj = unsafe { ObjectReference::from_raw_address_unchecked(addr) };
    mmtk::memory_manager::post_alloc(mutator, obj, bytes, AllocationSemantics::Default);
    // re-sync: hand the remaining bump window to the inline fast path
    if let Some((cursor, limit)) = bump {
        unsafe {
            ctx.heap_top = *cursor as u64;
            ctx.heap_end = *limit as u64;
        }
    }
    addr.to_mut_ptr()
}

/// `erlang:display/1` — print a term followed by newline.
#[no_mangle]
pub extern "C" fn mana_rt_display(term: u64) {
    use std::io::Write;
    let mut out = String::new();
    unsafe { write_term(term, &mut out) };
    out.push('\n');
    let _ = std::io::stdout().write_all(out.as_bytes());
}

#[no_mangle]
pub extern "C" fn mana_rt_match_fail(reason: u64) -> ! {
    let mut out = String::new();
    unsafe { write_term(reason, &mut out) };
    eprintln!("mana: no matching clause / exception: {}", out);
    std::process::exit(1);
}

#[no_mangle]
pub extern "C" fn mana_rt_badfun(term: u64) -> ! {
    let mut out = String::new();
    unsafe { write_term(term, &mut out) };
    eprintln!("mana: bad fun application: {}", out);
    std::process::exit(1);
}
