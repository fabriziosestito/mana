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

fn payload_words(header: u64) -> usize {
    match header & 0xff {
        KIND_TUPLE => (header >> 8) as usize,
        KIND_FLOAT => 1,
        KIND_FUN => 1 + (header >> 16) as usize,
        KIND_CONS => 2,
        _ => 0,
    }
}

fn object_words(header: u64) -> usize {
    1 + payload_words(header)
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
        _from: ObjectReference,
        _semantics: CopySemantics,
        _copy_context: &mut GCWorkerCopyContext<Mana>,
    ) -> ObjectReference {
        todo!("copying plans — after NoGC milestone")
    }

    fn copy_to(_from: ObjectReference, _to: ObjectReference, _region: Address) -> Address {
        todo!("copying plans — after NoGC milestone")
    }

    fn get_reference_when_copied_to(_from: ObjectReference, _to: Address) -> ObjectReference {
        todo!("copying plans — after NoGC milestone")
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
        _factory: impl RootsWorkFactory<mmtk::vm::slot::SimpleSlot>,
    ) {
        todo!("walk ProcCtx frame chain")
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
    fn stop_all_mutators<F>(_tls: VMWorkerThread, _mutator_visitor: F)
    where
        F: FnMut(&'static mut Mutator<Mana>),
    {
        todo!("single-mutator stop-the-world")
    }

    fn resume_mutators(_tls: VMWorkerThread) {
        todo!("single-mutator stop-the-world")
    }

    fn block_for_gc(_tls: VMMutatorThread) {
        todo!("single-mutator stop-the-world")
    }

    fn spawn_gc_thread(_tls: VMThread, ctx: GCThreadContext<Mana>) {
        std::thread::spawn(move || match ctx {
            GCThreadContext::Worker(w) => {
                mmtk::memory_manager::start_worker(mmtk_instance(), VMWorkerThread(VMThread::UNINITIALIZED), w)
            }
        });
    }
}

pub struct ManaActivePlan;

impl ActivePlan<Mana> for ManaActivePlan {
    fn number_of_mutators() -> usize {
        1
    }

    fn is_mutator(_tls: VMThread) -> bool {
        true
    }

    fn mutator(_tls: VMMutatorThread) -> &'static mut Mutator<Mana> {
        unsafe { &mut *MUTATOR.with(|m| *m.borrow()) }
    }

    fn mutators<'a>() -> Box<dyn Iterator<Item = &'a mut Mutator<Mana>> + 'a> {
        Box::new(std::iter::once(unsafe {
            &mut *MUTATOR.with(|m| *m.borrow())
        }))
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

// ---- runtime surface (same extern C API as mana-rt) ----

static MMTK_SINGLETON: OnceLock<MMTK<Mana>> = OnceLock::new();

thread_local! {
    static MUTATOR: std::cell::RefCell<*mut Mutator<Mana>> =
        const { std::cell::RefCell::new(std::ptr::null_mut()) };
}

fn mmtk_instance() -> &'static MMTK<Mana> {
    MMTK_SINGLETON.get().expect("mmtk not initialized")
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
    let builder = MMTKBuilder::new();
    let mmtk = MMTK_SINGLETON.get_or_init(|| builder.build());
    let tls = VMMutatorThread(VMThread::UNINITIALIZED);
    let mutator = mmtk::memory_manager::bind_mutator(mmtk, tls);
    let mutator = Box::into_raw(mutator);
    MUTATOR.with(|m| *m.borrow_mut() = mutator);
    Box::into_raw(Box::new(ProcCtx {
        heap_top: 8, // top > end: force slow path
        heap_end: 0,
        roots_head: 0,
        mutator,
    }))
}

#[no_mangle]
pub extern "C" fn mana_rt_alloc_slow(ctx: *mut ProcCtx, words: u64) -> *mut u64 {
    let ctx = unsafe { &mut *ctx };
    let mutator = unsafe { &mut *ctx.mutator };
    let addr = mmtk::memory_manager::alloc(
        mutator,
        words as usize * 8,
        8,
        0,
        AllocationSemantics::Default,
    );
    addr.to_mut_ptr()
}

// TODO(spike): display/match_fail/badfun duplicated from mana-rt for now —
// factor a shared mana-term crate when the spike graduates.
#[no_mangle]
pub extern "C" fn mana_rt_display(_term: u64) {
    unimplemented!("spike: link mana-rt's display or factor mana-term");
}

#[no_mangle]
pub extern "C" fn mana_rt_match_fail(_reason: u64) -> ! {
    std::process::exit(1)
}

#[no_mangle]
pub extern "C" fn mana_rt_badfun(_term: u64) -> ! {
    std::process::exit(1)
}
