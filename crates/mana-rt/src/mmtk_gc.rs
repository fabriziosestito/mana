//! MMTk-backed collection mode (`MANA_GC=mmtk`) — the SMP re-trial.
//!
//! One shared MMTk heap for all schedulers: no send-time promotion (all
//! cross-process references are trivially safe), but every collection —
//! including nursery GCs under generational plans — stops the world, versus
//! the native mode's scheduler-local minors. That trade is what the trial
//! benchmarks referee.
//!
//! Binding shape:
//! * one MMTk mutator per scheduler thread; the Default allocator's bump
//!   cursor/limit are synced through ctx words 0/1 so compiled code's
//!   inline fast path works unchanged;
//! * roots via `scan_vm_specific_roots`: every scheduler's live frame
//!   chain + exception slots, every *suspended* process's saved state
//!   (running processes' saved fields are stale — same rule as the native
//!   major), mailboxes (drained to private during STW), eternal objects;
//! * stop-the-world reuses the native park machinery: `stop_all_mutators`
//!   raises the STW flag and waits for every scheduler to park
//!   (`park_if_stw` at safepoints, `block_for_gc` on the triggering
//!   thread).
//!
//! Slots hold tagged terms; only non-zero tag-000 words are reported to
//! MMTk (immediates/atoms/pids are not heap references).

use std::sync::atomic::Ordering;
use std::sync::OnceLock;

use mmtk::util::copy::{CopySemantics, GCWorkerCopyContext};
use mmtk::util::opaque_pointer::*;
use mmtk::util::{Address, ObjectReference};
use mmtk::vm::slot::SimpleSlot;
use mmtk::vm::*;
use mmtk::{AllocationSemantics, MMTKBuilder, Mutator, MMTK};

use crate::{
    drain_ingress, payload_words, proc_mut, walk_proc_roots, Global, ProcCtx, KIND_CONS,
    KIND_FUN, KIND_TUPLE, TAG_MASK,
};

pub const MUTATOR_TLS_BASE: usize = 0x1000;

#[derive(Default)]
pub struct Mana;

impl VMBinding for Mana {
    type VMObjectModel = ManaObjectModel;
    type VMScanning = ManaScanning;
    type VMCollection = ManaCollection;
    type VMActivePlan = ManaActivePlan;
    type VMReferenceGlue = ManaReferenceGlue;
    type VMSlot = SimpleSlot;
    type VMMemorySlice = mmtk::vm::slot::UnimplementedMemorySlice;

    const MIN_ALIGNMENT: usize = 8;
    const MAX_ALIGNMENT: usize = 8;
}

static MMTK_SINGLETON: OnceLock<MMTK<Mana>> = OnceLock::new();
static GLOBAL_PTR: OnceLock<usize> = OnceLock::new();
/// mutator pointers indexed by scheduler id
static MUTATORS: OnceLock<Vec<std::sync::atomic::AtomicUsize>> = OnceLock::new();

fn global() -> &'static Global {
    unsafe { &*(*GLOBAL_PTR.get().unwrap() as *const Global) }
}

fn mmtk_instance() -> &'static MMTK<Mana> {
    MMTK_SINGLETON.get().expect("mmtk not initialized")
}

fn mutator_of(sched: usize) -> &'static mut Mutator<Mana> {
    let p = MUTATORS.get().unwrap()[sched].load(Ordering::Acquire) as *mut Mutator<Mana>;
    assert!(!p.is_null());
    unsafe { &mut *p }
}

fn sched_of_tls(tls: VMMutatorThread) -> usize {
    (tls.0).0.to_address().as_usize() - MUTATOR_TLS_BASE
}

fn mutator_tls(sched: usize) -> VMMutatorThread {
    VMMutatorThread(VMThread(OpaquePointer::from_address(unsafe {
        Address::from_usize(MUTATOR_TLS_BASE + sched)
    })))
}

/// Initialize MMTk (once) and bind this scheduler's mutator.
pub fn init_scheduler(g: &Global, sched_id: usize, n_scheds: usize) {
    let _ = GLOBAL_PTR.set(g as *const Global as usize);
    let mmtk = MMTK_SINGLETON.get_or_init(|| {
        let mut builder = MMTKBuilder::new();
        let plan = std::env::var("MANA_MMTK_PLAN").unwrap_or_else(|_| "GenImmix".into());
        builder
            .options
            .plan
            .set(plan.parse().unwrap_or(mmtk::util::options::PlanSelector::GenImmix));
        let heap_mb: usize = std::env::var("MANA_MMTK_HEAP_MB")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(256);
        builder.options.gc_trigger.set(
            mmtk::util::options::GCTriggerSelector::FixedHeapSize(heap_mb << 20),
        );
        let _ = builder.options.threads.set(2);
        builder.build()
    });
    MUTATORS.get_or_init(|| {
        (0..n_scheds)
            .map(|_| std::sync::atomic::AtomicUsize::new(0))
            .collect()
    });
    if sched_id == 0 {
        mmtk::memory_manager::initialize_collection(mmtk, VMThread::UNINITIALIZED);
    }
    let mutator = Box::into_raw(mmtk::memory_manager::bind_mutator(mmtk, mutator_tls(sched_id)));
    MUTATORS.get().unwrap()[sched_id].store(mutator as usize, Ordering::Release);
}

/// Bump window (cursor/limit) byte offsets inside the Mutator, if the
/// selected plan bump-allocates Default objects.
fn bump_offsets() -> Option<(usize, usize)> {
    static OFFS: OnceLock<Option<(usize, usize)>> = OnceLock::new();
    *OFFS.get_or_init(|| {
        let selector = mmtk::memory_manager::get_allocator_mapping(
            mmtk_instance(),
            AllocationSemantics::Default,
        );
        match mmtk::util::alloc::AllocatorInfo::new::<Mana>(selector) {
            mmtk::util::alloc::AllocatorInfo::BumpPointer { bump_pointer_offset } => {
                Some((bump_pointer_offset, bump_pointer_offset + 8))
            }
            _ => None,
        }
    })
}

/// Allocation slow path in MMTk mode: flush the inline cursor, allocate
/// (may trigger a collection), resync the window.
pub fn alloc_slow(ctx: &mut ProcCtx, words: usize) -> *mut u64 {
    let mutator = mutator_of(ctx.sched_id);
    let bytes = words * 8;
    unsafe {
        if let Some((c, _)) = bump_offsets() {
            let cursor = (mutator as *mut Mutator<Mana> as *mut u8).add(c) as *mut usize;
            let top = ctx.heap_top as usize;
            if top > 8 {
                *cursor = top;
            }
        }
    }
    let addr = mmtk::memory_manager::alloc(mutator, bytes, 8, 0, AllocationSemantics::Default);
    let obj = unsafe { ObjectReference::from_raw_address_unchecked(addr) };
    mmtk::memory_manager::post_alloc(mutator, obj, bytes, AllocationSemantics::Default);
    unsafe {
        if let Some((c, l)) = bump_offsets() {
            let base = mutator as *mut Mutator<Mana> as *mut u8;
            ctx.heap_top = *(base.add(c) as *const usize) as *mut u64;
            ctx.heap_end = *(base.add(l) as *const usize) as *mut u64;
        }
    }
    addr.to_mut_ptr()
}

// ---------------------------------------------------------------------------

pub struct ManaObjectModel;

impl ObjectModel<Mana> for ManaObjectModel {
    const GLOBAL_LOG_BIT_SPEC: VMGlobalLogBitSpec = VMGlobalLogBitSpec::side_first();
    const LOCAL_FORWARDING_POINTER_SPEC: VMLocalForwardingPointerSpec =
        VMLocalForwardingPointerSpec::in_header(0);
    const LOCAL_FORWARDING_BITS_SPEC: VMLocalForwardingBitsSpec =
        VMLocalForwardingBitsSpec::side_first();
    const LOCAL_MARK_BIT_SPEC: VMLocalMarkBitSpec =
        VMLocalMarkBitSpec::side_after(Self::LOCAL_FORWARDING_BITS_SPEC.as_spec());
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
        (1 + payload_words(header)) * 8
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

fn visit_term_slot<SV: SlotVisitor<SimpleSlot>>(addr: Address, sv: &mut SV) {
    let t = unsafe { addr.load::<u64>() };
    if t != 0 && t & TAG_MASK == 0 {
        sv.visit_slot(SimpleSlot::from_address(addr));
    }
}

impl Scanning<Mana> for ManaScanning {
    fn scan_object<SV: SlotVisitor<SimpleSlot>>(
        _tls: VMWorkerThread,
        object: ObjectReference,
        slot_visitor: &mut SV,
    ) {
        let base = object.to_raw_address();
        let header = unsafe { base.load::<u64>() };
        let (start, n) = match header & 0xff {
            KIND_TUPLE => (1usize, (header >> 8) as usize),
            KIND_CONS => (1, 2),
            KIND_FUN => (2, (header >> 16) as usize),
            _ => (0, 0),
        };
        for i in 0..n {
            visit_term_slot(base + (start + i) * 8, slot_visitor);
        }
    }

    fn notify_initial_thread_scan_complete(_partial_scan: bool, _tls: VMWorkerThread) {}

    fn scan_roots_in_mutator_thread(
        _tls: VMWorkerThread,
        _mutator: &'static mut Mutator<Mana>,
        _factory: impl RootsWorkFactory<SimpleSlot>,
    ) {
        // all roots are reported via scan_vm_specific_roots
    }

    fn scan_vm_specific_roots(_tls: VMWorkerThread, mut factory: impl RootsWorkFactory<SimpleSlot>) {
        let g = global();
        let mut slots: Vec<SimpleSlot> = Vec::new();
        let mut push = |p: *mut u64| {
            let t = unsafe { *p };
            if t != 0 && t & TAG_MASK == 0 {
                slots.push(SimpleSlot::from_address(Address::from_mut_ptr(p)));
            }
        };
        unsafe {
            // live scheduler contexts (+ collect running pids: their saved
            // process state is stale and must not be scanned)
            let mut running: Vec<usize> = Vec::new();
            for s in g.scheds.iter() {
                let ctxp = s.ctx_addr.load(Ordering::Acquire) as *mut ProcCtx;
                if ctxp.is_null() {
                    continue;
                }
                let ctx = &mut *ctxp;
                if ctx.current != usize::MAX {
                    running.push(ctx.current);
                }
                let mut frame = ctx.roots_head as *mut u64;
                while !frame.is_null() {
                    let len = *frame.add(1) as usize;
                    for i in 0..len {
                        push(frame.add(2 + i));
                    }
                    frame = *frame as *mut u64;
                }
                push(&mut ctx.exc_class as *mut u64);
                push(&mut ctx.exc_reason as *mut u64);
            }
            // processes (suspended ones' saved state; everyone's mailbox)
            let tab = g.procs.read();
            for (id, slot) in tab.iter().enumerate() {
                let Some(cell) = slot else { continue };
                let p = proc_mut(cell);
                if !running.contains(&id) {
                    walk_proc_roots(p, |s| push(s));
                }
                drain_ingress(p); // everyone is parked
                for m in p.private.iter_mut() {
                    push(m as *mut u64);
                }
            }
            // eternal objects' fields
            for (pa, _) in g.eternal.lock().iter() {
                let p = *pa as *mut u64;
                let header = *p;
                let (start, n) = match header & 0xff {
                    KIND_TUPLE => (1usize, (header >> 8) as usize),
                    KIND_CONS => (1, 2),
                    KIND_FUN => (2, (header >> 16) as usize),
                    _ => (0, 0),
                };
                for i in 0..n {
                    push(p.add(start + i));
                }
            }
        }
        if !slots.is_empty() {
            factory.create_process_roots_work(slots);
        }
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
        let g = global();
        crate::stw_begin_for_mmtk(g);
        for i in 0..g.n_scheds {
            mutator_visitor(mutator_of(i));
        }
    }

    fn resume_mutators(_tls: VMWorkerThread) {
        crate::stw_end_for_mmtk(global());
    }

    fn block_for_gc(tls: VMMutatorThread) {
        let _ = sched_of_tls(tls);
        crate::block_current_for_mmtk(global());
    }

    fn spawn_gc_thread(_tls: VMThread, ctx: GCThreadContext<Mana>) {
        static WORKER_ID: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(1);
        let id = WORKER_ID.fetch_add(1, Ordering::Relaxed);
        std::thread::spawn(move || match ctx {
            GCThreadContext::Worker(w) => {
                let tls = VMWorkerThread(VMThread(OpaquePointer::from_address(unsafe {
                    Address::from_usize(0x8000_0000 + (id << 4))
                })));
                mmtk::memory_manager::start_worker(mmtk_instance(), tls, w)
            }
        });
    }
}

pub struct ManaActivePlan;

impl ActivePlan<Mana> for ManaActivePlan {
    fn number_of_mutators() -> usize {
        global().n_scheds
    }

    fn is_mutator(tls: VMThread) -> bool {
        let a = tls.0.to_address().as_usize();
        (MUTATOR_TLS_BASE..MUTATOR_TLS_BASE + global().n_scheds).contains(&a)
    }

    fn mutator(tls: VMMutatorThread) -> &'static mut Mutator<Mana> {
        mutator_of(sched_of_tls(tls))
    }

    fn mutators<'a>() -> Box<dyn Iterator<Item = &'a mut Mutator<Mana>> + 'a> {
        Box::new((0..global().n_scheds).map(|i| {
            let p = MUTATORS.get().unwrap()[i].load(Ordering::Acquire) as *mut Mutator<Mana>;
            unsafe { &mut *p }
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
