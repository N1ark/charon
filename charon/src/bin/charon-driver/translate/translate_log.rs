//! Translating items in another order than the sequential worklist's, then renumbering as if we
//! had translated them in that order.
//!
//! Item and file ids are assigned in the order we first encounter items and files, so they depend
//! on the order in which we translate items. To produce the output of the sequential translation
//! from translations done in another order (e.g. in parallel), we record what translating each item
//! did to the state that items share: which items it registered, enqueued and translated right
//! away, which files it used, its effects on method usage, its errors. We then replay the
//! sequential worklist over these logs. This gives the ids the sequential translation assigns, and
//! we renumber everything to these.
use super::translate_cache::MemoKey;
use super::translate_ctx::*;
use crate::hax::BaseState;
use charon_lib::ast::*;
use charon_lib::errors::{DepNode, ErrorRecording, RecordedError};
use charon_lib::ids::IndexVec;
use rustc_const_uneval::{AllocView, ViewLookup};
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use rustc_middle::mir::interpret::AllocId;
use std::collections::VecDeque;
use std::ops::ControlFlow;

/// Something translating an item did that depends on or affects the order of translation.
#[derive(Debug, Clone, Copy)]
enum Event {
    /// Registered this item.
    Reg(ItemId),
    /// Enqueued this item or module.
    Enq(ItemOrModuleId),
    /// Translated this item right away, as it needed its contents.
    Use(ItemId),
    /// Stored the name of this item, as its registration couldn't compute it.
    Named(ItemId),
    /// Did what this memoized computation did.
    Memo(MemoRef),
    /// Used this file.
    File(FileId),
    MarkMethodUsed(TraitDeclId, TraitMethodId),
    MethodImpl(TraitDeclId, TraitMethodId, FunDeclId),
    /// Raised these errors: a range of `TranslationLog::errors`.
    Errors(u32, u32),
    /// Recorded these dependencies: a range of `TranslationLog::dep_edges`.
    DepEdges(u32, u32),
    /// Computed the vtable of this impl: `TranslationLog::vtables[i]`. The impl refers to it if it
    /// is translated already.
    ImplVTable(TraitImplId, u32),
    /// Translated the vtable `TranslationLog::vtables[i]` of this impl, which then refers to it if
    /// it is translated and its vtable wasn't.
    FillLazyVTable(TraitImplId, u32),
    /// Looked up the views of these allocations: a range of `TranslationLog::views`.
    Views(u32, u32),
}

/// A memoized computation: `TranslationLog::memos[index]` of the log of the given worker.
#[derive(Debug, Clone, Copy)]
pub(crate) struct MemoRef {
    worker: u32,
    index: u32,
}

/// What a log is about.
enum LogOwner {
    /// What happens before translating items.
    Start,
    /// The translation of this item or module.
    Item(ItemOrModuleId),
    /// The computation of the name of this item, at its registration.
    Naming(ItemId),
    /// A computation memoized across items.
    Memo,
    /// A computation that another log records.
    Discarded,
}

struct OpenLog {
    owner: LogOwner,
    events: Vec<Event>,
    /// The items, files and dependencies already in `events`: logging them once is enough.
    regs: HashSet<ItemId>,
    enqs: HashSet<ItemOrModuleId>,
    files: HashSet<FileId>,
    dep_edges: HashSet<(ItemId, DepNode)>,
}

/// What translating each item did, see the module docs.
#[derive(Default)]
pub(crate) struct TranslationLog<'tcx> {
    /// The logs being recorded, innermost last.
    open: Vec<OpenLog>,
    start: Vec<Event>,
    /// What happened outside of the logs above, in order.
    outside: Vec<Event>,
    items: HashMap<ItemOrModuleId, Vec<Event>>,
    namings: HashMap<ItemId, Vec<Event>>,
    /// The items whose name we stored when registering them.
    named_at_registration: HashSet<ItemId>,
    memos: Vec<Vec<Event>>,
    memo_ids: HashMap<MemoKey<'tcx>, u32>,
    errors: Vec<Option<RecordedError>>,
    dep_edges: Vec<(ItemId, DepNode)>,
    vtables: Vec<GlobalDeclRef>,
    views: Vec<ViewLookup<'tcx>>,
    /// The result of replaying the logs in sequential order.
    replay: Option<ReplayResult>,
    /// The errors before this index were formatted by workers which didn't know all the names:
    /// we redo the translations that raised them.
    worker_errors: u32,
}

impl<'tcx> TranslateCtx<'tcx> {
    /// Start logging what translation does, to be able to renumber with
    /// `renumber_as_sequential` afterwards.
    pub(crate) fn start_translation_log(&mut self) {
        let mut log = TranslationLog::default();
        log.push(LogOwner::Start);
        self.log = Some(Box::new(log));
        self.errors.get_mut().recording = Some(ErrorRecording::default());
        self.hax_state.global_cache().alloc_types.record_lookups();
    }

    /// Whether we're logging what translation does.
    pub(crate) fn is_logging(&self) -> bool {
        self.log.is_some()
    }

    fn log_event(&mut self, event: Event) {
        if let Some(log) = &mut self.log
            && let Some(open) = log.open.last_mut()
        {
            let new = match event {
                Event::Reg(id) => open.regs.insert(id),
                Event::Enq(id) => open.enqs.insert(id),
                Event::File(id) => open.files.insert(id),
                _ => true,
            };
            if new {
                open.events.push(event);
            }
        }
    }

    pub(crate) fn log_registration(&mut self, id: ItemId) {
        self.log_event(Event::Reg(id));
    }
    pub(crate) fn log_enqueue(&mut self, id: ItemOrModuleId) {
        self.log_event(Event::Enq(id));
    }
    pub(crate) fn log_use(&mut self, id: ItemId) {
        self.log_event(Event::Use(id));
    }
    pub(crate) fn log_named(&mut self, id: ItemId) {
        self.log_event(Event::Named(id));
    }
    pub(crate) fn log_mark_method_used(&mut self, trait_id: TraitDeclId, method_id: TraitMethodId) {
        self.log_event(Event::MarkMethodUsed(trait_id, method_id));
    }
    pub(crate) fn log_method_impl(
        &mut self,
        trait_id: TraitDeclId,
        method_id: TraitMethodId,
        fun_id: FunDeclId,
    ) {
        self.log_event(Event::MethodImpl(trait_id, method_id, fun_id));
    }
    pub(crate) fn log_impl_vtable(&mut self, impl_id: TraitImplId, vtable: &GlobalDeclRef) {
        if let Some(log) = &mut self.log {
            let i = log.vtables.len() as u32;
            log.vtables.push(vtable.clone());
            self.log_event(Event::ImplVTable(impl_id, i));
        }
    }
    pub(crate) fn log_fill_lazy_vtable(&mut self, impl_id: TraitImplId, vtable: &GlobalDeclRef) {
        if let Some(log) = &mut self.log {
            let i = log.vtables.len() as u32;
            log.vtables.push(vtable.clone());
            self.log_event(Event::FillLazyVTable(impl_id, i));
        }
    }
    /// Log the files a span uses.
    pub(crate) fn log_span(&mut self, span: Span) {
        if let Some(log) = &self.log
            && let Some(open) = log.open.last()
            && span.file_ids().all(|id| open.files.contains(&id))
        {
            return;
        }
        // In the order `translate_span` registers them.
        let span = span.unpack();
        for data in [span.generated_from_span, Some(span.data)]
            .into_iter()
            .flatten()
        {
            self.log_event(Event::File(data.file_id));
        }
    }

    /// Move the errors, dependencies and view lookups recorded so far into the innermost log.
    fn log_recorded_errors(&mut self) {
        let Some(log) = &mut self.log else {
            return;
        };
        let views = self.hax_state.global_cache().alloc_types.take_lookups();
        if !views.is_empty() {
            let start = log.views.len() as u32;
            log.views.extend(views);
            let end = log.views.len() as u32;
            match log.open.last_mut() {
                Some(open) => &mut open.events,
                None => &mut log.outside,
            }
            .push(Event::Views(start, end));
        }
        let errors = self.errors.get_mut();
        let Some(recording) = &mut errors.recording else {
            return;
        };
        let (events, seen_edges) = match log.open.last_mut() {
            Some(open) => (&mut open.events, Some(&mut open.dep_edges)),
            None => (&mut log.outside, None),
        };
        if !recording.dep_edges.is_empty() {
            let start = log.dep_edges.len() as u32;
            match seen_edges {
                Some(seen) => log.dep_edges.extend(
                    recording
                        .dep_edges
                        .drain(..)
                        .filter(|edge| seen.insert(*edge)),
                ),
                None => log.dep_edges.append(&mut recording.dep_edges),
            }
            let end = log.dep_edges.len() as u32;
            if end > start {
                events.push(Event::DepEdges(start, end));
            }
        }
        if !recording.errors.is_empty() {
            let start = log.errors.len() as u32;
            log.errors.extend(recording.errors.drain(..).map(Some));
            let end = log.errors.len() as u32;
            events.push(Event::Errors(start, end));
        }
    }

    fn log_push(&mut self, owner: LogOwner) {
        self.log_recorded_errors();
        self.log.as_mut().unwrap().push(owner);
    }

    fn log_pop(&mut self) -> (LogOwner, Vec<Event>) {
        self.log_recorded_errors();
        let mut open = self.log.as_mut().unwrap().open.pop().unwrap();
        open.events.shrink_to_fit();
        (open.owner, open.events)
    }

    /// Finish logging what happens before translating items.
    pub(crate) fn log_finish_start(&mut self) {
        if self.log.is_some() {
            let (LogOwner::Start, events) = self.log_pop() else {
                unreachable!()
            };
            self.log.as_mut().unwrap().start = events;
        }
    }

    pub(crate) fn log_start_item(&mut self, id: ItemOrModuleId) {
        if self.log.is_some() {
            self.log_push(LogOwner::Item(id));
        }
    }
    pub(crate) fn log_finish_item(&mut self) {
        if self.log.is_some() {
            let (LogOwner::Item(id), events) = self.log_pop() else {
                unreachable!()
            };
            self.log.as_mut().unwrap().items.insert(id, events);
        }
    }

    pub(crate) fn log_start_naming(&mut self, id: ItemId) {
        if self.log.is_some() {
            self.log_push(LogOwner::Naming(id));
        }
    }
    pub(crate) fn log_finish_naming(&mut self, named: bool) {
        if self.log.is_some() {
            let (LogOwner::Naming(id), events) = self.log_pop() else {
                unreachable!()
            };
            let log = self.log.as_mut().unwrap();
            log.namings.insert(id, events);
            if named {
                log.named_at_registration.insert(id);
            }
        }
    }

    pub(crate) fn log_start_discarded(&mut self) {
        if self.log.is_some() {
            self.log_push(LogOwner::Discarded);
        }
    }
    pub(crate) fn log_finish_discarded(&mut self) {
        if self.log.is_some() {
            let (LogOwner::Discarded, _) = self.log_pop() else {
                unreachable!()
            };
        }
    }

    pub(crate) fn log_start_memo(&mut self) {
        if self.log.is_some() {
            self.log_push(LogOwner::Memo);
        }
    }
    /// Finish a memoized computation, memoized under `key` if `memoized`.
    pub(crate) fn log_finish_memo(&mut self, memoized: bool, key: impl FnOnce() -> MemoKey<'tcx>) {
        if self.log.is_some() {
            let (LogOwner::Memo, events) = self.log_pop() else {
                unreachable!()
            };
            if memoized {
                let log = self.log.as_mut().unwrap();
                let memo_id = log.memos.len() as u32;
                log.memos.push(events);
                log.memo_ids.insert(key(), memo_id);
                self.log_event(Event::Memo(MemoRef {
                    worker: self.worker_index as u32,
                    index: memo_id,
                }));
            } else {
                for event in events {
                    self.log_event(event);
                }
            }
        }
    }
    /// Log that we reuse the result of the computation memoized under `key`.
    pub(crate) fn log_replay_memo(&mut self, key: impl FnOnce() -> MemoKey<'tcx>) {
        if let Some(log) = &self.log
            && let Some(&memo_id) = log.memo_ids.get(&key())
        {
            self.log_event(Event::Memo(MemoRef {
                worker: self.worker_index as u32,
                index: memo_id,
            }));
        }
    }
    /// The memoized computation of `key` in this context's log, if any.
    pub(crate) fn log_memo_ref(&self, key: &MemoKey<'tcx>) -> Option<MemoRef> {
        let index = *self.log.as_ref()?.memo_ids.get(key)?;
        Some(MemoRef {
            worker: self.worker_index as u32,
            index,
        })
    }
    /// Finish a memoized computation whose result is shared with other workers. Returns how to
    /// refer to its log.
    pub(crate) fn log_finish_shared_memo(&mut self, memoized: bool) -> Option<MemoRef> {
        self.log.as_ref()?;
        let (LogOwner::Memo, events) = self.log_pop() else {
            unreachable!()
        };
        if !memoized {
            for event in events {
                self.log_event(event);
            }
            return None;
        }
        let log = self.log.as_mut().unwrap();
        let memo = MemoRef {
            worker: self.worker_index as u32,
            index: log.memos.len() as u32,
        };
        log.memos.push(events);
        self.log_event(Event::Memo(memo));
        Some(memo)
    }
    /// Log that we reuse the result of this memoized computation.
    pub(crate) fn log_replay_memo_ref(&mut self, memo: Option<MemoRef>) {
        if let Some(memo) = memo {
            self.log_event(Event::Memo(memo));
        }
    }
    /// Whether we're logging a memoized computation. It must not reuse values computed earlier in
    /// the current item, as it wouldn't log what computing them did.
    pub(crate) fn log_recording_memo(&self) -> bool {
        self.log
            .as_ref()
            .and_then(|log| log.open.last())
            .is_some_and(|open| matches!(open.owner, LogOwner::Memo))
    }

    /// Replay the sequential worklist over the logs, redoing the translations that depend on the
    /// order. Call `renumber_as_sequential` afterwards.
    pub(crate) fn replay_sequential_order(&mut self) {
        self.log_recorded_errors();
        let allocs: HashSet<ItemId> = self
            .reverse_id_map
            .iter()
            .filter(|(_, src)| matches!(src.def_id().base, crate::hax::DefIdBase::Alloc(_)))
            .map(|(id, _)| *id)
            .collect();
        // Replay; if some items saw other views of allocations than in sequential order, or weren't
        // translated, translate them now and try again.
        let mut rounds = 0;
        let replay = loop {
            let stored: HashSet<ItemId> = self.translated.all_ids().collect();
            let mut replay = Replay::new(self.log.as_deref().unwrap(), &allocs, &stored);
            replay.run();
            if replay.to_translate.is_empty() {
                break replay.into_result();
            }
            rounds += 1;
            assert!(rounds < 10, "translation order doesn't converge");
            let views = std::mem::take(&mut replay.views);
            let to_translate = std::mem::take(&mut replay.to_translate);
            drop(replay);
            let alloc_types = self.hax_state.global_cache().alloc_types.clone();
            for (alloc_id, view) in views {
                alloc_types.force_view(alloc_id, view);
            }
            for id in to_translate {
                if let ItemOrModuleId::Item(id) = id {
                    self.translated.remove_item_temporarily(id);
                    self.errors.get_mut().forget_item_errors(id);
                }
                let src = match id {
                    ItemOrModuleId::Item(id) => self.reverse_id_map[&id].clone(),
                    ItemOrModuleId::Module(_) => continue,
                };
                self.translate_item(&src);
            }
            self.log_recorded_errors();
        };
        // Free what renumbering doesn't need.
        let log = &mut **self.log.as_mut().unwrap();
        let errors = std::mem::take(&mut log.errors);
        let dep_edges = std::mem::take(&mut log.dep_edges);
        let vtables = std::mem::take(&mut log.vtables);
        let mut replay = replay;
        replay.reverse_ids = Default::default();
        *log = TranslationLog {
            errors,
            dep_edges,
            vtables,
            replay: Some(replay),
            ..Default::default()
        };
    }

    /// Renumber items and files as the sequential translation would have, using the result of
    /// `replay_sequential_order`.
    pub(crate) fn renumber_as_sequential(&mut self) {
        let mut log = *self.log.take().unwrap();
        let replay = log.replay.take().unwrap();
        let errors = self.errors.get_mut();
        // The errors are counted again as we replay them.
        errors.error_count -= errors.recording.take().unwrap().count;
        errors.clear_items_with_errors();

        // The impls refer to their vtable as they would have in sequential order.
        for (impl_id, state) in &replay.vtables {
            if let Some(timpl) = self.translated.trait_impls.get_mut(*impl_id)
                && matches!(timpl.vtable, VTableDecl::Lazy | VTableDecl::VTable(_))
            {
                timpl.vtable = match state {
                    None => VTableDecl::Lazy,
                    Some(i) => VTableDecl::VTable(log.vtables[*i as usize].clone()),
                };
            }
        }

        let mut renumber = Renumber {
            ids: &replay.ids,
            files: &replay.files,
            memo: Default::default(),
        };
        renumber.apply(self, &replay.counts, &replay.names, &replay.alloc_order);

        // Report the errors in order.
        let errors = self.errors.get_mut();
        for diagnostic in replay.diagnostics {
            match diagnostic {
                Diagnostic::Error(i) => {
                    let mut error = log.errors[i as usize].take().unwrap();
                    error.span = renumber.span(error.span);
                    error.def_id = error.def_id.map(|id| renumber.item_id(id));
                    errors.replay_error(&self.translated, error);
                }
                Diagnostic::DepEdges(start, end) => {
                    for &(from, to) in &log.dep_edges[start as usize..end as usize] {
                        errors.insert_dep_edge(renumber.item_id(from), renumber.dep_node(to));
                    }
                }
            }
        }
        errors.def_id = None;
        errors.def_id_is_local = false;
    }
}

impl<'tcx> TranslationLog<'tcx> {
    /// Merge the logs of the workers, given in the order of their index. An item translated by
    /// several workers keeps the log of the first.
    pub(crate) fn merge(logs: Vec<Self>) -> Self {
        let mut memo_offsets = vec![];
        let mut memo_count = 0;
        for log in &logs {
            memo_offsets.push(memo_count);
            memo_count += log.memos.len() as u32;
        }
        let mut merged = Self::default();
        for (worker, log) in logs.into_iter().enumerate() {
            assert!(log.open.is_empty());
            let errors = merged.errors.len() as u32;
            let dep_edges = merged.dep_edges.len() as u32;
            let vtables = merged.vtables.len() as u32;
            let views = merged.views.len() as u32;
            let rebase = |mut events: Vec<Event>| -> Vec<Event> {
                for event in &mut events {
                    *event = match *event {
                        Event::Memo(MemoRef { worker, index }) => Event::Memo(MemoRef {
                            worker: 0,
                            index: memo_offsets[worker as usize] + index,
                        }),
                        Event::Errors(start, end) => Event::Errors(start + errors, end + errors),
                        Event::DepEdges(start, end) => {
                            Event::DepEdges(start + dep_edges, end + dep_edges)
                        }
                        Event::ImplVTable(id, i) => Event::ImplVTable(id, i + vtables),
                        Event::FillLazyVTable(id, i) => Event::FillLazyVTable(id, i + vtables),
                        Event::Views(start, end) => Event::Views(start + views, end + views),
                        event => event,
                    }
                }
                events
            };
            if worker == 0 {
                merged.start = rebase(log.start);
            }
            merged.outside.extend(rebase(log.outside));
            for (id, events) in log.items {
                merged.items.entry(id).or_insert_with(|| rebase(events));
            }
            for (id, events) in log.namings {
                merged.namings.entry(id).or_insert_with(|| rebase(events));
            }
            merged
                .named_at_registration
                .extend(log.named_at_registration);
            merged.memos.extend(log.memos.into_iter().map(rebase));
            for (key, index) in log.memo_ids {
                merged
                    .memo_ids
                    .entry(key)
                    .or_insert(memo_offsets[worker] + index);
            }
            merged.errors.extend(log.errors);
            merged.dep_edges.extend(log.dep_edges);
            merged.vtables.extend(log.vtables);
            merged.views.extend(log.views);
        }
        merged
    }

    pub(crate) fn mark_worker_errors(&mut self) {
        self.worker_errors = self.errors.len() as u32;
    }

    fn push(&mut self, owner: LogOwner) {
        self.open.push(OpenLog {
            owner,
            events: Default::default(),
            regs: Default::default(),
            enqs: Default::default(),
            files: Default::default(),
            dep_edges: Default::default(),
        });
    }
}

/// A diagnostic, in the order of the sequential translation.
enum Diagnostic {
    Error(u32),
    DepEdges(u32, u32),
}

enum MethodState {
    Unused(HashSet<FunDeclId>),
    Used,
}

/// Replays the sequential worklist over the logs.
struct Replay<'a, 'tcx> {
    log: &'a TranslationLog<'tcx>,
    allocs: &'a HashSet<ItemId>,
    /// The items that got translated.
    stored: &'a HashSet<ItemId>,
    /// The items whose translation we're replaying, innermost last.
    stack: Vec<ItemOrModuleId>,
    /// Whether we're replaying the computation of a name, at registration.
    naming_depth: usize,
    /// The items whose translation we replayed entirely.
    finished: HashSet<ItemOrModuleId>,
    queue: VecDeque<ItemOrModuleId>,
    processed: HashSet<ItemOrModuleId>,
    /// The usage of each method, with sequential ids.
    methods: HashMap<(ItemId, TraitMethodId), MethodState>,
    memos_with_errors_done: HashSet<u32>,
    /// The views of allocations, as decided in sequential order.
    views: HashMap<AllocId, AllocView<'tcx>>,
    /// The items whose translation we must redo because they saw other views than in
    /// sequential order, or that we must translate because they weren't.
    to_translate: Vec<ItemOrModuleId>,
    result: ReplayResult,
}

/// What we learn from replaying.
#[derive(Default)]
struct ReplayResult {
    /// The sequential id of each item.
    ids: HashMap<ItemId, ItemId>,
    reverse_ids: HashMap<ItemId, ItemId>,
    /// The number of items of each kind: types, functions, globals, trait decls, trait impls.
    counts: [usize; 5],
    /// The sequential id of each file.
    files: HashMap<FileId, FileId>,
    /// The items whose name we stored, in order.
    names: Vec<ItemId>,
    /// The anonymous allocations, in order of registration.
    alloc_order: Vec<ItemId>,
    diagnostics: Vec<Diagnostic>,
    /// The vtable each impl refers to, if any.
    vtables: HashMap<TraitImplId, Option<u32>>,
}

fn kind_index(id: ItemId) -> usize {
    match id {
        ItemId::Type(_) => 0,
        ItemId::Fun(_) => 1,
        ItemId::Global(_) => 2,
        ItemId::TraitDecl(_) => 3,
        ItemId::TraitImpl(_) => 4,
    }
}

fn item_id_of_kind(kind_of: ItemId, index: usize) -> ItemId {
    match kind_of {
        ItemId::Type(_) => ItemId::Type(TypeDeclId::from_usize(index)),
        ItemId::Fun(_) => ItemId::Fun(FunDeclId::from_usize(index)),
        ItemId::Global(_) => ItemId::Global(GlobalDeclId::from_usize(index)),
        ItemId::TraitDecl(_) => ItemId::TraitDecl(TraitDeclId::from_usize(index)),
        ItemId::TraitImpl(_) => ItemId::TraitImpl(TraitImplId::from_usize(index)),
    }
}

impl<'a, 'tcx> Replay<'a, 'tcx> {
    fn new(
        log: &'a TranslationLog<'tcx>,
        allocs: &'a HashSet<ItemId>,
        stored: &'a HashSet<ItemId>,
    ) -> Self {
        Replay {
            log,
            allocs,
            stored,
            stack: Default::default(),
            naming_depth: 0,
            finished: Default::default(),
            queue: Default::default(),
            processed: Default::default(),
            methods: Default::default(),
            memos_with_errors_done: Default::default(),
            views: Default::default(),
            to_translate: Default::default(),
            result: Default::default(),
        }
    }

    fn into_result(self) -> ReplayResult {
        self.result
    }

    fn run(&mut self) {
        let log = self.log;
        self.replay(&log.start, None);
        while let Some(id) = self.queue.pop_front() {
            self.translate(id);
        }
        // These happened between item translations, we don't know when exactly.
        self.replay(&log.outside, None);
    }

    fn translate(&mut self, id: ItemOrModuleId) {
        if !self.processed.insert(id) {
            return;
        }
        let log = self.log;
        match log.items.get(&id) {
            Some(events) => {
                self.stack.push(id);
                self.replay(events, None);
                self.stack.pop();
            }
            None => self.to_translate.push(id),
        }
        self.finished.insert(id);
    }

    /// Whether the sequential translation has translated this item.
    fn is_translated(&self, id: ItemId) -> bool {
        self.finished.contains(&ItemOrModuleId::Item(id)) && self.stored.contains(&id)
    }

    fn register(&mut self, id: ItemId) {
        if self.result.ids.contains_key(&id) {
            return;
        }
        let kind = kind_index(id);
        let new_id = item_id_of_kind(id, self.result.counts[kind]);
        self.result.counts[kind] += 1;
        self.result.ids.insert(id, new_id);
        self.result.reverse_ids.insert(new_id, id);
        if self.allocs.contains(&id) {
            self.result.alloc_order.push(id);
        }
        let log = self.log;
        if let Some(events) = log.namings.get(&id) {
            self.naming_depth += 1;
            self.replay(events, None);
            self.naming_depth -= 1;
        }
        if log.named_at_registration.contains(&id) {
            self.result.names.push(id);
        }
    }

    fn enqueue_fun(&mut self, id: FunDeclId) {
        let id = ItemOrModuleId::Item(id.into());
        if !self.processed.contains(&id) {
            self.queue.push_back(id);
        }
    }

    fn replay(&mut self, events: &[Event], memo: Option<u32>) {
        for &event in events {
            match event {
                Event::Reg(id) => self.register(id),
                Event::Enq(id) => self.queue.push_back(id),
                Event::Use(id) => self.translate(ItemOrModuleId::Item(id)),
                Event::Named(id) => self.result.names.push(id),
                Event::Memo(MemoRef { worker, index }) => {
                    assert_eq!(worker, 0, "unmerged logs");
                    let log = self.log;
                    self.replay(&log.memos[index as usize], Some(index));
                    self.memos_with_errors_done.insert(index);
                }
                Event::File(id) => {
                    let next = FileId::from_usize(self.result.files.len());
                    self.result.files.entry(id).or_insert(next);
                }
                Event::MarkMethodUsed(trait_id, method_id) => {
                    let key = (ItemId::TraitDecl(trait_id), method_id);
                    if let Some(MethodState::Unused(impls)) =
                        self.methods.insert(key, MethodState::Used)
                    {
                        for fun_id in impls {
                            let ItemId::Fun(fun_id) = self.result.reverse_ids[&fun_id.into()]
                            else {
                                unreachable!()
                            };
                            self.enqueue_fun(fun_id);
                        }
                    }
                }
                Event::MethodImpl(trait_id, method_id, fun_id) => {
                    let key = (ItemId::TraitDecl(trait_id), method_id);
                    let state = self
                        .methods
                        .entry(key)
                        .or_insert_with(|| MethodState::Unused(Default::default()));
                    match state {
                        MethodState::Unused(impls) => {
                            let ItemId::Fun(new_id) = self.result.ids[&fun_id.into()] else {
                                unreachable!()
                            };
                            impls.insert(new_id);
                        }
                        MethodState::Used => self.enqueue_fun(fun_id),
                    }
                }
                Event::Errors(start, end) => {
                    if start < self.log.worker_errors
                        && self.naming_depth == 0
                        && let Some(&item) = self.stack.last()
                        && !self.to_translate.contains(&item)
                    {
                        self.to_translate.push(item);
                    }
                    // The errors of a memoized computation are only reported the first time.
                    if memo.is_none_or(|memo| !self.memos_with_errors_done.contains(&memo)) {
                        self.result
                            .diagnostics
                            .extend((start..end).map(Diagnostic::Error));
                    }
                }
                Event::DepEdges(start, end) => {
                    self.result
                        .diagnostics
                        .push(Diagnostic::DepEdges(start, end));
                }
                Event::ImplVTable(impl_id, i) => {
                    let vtable_id = self.log.vtables[i as usize].id;
                    let state = self.is_translated(vtable_id.into()).then_some(i);
                    self.result.vtables.insert(impl_id, state);
                }
                Event::FillLazyVTable(impl_id, i) => {
                    if self.is_translated(impl_id.into())
                        && let Some(state @ None) = self.result.vtables.get_mut(&impl_id)
                    {
                        *state = Some(i);
                    }
                }
                Event::Views(start, end) => {
                    for lookup in &self.log.views[start as usize..end as usize] {
                        let view = *self.views.entry(lookup.alloc_id).or_insert(lookup.default);
                        if view != lookup.view
                            && let Some(&item) = self.stack.last()
                            && !self.to_translate.contains(&item)
                        {
                            self.to_translate.push(item);
                        }
                    }
                }
            }
        }
    }
}

/// Renames items and files to their sequential ids.
#[derive(Visitor)]
struct Renumber<'a> {
    ids: &'a HashMap<ItemId, ItemId>,
    files: &'a HashMap<FileId, FileId>,
    memo: HashConsMemo<()>,
}

impl Renumber<'_> {
    fn item_id(&self, id: ItemId) -> ItemId {
        *self
            .ids
            .get(&id)
            .unwrap_or_else(|| panic!("item {id:?} was not registered in sequential order"))
    }
    fn typed_id<I: Into<ItemId> + TryFrom<ItemId, Error: std::fmt::Debug>>(&self, id: I) -> I {
        self.item_id(id.into()).try_into().unwrap()
    }
    fn file_id(&self, id: FileId) -> FileId {
        *self
            .files
            .get(&id)
            .unwrap_or_else(|| panic!("file {id:?} was not used in sequential order"))
    }
    fn span(&self, mut span: Span) -> Span {
        span.map_file_ids(|id| self.file_id(id));
        span
    }
    fn dep_node(&self, node: DepNode) -> DepNode {
        match node {
            DepNode::External(id) => DepNode::External(self.item_id(id)),
            DepNode::Local(id, span) => DepNode::Local(self.item_id(id), self.span(span)),
        }
    }

    /// Renumber the translated crate.
    fn apply(
        &mut self,
        ctx: &mut TranslateCtx<'_>,
        counts: &[usize; 5],
        names: &[ItemId],
        alloc_order: &[ItemId],
    ) {
        let krate = &mut ctx.translated;
        fn move_items<
            I: charon_lib::ids::Idx + Into<ItemId> + TryFrom<ItemId, Error: std::fmt::Debug>,
            T,
        >(
            this: &Renumber<'_>,
            items: &mut IndexMap<I, T>,
            count: usize,
        ) {
            // We permute the items in place, following cycles, to not need a second copy.
            let mut placed = vec![false; items.slot_count().max(count)];
            for i in 0..items.slot_count() {
                if placed[i] {
                    continue;
                }
                let mut current = items.remove(I::from_usize(i)).map(|item| (i, item));
                while let Some((old_index, item)) = current {
                    // Drop items that the sequential translation doesn't reach: their translation
                    // was redone without referring to them.
                    let Some(&new_id) = this.ids.get(&I::from_usize(old_index).into()) else {
                        break;
                    };
                    let new_id: I = new_id.try_into().unwrap();
                    let displaced = items.remove(new_id);
                    items.insert(new_id, item);
                    placed[new_id.index()] = true;
                    current = displaced.map(|item| (new_id.index(), item));
                }
            }
            items.truncate(count);
            items.reserve_slots(count - items.slot_count());
        }
        // The visitor below renames the ids inside items, we move them to their new slot.
        move_items(self, &mut krate.type_decls, counts[0]);
        move_items(self, &mut krate.fun_decls, counts[1]);
        move_items(self, &mut krate.global_decls, counts[2]);
        move_items(self, &mut krate.trait_decls, counts[3]);
        move_items(self, &mut krate.trait_impls, counts[4]);

        // The anonymous allocations are numbered in order of registration.
        let alloc_numbers: HashMap<ItemId, usize> = alloc_order
            .iter()
            .enumerate()
            .map(|(i, id)| (*id, i))
            .collect();
        let renumber_alloc = |name: &mut Name, number: usize| {
            name.name.with_mut(|elems| {
                for elem in elems {
                    if let PathElem::Builtin(BuiltinPathElem::PromotedConst, disambiguator) = elem {
                        *disambiguator = Disambiguator::from_usize(number);
                    }
                }
            })
        };
        for (&id, &number) in &alloc_numbers {
            if let Some(mut item) = krate.get_item_mut(self.item_id(id)) {
                renumber_alloc(&mut item.item_meta().name, number);
            }
        }
        let mut old_names = std::mem::take(&mut krate.item_names);
        for id in names {
            if let Some(mut name) = old_names.swap_remove(id) {
                if let Some(&number) = alloc_numbers.get(id) {
                    renumber_alloc(&mut name, number);
                }
                // The visitor renames the keys too.
                krate.item_names.insert(*id, name);
            }
        }
        assert!(
            old_names.keys().all(|id| !self.ids.contains_key(id)),
            "names stored out of the log"
        );

        let old_assoc_names = std::mem::take(&mut krate.assoc_item_names);
        for (id, names) in old_assoc_names.into_iter_indexed() {
            krate.assoc_item_names.insert(self.typed_id(id), names);
        }

        let old_files = std::mem::take(&mut krate.files);
        let mut new_files: IndexMap<FileId, File> = IndexMap::new();
        new_files.reserve_slots(old_files.len());
        for (id, file) in old_files.into_iter_enumerated() {
            if let Some(&new_id) = self.files.get(&id) {
                new_files.set_slot(new_id, file);
            }
        }
        krate.files = new_files.into_iter().collect::<IndexVec<FileId, File>>();

        // The items are independent: we renumber them in parallel, then the rest of the crate.
        fn renumber_items<I: charon_lib::ids::Idx, T: AstVisitable + Send>(
            this: &Renumber<'_>,
            items: &mut IndexMap<I, T>,
        ) {
            use rayon::prelude::*;
            let items: Vec<&mut T> = items.iter_mut().collect();
            items.into_par_iter().for_each_init(
                || Renumber {
                    ids: this.ids,
                    files: this.files,
                    memo: Default::default(),
                },
                |renumber, item| {
                    let _ = VisitAstMut::visit(renumber, item);
                },
            );
        }
        renumber_items(self, &mut krate.type_decls);
        renumber_items(self, &mut krate.fun_decls);
        renumber_items(self, &mut krate.global_decls);
        renumber_items(self, &mut krate.trait_decls);
        renumber_items(self, &mut krate.trait_impls);
        let items = (
            std::mem::take(&mut krate.type_decls),
            std::mem::take(&mut krate.fun_decls),
            std::mem::take(&mut krate.global_decls),
            std::mem::take(&mut krate.trait_decls),
            std::mem::take(&mut krate.trait_impls),
        );
        let _ = krate.drive_mut(self);
        (
            krate.type_decls,
            krate.fun_decls,
            krate.global_decls,
            krate.trait_decls,
            krate.trait_impls,
        ) = items;
    }
}

impl VisitorWithMemo for Renumber<'_> {
    type MemoContext = ();
    fn memo(&mut self) -> &mut HashConsMemo<()> {
        &mut self.memo
    }
    fn memo_context(&self) -> Option<()> {
        Some(())
    }
}

impl VisitAstMut for Renumber<'_> {
    fn visit_with_cached_type_info<T: AstVisitable + HashConsable>(
        &mut self,
        x: &mut HashConsed<WithCachedTypeInfo<T>>,
    ) -> ControlFlow<Self::Break> {
        // Hash-consed values that mention no item mention no file either.
        if x.type_info().items == ItemBloom::default() {
            return ControlFlow::Continue(());
        }
        self.visit_memoized(x)
    }
    fn enter_type_decl_id(&mut self, id: &mut TypeDeclId) {
        *id = self.typed_id(*id);
    }
    fn enter_fun_decl_id(&mut self, id: &mut FunDeclId) {
        *id = self.typed_id(*id);
    }
    fn enter_global_decl_id(&mut self, id: &mut GlobalDeclId) {
        *id = self.typed_id(*id);
    }
    fn enter_trait_decl_id(&mut self, id: &mut TraitDeclId) {
        *id = self.typed_id(*id);
    }
    fn enter_trait_impl_id(&mut self, id: &mut TraitImplId) {
        *id = self.typed_id(*id);
    }
    fn enter_file_id(&mut self, id: &mut FileId) {
        *id = self.file_id(*id);
    }
    // Visitors don't explore spans.
    fn enter_span(&mut self, span: &mut Span) {
        *span = self.span(*span);
    }
}
