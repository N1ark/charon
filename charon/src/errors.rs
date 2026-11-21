//! Utilities to generate error reports about the external dependencies.
use crate::ast::*;
use crate::formatter::IntoFormatter;
use crate::pretty::FmtWithCtx;
pub use annotate_snippets::Level;
use itertools::Itertools;
use petgraph::algo::dijkstra::dijkstra;
use petgraph::prelude::DiGraphMap;
use rustc_hash::FxHashSet as HashSet;
use serde::{Deserialize, Serialize};
use std::cmp::{Ord, PartialOrd};
use std::hash::{Hash, Hasher};
use std::io::Write;
use std::ops::Range;
use std::sync::{Arc, Mutex, PoisonError, mpsc};
use std::thread::JoinHandle;

const BACKTRACE_ON_ERR: bool = false;

#[macro_export]
macro_rules! register_error {
    ($ctx:expr, crate($krate:expr), $span: expr, $($fmt:tt)*) => {{
        let msg = format!($($fmt)*);
        $ctx.span_err($krate, $span, &msg, $crate::errors::Level::WARNING)
    }};
    ($ctx:expr, no_crate, $($fmt:tt)*) => {{
        let msg = format!($($fmt)*);
        $ctx.span_err(&Default::default(), Default::default(), &msg, $crate::errors::Level::WARNING)
    }};
    ($ctx:expr, $span: expr, $($fmt:tt)*) => {{
        let msg = format!($($fmt)*);
        $ctx.span_err($span, &msg, $crate::errors::Level::WARNING)
    }};
}
pub use register_error;

/// Macro to either panic or return on error, depending on the CLI options
#[macro_export]
macro_rules! raise_error {
    ($($tokens:tt)*) => {{
        return Err(register_error!($($tokens)*));
    }};
}
pub use raise_error;

/// Custom assert to either panic or return an error
#[macro_export]
macro_rules! error_assert {
    ($ctx:expr, $span: expr, $b: expr) => {
        if !$b {
            $crate::errors::raise_error!($ctx, $span, "assertion failure: {:?}", stringify!($b));
        }
    };
    ($ctx:expr, $span: expr, $b: expr, $($fmt:tt)*) => {
        if !$b {
            $crate::errors::raise_error!($ctx, $span, $($fmt)*);
        }
    };
}
pub use error_assert;

/// Common error used during the translation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[derive(Serialize, Deserialize)]
pub struct Error {
    pub span: Span,
    pub msg: String,
}

impl Error {
    pub fn new(span: Span, msg: String) -> Self {
        Self { span, msg }
    }
    pub fn dummy() -> Self {
        Self {
            span: Span::dummy(),
            msg: String::new(),
        }
    }

    pub fn render(&self, krate: &TranslatedCrate, level: Level) -> String {
        use annotate_snippets::*;
        let span = self.span.data();

        let mut group = Group::with_title(level.primary_title(&self.msg));
        let origin;
        if let Some(file) = krate.files.get(span.file_id) {
            origin = format!("{}", file.name);
            if let Some(source) = &file.contents {
                let (source, line_start, range) =
                    covering_lines(source, span.to_byte_range(source));
                let snippet = Snippet::source(source)
                    .line_start(line_start)
                    .path(&origin)
                    .fold(true)
                    .annotation(AnnotationKind::Primary.span(range));
                group = group.element(snippet);
            } else {
                // Show just the file and line/col.
                let origin = Origin::path(&origin)
                    .line(span.beg.line as usize)
                    .char_column(span.beg.col as usize + 1);
                group = group.element(origin);
            }
        }

        Renderer::styled().render(&[group]).to_string()
    }
}

/// The lines of `source` that `range` touches, the number of the first one, and `range` relative to
/// them. The renderer takes time linear in the source it is given, so we only give it these lines.
fn covering_lines(source: &str, range: Range<usize>) -> (&str, usize, Range<usize>) {
    if range.start > range.end || range.end > source.len() {
        return (source, 1, range);
    }
    let bytes = source.as_bytes();
    let line_start_before = |pos: usize| {
        bytes[..pos]
            .iter()
            .rposition(|&b| b == b'\n')
            .map_or(0, |i| i + 1)
    };
    let mut lo = line_start_before(range.start);
    // The renderer counts lines in the text before the end of the range: keep that text non-empty.
    if range.end == lo && lo > 0 {
        lo = line_start_before(lo - 1);
    }
    let hi = bytes[range.end..]
        .iter()
        .position(|&b| b == b'\n')
        .map_or(source.len(), |i| range.end + i + 1);
    let line_start = 1 + bytes[..lo].iter().filter(|&&b| b == b'\n').count();
    (
        &source[lo..hi],
        line_start,
        range.start - lo..range.end - lo,
    )
}

/// Attach a source span to an error.
pub trait ErrorContext<T> {
    fn context(self, span: Span) -> Result<T, Error>;
}

impl<T, E: ToString> ErrorContext<T> for Result<T, E> {
    fn context(self, span: Span) -> Result<T, Error> {
        self.map_err(|error| Error::new(span, error.to_string()))
    }
}

impl<T: ToString> From<T> for Error {
    fn from(err: T) -> Self {
        Self {
            span: Span::dummy(),
            msg: err.to_string(),
        }
    }
}

/// Display an error without a specific location.
pub fn display_unspanned_error(level: Level, msg: &str) {
    use annotate_snippets::*;
    let title = level.primary_title(msg);
    let message = Renderer::styled()
        .render(&[Group::with_title(title)])
        .to_string();
    anstream::eprintln!("{message}\n");
}

/// Display an error at the given source span.
pub fn display_spanned_error(krate: &TranslatedCrate, span: Span, title: &str, label: &str) {
    use annotate_snippets::*;

    let span = span.data();
    let mut group = Group::with_title(Level::ERROR.primary_title(title));
    let origin;
    if let Some(file) = krate.files.get(span.file_id) {
        origin = file.name.to_string();
        if let Some(source) = &file.contents {
            let snippet = Snippet::source(source).path(&origin).annotation(
                AnnotationKind::Primary
                    .span(span.to_byte_range(source))
                    .label(label),
            );
            group = group.element(snippet);
        } else {
            let origin = Origin::path(origin)
                .line(span.beg.line as usize)
                .char_column(span.beg.col as usize + 1);
            group = group.element(origin);
        }
    }

    let diagnostic = [group];
    anstream::eprintln!("{}", Renderer::styled().render(&diagnostic));
}

/// We use this to save the origin of an id. This is useful for the external
/// dependencies, especially if some external dependencies don't extract:
/// we use this information to tell the user what is the code which
/// (transitively) lead to the extraction of those problematic dependencies.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DepSource {
    pub src_id: ItemId,
    /// The location where the id was referred to. We store `None` for external dependencies as we
    /// don't want to show these to the users.
    pub span: Option<Span>,
}

/// For tracing error dependencies.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum DepNode {
    External(ItemId),
    /// We use the span information only for local references
    Local(ItemId, Span),
}

/// Graph of dependencies between erroring definitions and the definitions they came from. Edges
/// always start from an external item, so we store them by kind of target to keep them small.
struct DepGraph {
    /// Edges from an external item to the external items that registered it.
    external_edges: HashSet<(ItemId, ItemId)>,
    /// Edges from an external item to the places in local items that registered it.
    local_edges: HashSet<(ItemId, ItemId, Span)>,
}

impl DepGraph {
    fn new() -> Self {
        DepGraph {
            external_edges: Default::default(),
            local_edges: Default::default(),
        }
    }

    fn insert_edge(&mut self, from: ItemId, to: DepNode) {
        match to {
            DepNode::External(to) => self.external_edges.insert((from, to)),
            DepNode::Local(to, span) => self.local_edges.insert((from, to, span)),
        };
    }

    fn graph(&self) -> DiGraphMap<DepNode, (), rustc_hash::FxBuildHasher> {
        let external = self
            .external_edges
            .iter()
            .map(|&(from, to)| (DepNode::External(from), DepNode::External(to)));
        let local = self
            .local_edges
            .iter()
            .map(|&(from, to, span)| (DepNode::External(from), DepNode::Local(to, span)));
        DiGraphMap::from_edges(external.chain(local))
    }
}

/// The context for tracking and reporting errors.
pub struct ErrorCtx {
    /// If true, do not abort on the first error and attempt to extract as much as possible.
    pub continue_on_failure: bool,
    /// If true, print the warnings as errors, and abort if any errors were raised.
    pub error_on_warnings: bool,

    /// The ids of the items for which extraction encountered errors.
    items_with_errors: HashSet<ItemId>,
    /// Graph of dependencies between items: there is an edge from item `a` to item `b` if `b`
    /// registered the id for `a` during its translation. Because we only use this to report errors
    /// on external items, we only record edges where `a` is an external item.
    external_dep_graph: DepGraph,
    /// The id of the definition we are exploring, used to track the source of errors.
    pub def_id: Option<ItemId>,
    /// Whether the definition being explored is local to the crate or not.
    pub def_id_is_local: bool,
    /// The number of errors encountered so far.
    pub error_count: usize,
    /// If set, our messages are held back here instead of printed.
    pub deferred_output: Option<Arc<Mutex<DeferredOutput>>>,
    /// Hashes of the diagnostics displayed so far (span, message and level), to display each only
    /// once: passes can run into the same problem many times at the same place.
    displayed: HashSet<u64>,
}

/// Like `anstream::eprintln!`, but in a single write: stderr is unbuffered, and `anstream` writes
/// every styled chunk separately.
fn eprintln_at_once(msg: &str) {
    let stderr = std::io::stderr();
    let mut buffer = anstream::AutoStream::new(Vec::new(), anstream::AutoStream::choice(&stderr));
    let _ = writeln!(buffer, "{msg}");
    let buffer = buffer.into_inner();
    let result = match &*STDERR_THREAD.lock().unwrap_or_else(PoisonError::into_inner) {
        // The thread only stops receiving once it was told to finish, under this lock.
        Some((sender, _)) => {
            sender.send(buffer).unwrap();
            Ok(())
        }
        None => write_to_stderr(&buffer),
    };
    if let Err(e) = result {
        panic!("failed printing to stderr: {e}");
    }
}

fn write_to_stderr(bytes: &[u8]) -> std::io::Result<()> {
    match std::io::stderr().lock().write_all(bytes) {
        Err(e) if e.kind() != std::io::ErrorKind::BrokenPipe => Err(e),
        _ => Ok(()),
    }
}

/// While this is set, `eprintln_at_once` hands its output to a thread that prints it in order, so
/// that we don't wait for a slow reader of stderr (cargo reads it line by line).
static STDERR_THREAD: Mutex<Option<(mpsc::Sender<Vec<u8>>, JoinHandle<std::io::Result<()>>)>> =
    Mutex::new(None);

/// Print the output of `eprintln_at_once` from a separate thread until
/// `finish_printing_in_background`. Everything else that prints to stderr in the meantime must
/// call `finish_printing_in_background` first.
pub fn print_in_background() {
    let (sender, receiver) = mpsc::channel::<Vec<u8>>();
    let thread = std::thread::spawn(move || {
        let mut result = Ok(());
        for bytes in receiver {
            if result.is_ok() {
                result = write_to_stderr(&bytes);
            }
        }
        result
    });
    let previous = STDERR_THREAD
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .replace((sender, thread));
    assert!(previous.is_none());
}

/// Wait until the output handed to the printing thread is printed, and print directly from now
/// on.
pub fn finish_printing_in_background() -> std::io::Result<()> {
    // We keep the lock until the thread is done, so that nothing is printed in the meantime.
    let mut guard = STDERR_THREAD.lock().unwrap_or_else(PoisonError::into_inner);
    match guard.take() {
        Some((sender, thread)) => {
            // This ends the thread's loop.
            drop(sender);
            thread.join().unwrap()
        }
        None => Ok(()),
    }
}

/// Messages held back until `release` is called. We use this when translating in parallel with
/// rustc's own checks, so as to report nothing if rustc rejects the crate.
#[derive(Default)]
pub struct DeferredOutput {
    released: bool,
    messages: Vec<String>,
}

impl DeferredOutput {
    /// Print the held-back messages, and let subsequent ones through.
    pub fn release(&mut self) {
        self.released = true;
        for msg in self.messages.drain(..) {
            eprintln_at_once(&msg);
        }
    }
}

impl ErrorCtx {
    pub fn new() -> Self {
        Self {
            continue_on_failure: true,
            error_on_warnings: false,
            items_with_errors: HashSet::default(),
            external_dep_graph: DepGraph::new(),
            def_id: None,
            def_id_is_local: false,
            error_count: 0,
            deferred_output: None,
            displayed: HashSet::default(),
        }
    }

    pub fn continue_on_failure(&self) -> bool {
        self.continue_on_failure
    }
    pub fn has_errors(&self) -> bool {
        self.error_count > 0
    }
    pub fn item_has_errors(&self, id: impl Into<ItemId>) -> bool {
        self.items_with_errors.contains(&id.into())
    }

    /// Print a message, or hold it back if requested.
    pub(crate) fn emit(&self, msg: String) {
        if let Some(deferred) = &self.deferred_output {
            let mut deferred = deferred.lock().unwrap();
            if !deferred.released {
                deferred.messages.push(msg);
                return;
            }
        }
        eprintln_at_once(&msg);
    }

    /// Report an error without registering anything. `rendered` is the error rendered at `level`,
    /// if already known.
    pub fn display_error(
        &self,
        krate: &TranslatedCrate,
        span: Span,
        level: Level,
        msg: String,
        rendered: Option<String>,
    ) -> Error {
        let error = Error { span, msg };
        let rendered = rendered.unwrap_or_else(|| error.render(krate, level));
        self.emit(format!("{rendered}\n"));
        if BACKTRACE_ON_ERR {
            let backtrace = std::backtrace::Backtrace::force_capture();
            eprintln!("{backtrace}\n");
        }
        error
    }

    /// What identifies a diagnostic: we display each one once.
    pub(crate) fn display_key(span: Span, msg: &str, level: &Level) -> u64 {
        let mut hasher = std::hash::DefaultHasher::new();
        (span, msg, format!("{level:?}")).hash(&mut hasher);
        hasher.finish()
    }

    /// Report and register an error.
    pub fn span_err(
        &mut self,
        krate: &TranslatedCrate,
        span: Span,
        msg: &str,
        level: Level,
    ) -> Error {
        self.span_err_rendered(krate, span, msg, level, None)
    }

    /// Like `span_err`, given the `display_key` and the rendering of the error at `level` if
    /// they're already known.
    pub(crate) fn span_err_rendered(
        &mut self,
        krate: &TranslatedCrate,
        span: Span,
        msg: &str,
        level: Level,
        rendered: Option<(u64, String)>,
    ) -> Error {
        let (level, rendered) = if level == Level::WARNING && self.error_on_warnings {
            (Level::ERROR, None)
        } else {
            (level, rendered)
        };
        let (key, rendered) = match rendered {
            Some((key, rendered)) => (key, Some(rendered)),
            None => (Self::display_key(span, msg, &level), None),
        };
        let err = if self.displayed.insert(key) {
            self.display_error(krate, span, level, msg.to_string(), rendered)
        } else {
            Error::new(span, msg.to_string())
        };
        self.error_count += 1;
        if let Some(id) = self.def_id
            && self.items_with_errors.insert(id)
            && !self.def_id_is_local
        {
            // If this item comes from an external crate, after the first error for that item
            // we display where in the local crate that item was reached from.
            self.report_external_dep_error(krate, id);
        }
        if !self.continue_on_failure() {
            panic!("{msg}");
        }
        err
    }

    /// Register the fact that `id` is a dependency of `src` (if `src` is not `None`).
    pub fn register_dep_source(
        &mut self,
        src: &Option<DepSource>,
        item_id: ItemId,
        is_local: bool,
    ) {
        if let Some(src) = src
            && src.src_id != item_id
            && !is_local
        {
            let tgt_node = match src.span {
                Some(span) => DepNode::Local(src.src_id, span),
                None => DepNode::External(src.src_id),
            };
            self.external_dep_graph.insert_edge(item_id, tgt_node)
        }
    }

    /// In case errors happened when extracting the definitions coming from the external
    /// dependencies, print a detailed report to explain to the user which dependencies were
    /// problematic, and where they are used in the code.
    pub fn report_external_dep_error(&self, krate: &TranslatedCrate, id: ItemId) {
        use annotate_snippets::*;

        // Use `Dijkstra's` algorithm to find the local items reachable from the current non-local
        // item.
        let graph = self.external_dep_graph.graph();
        let reachable = dijkstra(&graph, DepNode::External(id), None, |_| 1);
        trace!("id: {:?}\nreachable:\n{:?}", id, reachable);

        // Collect reachable local spans.
        let by_file: std::collections::HashMap<FileId, Vec<Span>> = reachable
            .iter()
            .filter_map(|(n, _)| match n {
                DepNode::External(_) => None,
                DepNode::Local(_, span) => Some(*span),
            })
            .into_group_map_by(|span| span.data().file_id);

        // Collect to a `Vec` to be able to sort it and to borrow `origin` (needed by
        // `Snippet::source`).
        let mut by_file: Vec<(FileId, _, _, Vec<Span>)> = by_file
            .into_iter()
            .filter_map(|(file_id, mut spans)| {
                spans.sort(); // Sort spans to display in file order
                let file = krate.files.get(file_id)?;
                let source = file.contents.as_ref()?;
                let file_name = file.name.to_string();
                Some((file_id, file_name, source, spans))
            })
            .collect();
        // Sort by file id to avoid output instability.
        by_file.sort_by_key(|(file_id, ..)| *file_id);

        let level = Level::NOTE;
        let snippets =
            by_file.iter().map(|(_, origin, source, spans)| {
                Snippet::source(*source)
                    .path(origin)
                    .fold(true)
                    .annotations(spans.iter().map(|span| {
                        AnnotationKind::Context.span(span.data().to_byte_range(source))
                    }))
            });

        let msg = format!(
            "the error occurred when translating `{}`, \
             which is (transitively) used at the following location(s):",
            id.with_ctx(&krate.into_fmt())
        );
        let message = Group::with_title(level.primary_title(&msg)).elements(snippets);
        let out = Renderer::styled().render(&[message]).to_string();
        self.emit(out);
    }
}
