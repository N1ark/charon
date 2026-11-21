//! ULLBC to LLBC
//!
//! We reconstruct the control-flow in the Unstructured LLBC.
//!
//! The reconstruction algorithm is not written to be efficient (its complexity
//! is probably very bad), but it was not written to be: this is still an early
//! stage and we want the algorithm to generate the best reconstruction as
//! possible. We still need to test the algorithm on more interesting examples,
//! and will consider making it more efficient once it is a bit mature and well
//! tested.
//! Also note that we more importantly focus on making the algorithm sound: the
//! reconstructed program must always be equivalent to the original MIR program,
//! and the fact that the reconstruction preserves this property must be obvious.
use fixedbitset::FixedBitSet;
use itertools::Itertools;
use petgraph::algo::dominators::{Dominators, simple_fast};
use petgraph::graphmap::DiGraphMap;
use petgraph::visit::{Dfs, DfsPostOrder, EdgeFiltered, EdgeRef, Walker};
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use smallvec::SmallVec;
use std::cmp::Reverse;
use std::mem;

use crate::ids::IndexVec;
use crate::llbc_ast as tgt;
use crate::transform::TransformCtx;
use crate::transform::ctx::LlbcPass;
use crate::ullbc_ast::{self as src, BlockId};
use crate::utils::{DfsWithPath, ensure_sufficient_stack};
use crate::{ast::*, register_error};

/// Control-Flow Graph
type Cfg = DiGraphMap<src::BlockId, (), rustc_hash::FxBuildHasher>;

/// Information precomputed about a function's CFG.
#[derive(Debug)]
struct CfgInfo {
    /// The CFG
    pub cfg: Cfg,
    /// The CFG where all the backward edges have been removed. Aka "forward CFG".
    pub fwd_cfg: Cfg,
    /// We consider the destination of the backward edges to be loop entries and
    /// store them here.
    pub loop_entries: HashSet<src::BlockId>,
    /// The blocks whose terminators are a switch are stored here.
    pub switch_blocks: HashSet<src::BlockId>,
    /// Tree of which nodes dominates which other nodes.
    #[expect(unused)]
    pub dominator_tree: Dominators<BlockId>,
    /// Computed data about each block.
    pub block_data: IndexVec<BlockId, Box<BlockData>>,
}

#[derive(Debug)]
struct BlockData {
    pub span: Span,
    /// The (unique) entrypoints of each loop. Unique because we error on irreducible cfgs.
    pub is_loop_header: bool,
    /// Whether this block is only reachable by taking an unwind edge.
    pub is_unwind: bool,
    /// Whether this block does nothing but return (and possibly deallocate locals).
    pub is_return: bool,
    /// Whether this block has multiple incoming control-flow edges in the forward graph.
    pub is_merge_target: bool,
    /// Order in a reverse postorder numbering. `None` if the block is unreachable.
    pub reverse_postorder: Option<u32>,
    /// Nodes that this block immediately dominates. Sorted by reverse_postorder_id, with largest
    /// id first.
    pub immediately_dominates: SmallVec<[BlockId; 2]>,
    /// The nodes from `immediately_dominates` that are also merge targets. Sorted in the same
    /// order.
    pub immediately_dominated_merge_targets: SmallVec<[BlockId; 2]>,
    /// List of loops inside of which this node is (loops are identified by their header). A node
    /// is considered inside a loop if it is reachable from the loop header and if it can reach the
    /// loop header using only the backwards edges into it (i.e. we don't count a path that enters
    /// the loop header through a forward edge).
    ///
    /// Note that we might have to take a backward edge to reach the loop header, e.g.:
    ///   'a: loop {
    ///       // ...
    ///       'b: loop {
    ///           // ...
    ///           if true {
    ///               continue 'a;
    ///           } else {
    ///               if true {
    ///                   break 'a;
    ///               }
    ///               // This node has to take two backward edges in order to reach the start of `'a`.
    ///           }
    ///       }
    ///   }
    ///
    /// The restriction on backwards edges is for the following case:
    ///   loop {
    ///     loop {
    ///       ..
    ///     }
    ///     // Not in inner loop
    ///   }
    ///
    /// This is sorted by path order from the graph root.
    pub within_loops: SmallVec<[BlockId; 2]>,
    /// Node from where we can only reach error nodes (panic, etc.)
    // TODO: track more nicely the set of targets reachable from a node: panic, return, exit loop,
    // continue loop (this is a partial order).
    pub only_reach_error: bool,
    /// Whether a switch is reachable from this node (including itself) in the forward graph.
    pub reaches_switch: bool,
    /// Whether this node is translated once into a cleanup block of the body, that the unwind
    /// paths that reach it continue with.
    pub is_shared_cleanup: bool,
    /// The nodes reachable from this node in the forward graph, including itself.
    pub reachable: FixedBitSet,
    /// Reconstructed information about loops and switches.
    pub exit_info: ExitInfo,
}

#[derive(Debug, Default, Clone)]
struct ExitInfo {
    /// The loop exit
    loop_exit: Option<src::BlockId>,
    /// The switch exit.
    switch_exit: Option<src::BlockId>,
}

/// Error indicating that the control-flow graph is not reducible. The contained block id is a
/// block involved in an irreducible subgraph.
struct Irreducible(BlockId);

impl BlockData {
    fn new(data: &ullbc_ast::BlockData) -> Self {
        Self {
            span: data.terminator.span,
            is_loop_header: false,
            is_unwind: false,
            is_return: data.is_trivial_return(),
            is_merge_target: false,
            reverse_postorder: None,
            immediately_dominates: Default::default(),
            immediately_dominated_merge_targets: Default::default(),
            within_loops: Default::default(),
            only_reach_error: false,
            reaches_switch: false,
            is_shared_cleanup: false,
            reachable: Default::default(),
            exit_info: Default::default(),
        }
    }
}

impl CfgInfo {
    /// Build the CFGs (the "regular" CFG and the CFG without backward edges) and precompute a
    /// bunch of graph information about the CFG.
    fn build(ctx: &TransformCtx, body: &src::BodyContents) -> Result<Self, Irreducible> {
        // The steps in this function follow a precise order, as each step typically requires the
        // previous one.
        let start_block = BlockId::ZERO;

        let mut block_data: IndexVec<BlockId, _> =
            body.map_ref(|contents| Box::new(BlockData::new(contents)));

        // Build the node graph.
        let mut cfg = Cfg::new();
        let mut cfg_without_unwind = Cfg::new();
        for (block_id, block) in body.iter_enumerated() {
            cfg.add_node(block_id);
            cfg_without_unwind.add_node(block_id);
            for tgt in block.targets() {
                cfg.add_edge(block_id, tgt, ());
            }
            for tgt in block.targets_ignoring_unwind() {
                cfg_without_unwind.add_edge(block_id, tgt, ());
            }
        }

        // Compute the dominator tree.
        let dominator_tree = simple_fast(&cfg, start_block);

        // Compute reverse postorder numbering.
        for (i, block_id) in DfsPostOrder::new(&cfg, start_block).iter(&cfg).enumerate() {
            let rev_post_id = body.len() - i;
            block_data[block_id].reverse_postorder = Some(rev_post_id.try_into().unwrap());

            // Store the dominator tree in `block_data`.
            if let Some(dominator) = dominator_tree.immediate_dominator(block_id) {
                block_data[dominator].immediately_dominates.push(block_id);
            }
        }

        // Compute the forward graph (without backward edges).
        let mut fwd_cfg = Cfg::new();
        let mut loop_entries = HashSet::default();
        let mut switch_blocks = HashSet::default();
        for block_id in Dfs::new(&cfg, start_block).iter(&cfg) {
            fwd_cfg.add_node(block_id);

            if body[block_id].terminator.kind.is_switch() {
                switch_blocks.insert(block_id);
            }

            // Iterate over edges into this node (so that we can determine whether this node is a
            // loop header).
            let mut incoming_fwd_edges = 0;
            for from in cfg.neighbors_directed(block_id, petgraph::Direction::Incoming) {
                // Check if the edge is a backward edge.
                if block_data[from].reverse_postorder >= block_data[block_id].reverse_postorder {
                    // This is a backward edge
                    block_data[block_id].is_loop_header = true;
                    loop_entries.insert(block_id);
                    // A cfg is reducible iff the target of every back edge dominates the
                    // edge's source.
                    if !dominator_tree.dominators(from).unwrap().contains(&block_id) {
                        return Err(Irreducible(from));
                    }
                } else {
                    incoming_fwd_edges += 1;
                    fwd_cfg.add_edge(from, block_id, ());
                }
            }

            // Detect merge targets.
            if incoming_fwd_edges >= 2 {
                block_data[block_id].is_merge_target = true;
            }
        }

        let reachable_without_unwind: HashSet<BlockId> = Dfs::new(&cfg_without_unwind, start_block)
            .iter(&cfg_without_unwind)
            .collect();

        // Finish filling in information.
        for block_id in DfsPostOrder::new(&fwd_cfg, start_block).iter(&fwd_cfg) {
            let block = &body[block_id];
            let targets = cfg.neighbors(block_id).collect_vec();
            let fwd_targets = fwd_cfg.neighbors(block_id).collect_vec();

            // Compute the nodes that are part of unwind paths.
            block_data[block_id].is_unwind = !reachable_without_unwind.contains(&block_id);

            // Compute the nodes that can only reach error nodes.
            // The node can only reach error nodes if:
            // - it is an error node;
            // - or it has neighbors and they all lead to errors.
            // Note that if there is a backward edge, `only_reach_error` cannot contain this
            // node yet. In other words, this does not consider infinite loops as reaching an
            // error node.
            if block.terminator.is_error()
                || (!targets.is_empty()
                    && targets.iter().all(|&tgt| block_data[tgt].only_reach_error))
            {
                block_data[block_id].only_reach_error = true;
            }

            block_data[block_id].reaches_switch = switch_blocks.contains(&block_id)
                || fwd_targets
                    .iter()
                    .any(|&tgt| block_data[tgt].reaches_switch);

            let mut reachable = FixedBitSet::with_capacity(body.len());
            reachable.insert(block_id.index());
            for &tgt in &fwd_targets {
                reachable.union_with(&block_data[tgt].reachable);
            }
            block_data[block_id].reachable = reachable;

            // Fill in the rest of the domination data.
            let mut dominatees = mem::take(&mut block_data[block_id].immediately_dominates);
            dominatees.sort_by_key(|&child| block_data[child].reverse_postorder);
            dominatees.reverse();
            block_data[block_id].immediately_dominates = dominatees;
            block_data[block_id].immediately_dominated_merge_targets = block_data[block_id]
                .immediately_dominates
                .iter()
                .copied()
                .filter(|&child| block_data[child].is_merge_target)
                .collect();
        }

        // Fill in the within_loop information. See the docs of `within_loops` to understand what
        // we're computing.
        let mut path_dfs = DfsWithPath::new(&cfg, start_block);
        while let Some(block_id) = path_dfs.next(&cfg) {
            // Store all the loops on the path to this
            // node.
            let mut within_loops: SmallVec<_> = path_dfs
                .path
                .iter()
                .copied()
                .filter(|&loop_id| block_data[loop_id].is_loop_header)
                .collect();
            // The loops that we can reach by taking a single backward edge.
            let loops_directly_within = within_loops
                .iter()
                .copied()
                .filter(|&loop_header| {
                    cfg.neighbors_directed(loop_header, petgraph::Direction::Incoming)
                        .any(|bid| block_data[block_id].reachable.contains(bid.index()))
                })
                .collect_vec();
            // The loops that we can reach by taking any number of backward edges.
            let loops_indirectly_within: HashSet<_> = loops_directly_within
                .iter()
                .copied()
                .flat_map(|loop_header| &block_data[loop_header].within_loops)
                .chain(&loops_directly_within)
                .copied()
                .collect();
            within_loops.retain(|id| loops_indirectly_within.contains(id));
            block_data[block_id].within_loops = within_loops;
        }

        // Several unwind paths may continue with the same unwind node: we translate it once into a
        // cleanup block of the body, unless it does nothing but end unwinding.
        let mut incoming_edges = body.map_ref(|_| 0usize);
        for block in body {
            for tgt in block.targets() {
                incoming_edges[tgt] += 1;
            }
        }
        for (block_id, block) in body.iter_enumerated() {
            let data = &mut block_data[block_id];
            let is_lone_terminator = block.statements.is_empty()
                && matches!(
                    block.terminator.kind,
                    src::TerminatorKind::UnwindResume
                        | src::TerminatorKind::UnwindTerminate(..)
                        | src::TerminatorKind::UndefinedBehavior
                );
            data.is_shared_cleanup = data.is_unwind
                && incoming_edges[block_id] >= 2
                && !is_lone_terminator
                && !data.is_loop_header
                && data.within_loops.is_empty();
        }

        let mut cfg = CfgInfo {
            cfg,
            fwd_cfg,
            loop_entries,
            switch_blocks,
            dominator_tree,
            block_data,
        };

        // Pick an exit block for each loop, if we find one.
        ExitInfo::compute_loop_exits(ctx, &mut cfg);

        // Pick an exit block for each switch, if we find one.
        ExitInfo::compute_switch_exits(&mut cfg, body);

        Ok(cfg)
    }

    fn block_data(&self, block_id: BlockId) -> &BlockData {
        &self.block_data[block_id]
    }
    fn can_reach(&self, src: BlockId, tgt: BlockId) -> bool {
        self.block_data[src].reachable.contains(tgt.index())
    }
    fn topo_rank(&self, block_id: BlockId) -> u32 {
        self.block_data[block_id].reverse_postorder.unwrap()
    }
    #[expect(unused)]
    fn is_backward_edge(&self, src: BlockId, tgt: BlockId) -> bool {
        self.block_data[src].reverse_postorder >= self.block_data[tgt].reverse_postorder
            && self.cfg.contains_edge(src, tgt)
    }

    /// Check if the node is within the given loop.
    fn is_within_loop(&self, loop_header: src::BlockId, block_id: src::BlockId) -> bool {
        self.block_data[block_id]
            .within_loops
            .contains(&loop_header)
    }

    /// Check if all paths from `src` to nodes in `target_set` go through `through_node`. If `src`
    /// is already in `target_set`, we ignore that empty path.
    fn all_paths_go_through(
        &self,
        src: src::BlockId,
        through_node: src::BlockId,
        target_set: &HashSet<src::BlockId>,
    ) -> bool {
        let graph = EdgeFiltered::from_fn(&self.fwd_cfg, |edge| edge.source() != through_node);
        !Dfs::new(&graph, src)
            .iter(&graph)
            .skip(1) // skip src
            .any(|bid| target_set.contains(&bid))
    }
}

impl BlockData {
    fn reachable_including_self(&self) -> impl Iterator<Item = BlockId> {
        self.reachable.ones().map(BlockId::new)
    }
}

/// See [`ExitInfo::compute_loop_exit_ranks`].
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct LoopExitRank {
    /// Whether this exit can reach a switch.
    continues: bool,
    /// Number of paths we found going to this exit.
    path_count: usize,
    /// Distance from the loop header.
    distance_from_header: Reverse<usize>,
}

impl ExitInfo {
    /// Compute the first node on each path that exits the loop.
    fn compute_loop_exit_starting_points(
        cfg: &CfgInfo,
        loop_header: src::BlockId,
    ) -> Vec<src::BlockId> {
        let mut loop_exits = Vec::new();
        // Do a dfs from the loop header while keeping track of the path from the loop header to
        // the current node.
        let mut dfs = Dfs::new(&cfg.fwd_cfg, loop_header);
        while let Some(block_id) = dfs.next(&cfg.fwd_cfg) {
            // If we've exited all the loops after and including the target one, this node is an
            // exit node for the target loop.
            if !cfg.is_within_loop(loop_header, block_id) {
                loop_exits.push(block_id);
                // Don't explore any more paths from this node.
                dfs.discovered.extend(cfg.fwd_cfg.neighbors(block_id));
            }
        }
        loop_exits
    }

    /// Compute the loop exit candidates along with a rank.
    ///
    /// In the simple case, there is one exit node through which all exit paths go. We want to be
    /// sure to catch that case, and when that's not possible we want to still find a node through
    /// which a lot of exit paths go.
    ///
    /// To do that, we first count for each exit node how many exit paths go through it. We pick a
    /// node that can reach a switch over exit code (straight-line code to a return), then the node
    /// with most occurrences. If there are many such nodes, we pick the one with shortest distance
    /// from the loop header. Finally if there are still many such nodes, we keep the
    /// first node found (the order in which we explore the graph is deterministic, and we use an
    /// insertion-order hash map).
    ///
    /// Note that exit candidates will typically be referenced more than once for one loop. This
    /// comes from the fact that whenever we reach a node outside the current loop, we register
    /// this node as well as all its children as exit candidates.
    /// Consider the following example:
    /// ```text
    /// while i < max {
    ///     if cond {
    ///         break;
    ///     }
    ///     s += i;
    ///     i += 1
    /// }
    /// // All the below nodes are exit candidates (each of them is referenced twice)
    /// s += 1;
    /// return s;
    /// ```
    fn compute_loop_exit_ranks(
        cfg: &CfgInfo,
        loop_header: src::BlockId,
    ) -> SeqHashMap<src::BlockId, LoopExitRank> {
        let mut loop_exits: SeqHashMap<BlockId, LoopExitRank> = SeqHashMap::default();
        let header_is_unwind = cfg.block_data[loop_header].is_unwind;
        // The length of the shortest path from the loop header to each node of the forward graph.
        let mut distance_from_header = cfg.block_data.map_ref(|_| usize::MAX);
        distance_from_header[loop_header] = 0;
        let mut queue = std::collections::VecDeque::from([loop_header]);
        while let Some(bid) = queue.pop_front() {
            for tgt in cfg.fwd_cfg.neighbors(bid) {
                if distance_from_header[tgt] == usize::MAX {
                    distance_from_header[tgt] = distance_from_header[bid] + 1;
                    queue.push_back(tgt);
                }
            }
        }
        for block_id in Self::compute_loop_exit_starting_points(cfg, loop_header) {
            for bid in cfg.block_data(block_id).reachable_including_self() {
                let block_data = &cfg.block_data[bid];
                // We want to force duplication of return-only blocks, so we only count them for the
                // paths that jump to them directly.
                if block_data.is_return && bid != block_id {
                    continue;
                }
                // Unwind paths are translated inside the `on_unwind` block of the statement that
                // unwinds, so we can't `break` to them from a regular loop.
                if block_data.is_unwind && !header_is_unwind {
                    continue;
                }
                loop_exits
                    .entry(bid)
                    .or_insert_with(|| LoopExitRank {
                        continues: block_data.reaches_switch,
                        path_count: 0,
                        distance_from_header: Reverse(distance_from_header[bid]),
                    })
                    .path_count += 1;
            }
        }
        loop_exits
    }

    /// A loop exit is any block reachable from the loop header that isn't inside the loop.
    /// This function choses an exit for every loop. See `compute_loop_exit_ranks` for how we
    /// select them.
    ///
    /// For example:
    /// ```text
    /// while ... {
    ///    ...
    ///    if ... {
    ///        // We can't reach the loop entry from here: this is an exit
    ///        // candidate
    ///        return;
    ///    }
    /// }
    /// // This is another exit candidate - and this is the one we want to use
    /// // as the "real" exit...
    /// ...
    /// ```
    ///
    /// Once we listed all the exit candidates, we find the "best" one for every loop. The best
    /// exit is the following one:
    /// - it is the one which is used the most times (note that there can be
    ///   several candidates which are referenced strictly more than once: see the
    ///   comment below)
    /// - if several exits have the same number of occurrences, we choose the one
    ///   for which we goto the "earliest" (earliest meaning that the goto is close to
    ///   the loop entry node in the AST). The reason is that all the loops should
    ///   have an outer if ... then ... else ... which executes the loop body or goes
    ///   to the exit (note that this is not necessarily the first
    ///   if ... then ... else ... we find: loop conditions can be arbitrary
    ///   expressions, containing branchings).
    ///
    /// # Several candidates for a loop exit:
    /// =====================================
    /// There used to be a sanity check to ensure there are no two different
    /// candidates with exactly the same number of occurrences and distance from
    /// the entry of the loop, if the number of occurrences is > 1.
    ///
    /// We removed it because it does happen, for instance here (the match
    /// introduces an `unreachable` node, and it has the same number of
    /// occurrences and the same distance to the loop entry as the `panic`
    /// node):
    ///
    /// ```text
    /// pub fn list_nth_mut_loop_pair<'a, T>(
    ///     mut ls: &'a mut List<T>,
    ///     mut i: u32,
    /// ) -> &'a mut T {
    ///     loop {
    ///         match ls {
    ///             List::Nil => {
    ///                 panic!() // <-- best candidate
    ///             }
    ///             List::Cons(x, tl) => {
    ///                 if i == 0 {
    ///                     return x;
    ///                 } else {
    ///                     ls = tl;
    ///                     i -= 1;
    ///                 }
    ///             }
    ///             _ => {
    ///               // Note that Rustc always introduces an unreachable branch after
    ///               // desugaring matches.
    ///               unreachable!(), // <-- best candidate
    ///             }
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// When this happens we choose an exit candidate whose edges don't necessarily
    /// lead to an error (above there are none, so we don't choose any exits). Note
    /// that this last condition is important to prevent loops from being unnecessarily
    /// nested:
    ///
    /// ```text
    /// pub fn nested_loops_enum(step_out: usize, step_in: usize) -> usize {
    ///     let mut s = 0;
    ///
    ///     for _ in 0..128 { // We don't want this loop to be nested with the loops below
    ///         s += 1;
    ///     }
    ///
    ///     for _ in 0..(step_out) {
    ///         for _ in 0..(step_in) {
    ///             s += 1;
    ///         }
    ///     }
    ///
    ///     s
    /// }
    /// ```
    fn compute_loop_exits(_ctx: &TransformCtx, cfg: &mut CfgInfo) {
        for &loop_id in &cfg.loop_entries {
            // Compute the candidates.
            let loop_exits: SeqHashMap<BlockId, LoopExitRank> =
                Self::compute_loop_exit_ranks(cfg, loop_id);
            // We choose the exit that:
            // - can reach a switch
            // - has the most occurrences
            // - the least total distance (if there are several possibilities)
            // - doesn't necessarily lead to an error (panic, unreachable)
            let best_exits: Vec<(BlockId, LoopExitRank)> =
                loop_exits.into_iter().max_set_by_key(|&(_, rank)| rank);
            // If there is exactly one best candidate, use it. Otherwise we need to split further.
            let chosen_exit = match best_exits.into_iter().map(|(bid, _)| bid).exactly_one() {
                Ok(best_exit) => Some(best_exit),
                Err(best_exits) => {
                    // Remove the candidates which only lead to errors (panic or unreachable).
                    // If there is exactly one candidate we select it, otherwise we do not select any
                    // exit.
                    // We don't want to select any exit if we are in the below situation
                    // (all paths lead to errors). We added a sanity check below to
                    // catch the situations where there are several exits which don't
                    // lead to errors.
                    //
                    // Example:
                    // ========
                    // ```
                    // loop {
                    //     match ls {
                    //         List::Nil => {
                    //             panic!() // <-- best candidate
                    //         }
                    //         List::Cons(x, tl) => {
                    //             if i == 0 {
                    //                 return x;
                    //             } else {
                    //                 ls = tl;
                    //                 i -= 1;
                    //             }
                    //         }
                    //         _ => {
                    //           unreachable!(); // <-- best candidate (Rustc introduces an `unreachable` case)
                    //         }
                    //     }
                    // }
                    // ```
                    // The `exactly_one` can fail, see `tests/ui/control-flow/ambiguous-loop-exit.rs`
                    best_exits
                        .filter(|&bid| !cfg.block_data[bid].only_reach_error)
                        .exactly_one()
                        .ok()
                }
            };
            cfg.block_data[loop_id].exit_info.loop_exit = chosen_exit;
        }
    }

    /// The exit of a switch is the block where the code that follows the switch starts: we
    /// translate it after the switch, and the branches that reach it end there. The candidates are
    /// the blocks that the switch immediately dominates and that several of its branches reach, in
    /// the innermost loop of the switch and outside unwind paths (unless the switch is in one).
    /// Exit code is code that can't reach a switch of that loop, e.g. straight-line code to a
    /// return or to the loop header. The blocks a candidate bypasses are the blocks after it that
    /// a branch reaches without going through it. The exit is the first candidate in this order:
    /// - candidates that aren't exit code;
    /// - candidates such that no bypassed block outside exit code is a merge of bypassed blocks;
    /// - candidates that every path from the switch goes through before leaving the loop;
    /// - the nearest candidate.
    ///
    /// Without a candidate, if all the branches but one are exit code, the exit is the target of
    /// that branch. Outer switches choose first, and a switch can't take an exit taken by an outer
    /// switch, nor one that a branch bypasses to reach an outer exit.
    fn compute_switch_exits(cfg: &mut CfgInfo, body: &src::BodyContents) {
        let mut exits_set = HashSet::default();
        // The exits that lead to more branching, see below.
        let mut branching_exits = HashSet::default();
        for bid in cfg
            .switch_blocks
            .iter()
            .copied()
            .sorted_unstable_by_key(|&bid| (cfg.topo_rank(bid), bid))
        {
            let block_data = &cfg.block_data[bid];
            let current_loop = block_data.within_loops.last().copied();
            let in_region = |b: BlockId| {
                current_loop.is_none_or(|l| cfg.is_within_loop(l, b))
                    && (block_data.is_unwind || !cfg.block_data[b].is_unwind)
            };
            let mut region_switches = FixedBitSet::with_capacity(body.len());
            for &s in &cfg.switch_blocks {
                if in_region(s) {
                    region_switches.insert(s.index());
                }
            }
            let is_exit_code =
                |b: BlockId| cfg.block_data[b].reachable.is_disjoint(&region_switches);
            let branches = body[bid]
                .targets()
                .into_iter()
                .filter(|&tgt| cfg.fwd_cfg.contains_edge(bid, tgt))
                .collect_vec();
            // Whether the block is reachable from several branches.
            let is_merge = |id: BlockId| {
                branches
                    .iter()
                    .filter(|&&branch| cfg.can_reach(branch, id))
                    .count()
                    >= 2
            };
            let is_candidate =
                |b: BlockId| in_region(b) && !cfg.block_data[b].is_return && is_merge(b);
            let rank = |exit_id: BlockId| {
                let graph = EdgeFiltered::from_fn(&cfg.fwd_cfg, |edge| {
                    edge.target() != exit_id && in_region(edge.target())
                });
                // The blocks that a branch reaches without going through `exit_id`.
                let mut avoiding_exit = FixedBitSet::with_capacity(body.len());
                for &branch in &branches {
                    if branch != exit_id && in_region(branch) {
                        let mut dfs = Dfs::new(&graph, branch);
                        while let Some(b) = dfs.next(&graph) {
                            avoiding_exit.insert(b.index());
                        }
                    }
                }
                let bypassed = &avoiding_exit & &cfg.block_data[exit_id].reachable;
                let bypasses_merge = bypassed.ones().map(BlockId::new).any(|b| {
                    cfg.block_data[b].is_merge_target
                        && !is_exit_code(b)
                        && cfg
                            .fwd_cfg
                            .neighbors_directed(b, petgraph::Direction::Incoming)
                            .all(|pred| bypassed.contains(pred.index()))
                });
                let post_dominates = avoiding_exit.ones().map(BlockId::new).all(|b| {
                    let mut succs = cfg
                        .fwd_cfg
                        .neighbors(b)
                        .filter(|&s| block_data.is_unwind || !cfg.block_data[s].is_unwind)
                        .peekable();
                    !cfg.block_data[b].is_return
                        && succs.peek().is_some()
                        && succs.all(|s| s == exit_id || in_region(s))
                });
                (
                    is_exit_code(exit_id),
                    bypasses_merge,
                    !post_dominates,
                    cfg.topo_rank(exit_id),
                )
            };
            let merge_exit = block_data
                .immediately_dominates
                .iter()
                .copied()
                .filter(|&b| is_candidate(b))
                .min_by_key(|&b| rank(b));
            let continuing_branch = || {
                branches
                    .iter()
                    .copied()
                    .filter(|&b| in_region(b) && !cfg.block_data[b].is_return && !is_exit_code(b))
                    .exactly_one()
                    .ok()
            };
            let Some(exit_id) = merge_exit.or_else(continuing_branch) else {
                continue;
            };
            // A jump to an outer exit that is straight-line code is translated by inlining that
            // code, so a branching exit may be bypassed to reach such an outer exit.
            let outer_exits = if cfg.block_data[exit_id].reaches_switch && is_merge(exit_id) {
                &branching_exits
            } else {
                &exits_set
            };
            if exits_set.contains(&exit_id) || !cfg.all_paths_go_through(bid, exit_id, outer_exits)
            {
                continue;
            }
            exits_set.insert(exit_id);
            if cfg.block_data[exit_id].reaches_switch {
                branching_exits.insert(exit_id);
            }
            // The switch of a loop header only uses its exit if its branches merge there, so
            // that e.g. the body of a `while` loop stays inside the `if`.
            if !block_data.is_loop_header || is_merge(exit_id) {
                cfg.block_data[bid].exit_info.switch_exit = Some(exit_id);
            }
        }
    }
}

/// Iter over the last non-switch statements that may be executed on any branch of this block.
/// Skips over `Nop`s.
fn iter_tail_statements(block: &mut tgt::Block, f: &mut impl FnMut(&mut tgt::Statement)) {
    let Some(st) = block
        .statements
        .iter_mut()
        .rev()
        .find(|st| !st.kind.is_nop())
    else {
        return;
    };
    if let tgt::StatementKind::Switch { branches, .. } = &mut st.kind {
        for block in branches {
            iter_tail_statements(block, f);
        }
    } else {
        f(st)
    };
}

type Depth = usize;

#[derive(Debug, Copy, Clone)]
enum SpecialJumpKind {
    /// This block can be reached by a `continue` to the given depth.
    LoopContinue(Depth),
    /// This block can be reached by a `break` to the given depth. This comes from a loop.
    LoopBreak(Depth),
    /// This block can be reached by a `break` to the given depth. This is a `loop` context
    /// introduced only for forward jumps.
    ForwardBreak(Depth),
    /// This block can be reached by doing nothing as this is the next block that will be
    /// translated. Only applies if this block is at the top of the stack.
    NextBlock,
}

#[derive(Copy, Clone)]
struct SpecialJump {
    /// The relevant block.
    target_block: BlockId,
    /// How to translate a jump to the target block.
    kind: SpecialJumpKind,
}

impl SpecialJump {
    fn new(target_block: BlockId, kind: SpecialJumpKind) -> Self {
        Self { target_block, kind }
    }
}

impl std::fmt::Debug for SpecialJump {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SpecialJump({}, {:?})", self.target_block, self.kind)
    }
}

/// What comes after the translation of a terminator.
enum Next {
    /// The translation continues with this block.
    Jump(BlockId),
    /// The translation continues with this block, after the assert statement the terminator
    /// translated to.
    AssertJump(BlockId),
    /// The translation is complete.
    Done(tgt::Block),
}

/// How to handle blocks reachable from multiple branches.
enum ReconstructMode {
    /// Duplicate blocks reachable from multiple branches.
    Duplicate,
    /// Insert loops for the purpose of breaking forward to them to implement DAG-like control-flow
    /// without duplicating blocks.
    /// Based on the algorithm from "Beyond Relooper" (https://dl.acm.org/doi/10.1145/3547621).
    ForwardBreak,
}

struct ReconstructCtx<'a> {
    cfg: CfgInfo,
    body: &'a src::ExprBody,
    /// The depth of `loop` contexts we may `break`/`continue` to.
    break_context_depth: Depth,
    /// Stack of block ids that should be translated to special jumps (`break`/`continue`/do
    /// nothing) in the current context.
    /// The block where control-flow continues naturally after this block is kept at the top of the
    /// stack.
    special_jump_stack: Vec<SpecialJump>,
    mode: ReconstructMode,
    /// The ids of the cleanup blocks we jumped to so far.
    cleanup_ids: HashMap<BlockId, tgt::CleanupId>,
    /// The nodes to translate into cleanup blocks, by cleanup id.
    cleanups: IndexVec<tgt::CleanupId, BlockId>,
}

impl<'a> ReconstructCtx<'a> {
    fn build(ctx: &TransformCtx, src_body: &'a src::ExprBody) -> Result<Self, Irreducible> {
        // Compute all sorts of graph-related information about the control-flow graph, including
        // reachability, the dominator tree, loop entries, and loop/switch exits.
        let cfg = CfgInfo::build(ctx, &src_body.body)?;

        // Translate the body by reconstructing the loops and the
        // conditional branchings.
        let allow_duplication = !ctx.options.no_code_duplication;
        Ok(ReconstructCtx {
            cfg,
            body: src_body,
            break_context_depth: 0,
            special_jump_stack: Vec::new(),
            mode: if allow_duplication {
                ReconstructMode::Duplicate
            } else {
                ReconstructMode::ForwardBreak
            },
            cleanup_ids: HashMap::default(),
            cleanups: IndexVec::new(),
        })
    }

    fn translate_statement(&self, st: &src::Statement) -> tgt::Statement {
        let span = st.span;
        let kind = match st.kind.clone() {
            src::StatementKind::Assign(assign) => {
                let (place, rvalue) = *assign;
                tgt::StatementKind::Assign(place, Box::new(rvalue))
            }
            src::StatementKind::SetDiscriminant(set_discr) => {
                let (place, variant_id) = *set_discr;
                tgt::StatementKind::SetDiscriminant(place, variant_id)
            }
            src::StatementKind::StorageLive(var_id) => tgt::StatementKind::StorageLive(var_id),
            src::StatementKind::StorageDead(var_id) => tgt::StatementKind::StorageDead(var_id),
            src::StatementKind::Assert { assert, on_failure } => tgt::StatementKind::Assert {
                assert,
                on_failure: on_failure.clone(),
                on_unwind: Box::new(
                    tgt::Statement::new(span, tgt::StatementKind::UnwindResume).into_block(),
                ),
            },
            src::StatementKind::PlaceMention(place) => tgt::StatementKind::PlaceMention(*place),
            src::StatementKind::Borrowck(statement) => tgt::StatementKind::Borrowck(statement),
            src::StatementKind::Nop => tgt::StatementKind::Nop,
        };
        let mut translated = tgt::Statement::new(span, kind);
        translated.comments_before = st.comments_before.clone();
        translated
    }

    /// Translate a jump to the given block. The span is used to create the jump statement, if any.
    #[tracing::instrument(skip(self), ret, fields(stack = ?self.special_jump_stack))]
    fn translate_jump(&mut self, span: Span, target_block: src::BlockId) -> tgt::Block {
        match self
            .special_jump_stack
            .iter()
            .rev()
            .enumerate()
            .find(|(_, j)| j.target_block == target_block)
        {
            Some((i, jump_target)) => {
                let mk_block = |kind| tgt::Statement::new(span, kind).into_block();
                match jump_target.kind {
                    // The top of the stack is where control-flow goes naturally, no need to add a
                    // `break`/`continue`. We only do that in `ForwardBreak` mode to avoid breaking aeneas.
                    SpecialJumpKind::LoopContinue(_)
                    | SpecialJumpKind::ForwardBreak(_)
                    | SpecialJumpKind::NextBlock
                        if i == 0 && matches!(self.mode, ReconstructMode::ForwardBreak) =>
                    {
                        mk_block(tgt::StatementKind::Nop)
                    }
                    SpecialJumpKind::LoopContinue(depth) => mk_block(tgt::StatementKind::Continue(
                        self.break_context_depth - depth,
                    )),
                    SpecialJumpKind::ForwardBreak(depth) | SpecialJumpKind::LoopBreak(depth) => {
                        mk_block(tgt::StatementKind::Break(self.break_context_depth - depth))
                    }
                    SpecialJumpKind::NextBlock if i == 0 => mk_block(tgt::StatementKind::Nop),
                    // Translate the block without a jump.
                    SpecialJumpKind::NextBlock => self.translate_block(target_block),
                }
            }
            None if self.cfg.block_data[target_block].is_shared_cleanup => {
                self.goto_cleanup(span, target_block)
            }
            // Translate the block without a jump.
            None => self.translate_block(target_block),
        }
    }

    /// Translate the unwind path that starts at the given node. The span is that of the
    /// terminator that unwinds.
    fn translate_unwind(&mut self, span: Span, block_id: src::BlockId) -> tgt::Block {
        if self.cfg.block_data[block_id].is_shared_cleanup {
            self.goto_cleanup(span, block_id)
        } else {
            self.translate_block(block_id)
        }
    }

    /// Jump to the cleanup block that the given node translates to.
    fn goto_cleanup(&mut self, span: Span, block_id: src::BlockId) -> tgt::Block {
        let id = *self
            .cleanup_ids
            .entry(block_id)
            .or_insert_with(|| self.cleanups.push(block_id));
        tgt::Statement::new(span, tgt::StatementKind::GotoCleanup(id)).into_block()
    }

    /// Translate a terminator. A terminator that continues to a single block after its own
    /// statement (if any) pushes that statement to `statements` and returns the block to continue
    /// with; we translate it in `translate_block_itself`.
    fn translate_terminator(
        &mut self,
        terminator: &src::Terminator,
        statements: &mut Vec<tgt::Statement>,
    ) -> Next {
        let src_span = terminator.span;
        let kind = match &terminator.kind {
            src::TerminatorKind::Goto { target } => return Next::Jump(*target),
            src::TerminatorKind::Call {
                call,
                dest,
                target,
                on_unwind,
            } => {
                let on_unwind = Box::new(self.translate_unwind(src_span, *on_unwind));
                statements.push(tgt::Statement::new(
                    src_span,
                    tgt::StatementKind::Call {
                        call: Box::new(call.clone()),
                        dest: Box::new(dest.clone()),
                        on_unwind,
                    },
                ));
                return Next::Jump(*target);
            }
            src::TerminatorKind::Drop {
                kind,
                place,
                fn_ptr,
                target,
                on_unwind,
            } => {
                let on_unwind = Box::new(self.translate_unwind(src_span, *on_unwind));
                statements.push(tgt::Statement::new(
                    src_span,
                    tgt::StatementKind::Drop {
                        place: Box::new(place.clone()),
                        fn_ptr: fn_ptr.clone(),
                        kind: *kind,
                        on_unwind,
                    },
                ));
                return Next::Jump(*target);
            }
            src::TerminatorKind::DropEmptyBox {
                place,
                target,
                on_unwind,
            } => {
                let on_unwind = Box::new(self.translate_unwind(src_span, *on_unwind));
                statements.push(tgt::Statement::new(
                    src_span,
                    tgt::StatementKind::DropEmptyBox {
                        place: place.clone(),
                        on_unwind,
                    },
                ));
                return Next::Jump(*target);
            }
            src::TerminatorKind::Assert {
                assert,
                target,
                on_unwind,
            } => {
                let on_unwind = Box::new(self.translate_unwind(src_span, *on_unwind));
                statements.push(tgt::Statement::new(
                    src_span,
                    tgt::StatementKind::Assert {
                        assert: Box::new(assert.clone()),
                        on_failure: AbortKind::Panic,
                        on_unwind,
                    },
                ));
                return Next::AssertJump(*target);
            }
            src::TerminatorKind::Panic { call, on_unwind } => {
                let on_unwind = Box::new(self.translate_unwind(src_span, *on_unwind));
                tgt::StatementKind::Panic {
                    call: Box::new(call.clone()),
                    on_unwind,
                }
            }
            src::TerminatorKind::UndefinedBehavior => tgt::StatementKind::UndefinedBehavior,
            src::TerminatorKind::UnwindTerminate(reason, fun_ref) => {
                tgt::StatementKind::UnwindTerminate(*reason, fun_ref.clone())
            }
            src::TerminatorKind::Return => tgt::StatementKind::Return,
            src::TerminatorKind::UnwindResume => tgt::StatementKind::UnwindResume,
            src::TerminatorKind::InlineAsm {
                asm,
                fallthrough,
                labels,
                on_unwind,
            } => {
                let fallthrough = fallthrough
                    .map(|target| Box::new(self.translate_jump(terminator.span, target)));
                let labels = Box::new(
                    labels.map_ref(|target| self.translate_jump(terminator.span, *target)),
                );
                let on_unwind = Box::new(self.translate_unwind(src_span, *on_unwind));
                tgt::StatementKind::InlineAsm {
                    asm: asm.clone(),
                    fallthrough,
                    labels,
                    on_unwind,
                }
            }
            src::TerminatorKind::Switch { data, branches } => {
                let branches =
                    branches.map_ref(|target| self.translate_jump(terminator.span, *target));
                let span = combine_span_iter(branches.iter().map(|branch| &branch.span));
                let span = combine_span(&src_span, &span);
                let st = tgt::StatementKind::Switch {
                    data: Box::new(data.clone()),
                    branches,
                };
                return Next::Done(tgt::Statement::new(span, st).into_block());
            }
        };
        Next::Done(tgt::Statement::new(src_span, kind).into_block())
    }

    /// Translate the block statements and terminator, followed by the blocks it continues to as
    /// long as they don't need surrounding control-flow. We iterate on those instead of recursing
    /// so that long straight-line code doesn't recurse deeply.
    fn translate_block_itself(&mut self, block_id: BlockId) -> tgt::Block {
        let body = self.body;
        let mut block_id = block_id;
        let mut statements = Vec::new();
        // The spans to combine with the span of the last block, from the innermost: the result
        // has the span of nesting the translated blocks like `{ statements; { assert; target } }`.
        let mut spans = Vec::new();
        let last_block = loop {
            let block = &body.body[block_id];
            let first = statements.len();
            statements.extend(
                block
                    .statements
                    .iter()
                    .map(|st| self.translate_statement(st)),
            );
            if statements.len() > first {
                spans.push(combine_span_iter(
                    statements[first..].iter().map(|st| &st.span),
                ));
            }
            let target = match self.translate_terminator(&block.terminator, &mut statements) {
                Next::Done(block) => break block,
                Next::Jump(target) => target,
                Next::AssertJump(target) => {
                    spans.push(statements.last().unwrap().span);
                    target
                }
            };
            let span = block.terminator.span;
            if self.cfg.block_data[target].is_shared_cleanup
                || self
                    .special_jump_stack
                    .iter()
                    .any(|jump| jump.target_block == target)
            {
                break self.translate_jump(span, target);
            }
            let old_context_depth = self.special_jump_stack.len();
            self.push_special_jumps(target);
            if self.special_jump_stack.len() != old_context_depth {
                break ensure_sufficient_stack(|| {
                    self.translate_block_with_special_jumps(target, old_context_depth)
                });
            }
            block_id = target;
        };
        let span = spans
            .iter()
            .rev()
            .fold(last_block.span, |span, part| combine_span(part, &span));
        statements.extend(last_block.statements);
        tgt::Block::new(span, statements)
    }

    /// Translate a block including surrounding control-flow like looping.
    #[tracing::instrument(skip(self), fields(stack = ?self.special_jump_stack))]
    fn translate_block(&mut self, block_id: src::BlockId) -> tgt::Block {
        ensure_sufficient_stack(|| {
            let old_context_depth = self.special_jump_stack.len();
            self.push_special_jumps(block_id);
            self.translate_block_with_special_jumps(block_id, old_context_depth)
        })
    }

    /// Some of the blocks we might jump to inside the tree of this block can't be translated as
    /// normal blocks: the loop backward edges must become `continue`s and the merge nodes may need
    /// some care if we're jumping to them from distant locations.
    /// For this purpose, we push to the `special_jump_stack` the block ids that must be translated
    /// specially. In `translate_jump` we check the stack. After translating the block, we restore
    /// the stack to its previous state in `translate_block_with_special_jumps`.
    fn push_special_jumps(&mut self, block_id: src::BlockId) {
        let block_data = &self.cfg.block_data[block_id];

        // Catch jumps to the loop header or loop exit.
        if block_data.is_loop_header {
            self.break_context_depth += 1;
            if let Some(exit_id) = block_data.exit_info.loop_exit {
                self.special_jump_stack.push(SpecialJump::new(
                    exit_id,
                    SpecialJumpKind::LoopBreak(self.break_context_depth),
                ));
            }
            // Put the next block at the top of the stack.
            self.special_jump_stack.push(SpecialJump::new(
                block_id,
                SpecialJumpKind::LoopContinue(self.break_context_depth),
            ));
        }

        // Catch jumps to a merge node.
        let merge_children = &block_data.immediately_dominated_merge_targets;
        if let ReconstructMode::ForwardBreak = self.mode {
            // We support forward-jumps using `break`
            // The child with highest postorder numbering is nested outermost in this scheme.
            for &child in merge_children {
                self.break_context_depth += 1;
                self.special_jump_stack.push(SpecialJump::new(
                    child,
                    SpecialJumpKind::ForwardBreak(self.break_context_depth),
                ));
            }
        }

        if let Some(bid) = block_data.exit_info.switch_exit
            && !(matches!(self.mode, ReconstructMode::ForwardBreak)
                && merge_children.contains(&bid))
        {
            // Move some code that would be inside one or several switch branches to be after the
            // switch intead.
            self.special_jump_stack
                .push(SpecialJump::new(bid, SpecialJumpKind::NextBlock));
        }
    }

    /// Translate a block after `push_special_jumps`, and pop the special jumps it pushed above
    /// `old_context_depth`.
    fn translate_block_with_special_jumps(
        &mut self,
        block_id: src::BlockId,
        old_context_depth: usize,
    ) -> tgt::Block {
        let span = self.cfg.block_data[block_id].span;
        // Translate this block. Any jumps to a loop header or a merge node will be replaced with
        // `continue`/`break`.
        let mut block = self.translate_block_itself(block_id);

        // Reset the state to what it was previously, and translate what remains.
        let new_statement = move |kind| tgt::Statement::new(block.span, kind);
        while self.special_jump_stack.len() > old_context_depth {
            let special_jump = self.special_jump_stack.pop().unwrap();
            match &special_jump.kind {
                SpecialJumpKind::LoopContinue(_) => {
                    self.break_context_depth -= 1;
                    if let ReconstructMode::ForwardBreak = self.mode {
                        // We add `continue` at the end for users that don't know that the default
                        // behavior at the end of a loop block is `continue`. Not needed for
                        // `Duplicate` mode because we use explicit `continue`s there. TODO: clean
                        // that up.
                        block
                            .statements
                            .push(new_statement(tgt::StatementKind::Continue(0)));
                    }
                    block = new_statement(tgt::StatementKind::Loop(Box::new(block))).into_block();
                }
                SpecialJumpKind::ForwardBreak(_) => {
                    self.break_context_depth -= 1;
                    // Remove unneeded `break`s in branches leading up to that final one.
                    iter_tail_statements(&mut block, &mut |st| {
                        if matches!(st.kind, tgt::StatementKind::Break(0)) {
                            st.kind = tgt::StatementKind::Nop;
                        }
                    });
                    // We add a `loop { ...; break }` so that we can use `break` to jump forward.
                    block
                        .statements
                        .push(new_statement(tgt::StatementKind::Break(0)));
                    block = new_statement(tgt::StatementKind::Loop(Box::new(block))).into_block();
                    // We must translate the merge nodes after the block used for forward jumps to
                    // them.
                    let next_block = self.translate_jump(span, special_jump.target_block);
                    block = block.merge(next_block);
                }
                SpecialJumpKind::NextBlock | SpecialJumpKind::LoopBreak(..) => {
                    let next_block = self.translate_jump(span, special_jump.target_block);
                    block = block.merge(next_block);
                }
            }
        }
        block
    }
}

/// Remove the loops whose only jump is the `break` at their end: these were introduced to jump
/// forward, but end up not being needed.
fn remove_useless_jump_blocks(body: &mut tgt::ExprBody) {
    use tgt::{Block, StatementKind};
    #[derive(Default, Clone, Copy)]
    struct Count {
        continue_count: u32,
        break_count: u32,
    }

    fn nested_blocks(kind: &mut StatementKind) -> SmallVec<[&mut Block; 2]> {
        match kind {
            StatementKind::Drop { on_unwind, .. }
            | StatementKind::DropEmptyBox { on_unwind, .. }
            | StatementKind::Assert { on_unwind, .. }
            | StatementKind::Call { on_unwind, .. }
            | StatementKind::Panic { on_unwind, .. } => smallvec::smallvec![&mut **on_unwind],
            StatementKind::InlineAsm {
                fallthrough,
                labels,
                on_unwind,
                ..
            } => fallthrough
                .as_deref_mut()
                .into_iter()
                .chain(labels.iter_mut())
                .chain([&mut **on_unwind])
                .collect(),
            StatementKind::Switch { branches, .. } => branches.iter_mut().collect(),
            StatementKind::Loop(body) => smallvec::smallvec![&mut **body],
            StatementKind::Assign(..)
            | StatementKind::SetDiscriminant(..)
            | StatementKind::StorageLive(..)
            | StatementKind::StorageDead(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::Borrowck(..)
            | StatementKind::Break(..)
            | StatementKind::Continue(..)
            | StatementKind::UnwindTerminate(..)
            | StatementKind::UnwindResume
            | StatementKind::GotoCleanup(..)
            | StatementKind::Return
            | StatementKind::UndefinedBehavior
            | StatementKind::Nop => SmallVec::new(),
        }
    }

    /// Count the jumps to each loop. Loops are numbered in pre-order; `loop_stack` holds the
    /// numbers of the loops we're in.
    fn count_jumps(block: &mut Block, loop_stack: &mut Vec<usize>, counts: &mut Vec<Count>) {
        for st in &mut block.statements {
            match st.kind {
                StatementKind::Loop(_) => {
                    loop_stack.push(counts.len());
                    counts.push(Count::default());
                }
                StatementKind::Break(depth) => {
                    counts[loop_stack[loop_stack.len() - 1 - depth]].break_count += 1;
                }
                StatementKind::Continue(depth) => {
                    counts[loop_stack[loop_stack.len() - 1 - depth]].continue_count += 1;
                }
                _ => {}
            }
            for block in nested_blocks(&mut st.kind) {
                count_jumps(block, loop_stack, counts);
            }
            if st.kind.is_loop() {
                loop_stack.pop();
            }
        }
    }

    /// Remove the useless loops, in the same order as `count_jumps`. `loop_stack` holds, for every
    /// loop we're in, whether we're keeping it.
    fn remove_loops(
        block: &mut Block,
        loop_stack: &mut Vec<bool>,
        counts: &mut impl Iterator<Item = Count>,
    ) {
        // The positions of the loops to remove from this block.
        let mut removed_loops: SmallVec<[usize; 2]> = SmallVec::new();
        for (i, st) in block.statements.iter_mut().enumerate() {
            match &mut st.kind {
                StatementKind::Loop(block) => {
                    let counts = counts.next().unwrap();
                    let remove = counts.continue_count == 0
                        && counts.break_count == 1
                        && matches!(
                            block.statements.last().unwrap().kind,
                            StatementKind::Break(0)
                        );
                    loop_stack.push(!remove);
                }
                StatementKind::Break(depth) | StatementKind::Continue(depth) => {
                    *depth = loop_stack[loop_stack.len() - *depth..]
                        .iter()
                        .filter(|&&keep| keep)
                        .count();
                }
                _ => {}
            }
            for block in nested_blocks(&mut st.kind) {
                remove_loops(block, loop_stack, counts);
            }
            if st.kind.is_loop() && !loop_stack.pop().unwrap() {
                // Replace the final `break` with a `Nop`; we inline the loop body below.
                let StatementKind::Loop(inner_block) = &mut st.kind else {
                    unreachable!()
                };
                inner_block.statements.last_mut().unwrap().kind = StatementKind::Nop;
                removed_loops.push(i);
            }
        }
        // These vectors make up most of the final bodies: avoid leaving slack in them.
        if removed_loops.is_empty() {
            block.statements.shrink_to_fit();
            return;
        }
        let len = block.statements.len() - removed_loops.len()
            + removed_loops
                .iter()
                .map(|&i| block.statements[i].kind.as_loop().unwrap().statements.len())
                .sum::<usize>();
        let mut removed_loops = removed_loops.into_iter().peekable();
        let statements = mem::replace(&mut block.statements, Vec::with_capacity(len));
        for (i, st) in statements.into_iter().enumerate() {
            if removed_loops.next_if_eq(&i).is_some() {
                let StatementKind::Loop(inner_block) = st.kind else {
                    unreachable!()
                };
                block.statements.extend(inner_block.statements);
            } else {
                block.statements.push(st);
            }
        }
    }

    for block in body.body.blocks_mut() {
        let mut counts = Vec::new();
        count_jumps(block, &mut Vec::new(), &mut counts);
        remove_loops(block, &mut Vec::new(), &mut counts.into_iter());
    }
}

/// Copy the cleanup blocks that take less space copied at each jump to them than shared.
fn inline_small_cleanups(body: &mut tgt::StructuredBody) {
    use tgt::{CleanupId, StatementKind};
    if body.cleanups.is_empty() {
        return;
    }
    // The number of jumps to each cleanup block, the cleanup blocks each one jumps to (once per
    // jump), and the number of statements of each one.
    let mut refs = body.cleanups.map_ref(|_| 0usize);
    let mut targets = body.cleanups.map_ref(|_| Vec::new());
    let mut sizes = body.cleanups.map_ref(|_| 0usize);
    body.block.visit_statements(|st| {
        if let StatementKind::GotoCleanup(id) = st.kind {
            refs[id] += 1;
        }
    });
    for (id, block) in body.cleanups.iter_mut_enumerated() {
        block.visit_statements(|st| {
            if !st.kind.is_nop() {
                sizes[id] += 1;
            }
            if let StatementKind::GotoCleanup(target) = st.kind {
                refs[target] += 1;
                targets[id].push(target);
            }
        });
    }

    // Copying a cleanup block makes the ones that jump to it bigger, so we decide for the
    // cleanup blocks after the ones they jump to.
    let mut order = Vec::with_capacity(body.cleanups.len());
    let mut visited = body.cleanups.map_ref(|_| false);
    for root in body.cleanups.indices() {
        let mut stack = vec![(root, 0)];
        while let Some((id, next_target)) = stack.pop() {
            if next_target == 0 {
                if visited[id] {
                    continue;
                }
                visited[id] = true;
            }
            if let Some(&target) = targets[id].get(next_target) {
                stack.push((id, next_target + 1));
                stack.push((target, 0));
            } else {
                order.push(id);
            }
        }
    }
    let mut inline = body.cleanups.map_ref(|_| false);
    for &id in &order {
        sizes[id] += targets[id]
            .iter()
            .filter(|&&target| inline[target])
            .map(|&target| sizes[target] - 1)
            .sum::<usize>();
        // Copied, the statements take `refs * size` lines of pretty-printed code. Shared, they
        // take `refs + size + 3`: the jumps, the block, and an empty line, a header and a closing
        // line around it.
        inline[id] = refs[id] * sizes[id] <= refs[id] + sizes[id] + 3;
    }
    if !inline.iter().any(|&inline| inline) {
        return;
    }

    // Replace the jumps to the copied blocks with fresh copies of them.
    let replace_jumps =
        |block: &mut tgt::Block, cleanups: &IndexVec<CleanupId, Option<tgt::Block>>| {
            let copy = |id: CleanupId| {
                let mut copy = cleanups[id].clone().unwrap();
                copy.visit_blocks_bwd(|block: &mut tgt::Block| {
                    block.id = tgt::BlockId::fresh();
                    for st in &mut block.statements {
                        st.id = tgt::StatementId::fresh();
                    }
                });
                copy
            };
            block.visit_blocks_bwd(|block: &mut tgt::Block| {
            let is_copied_jump = |st: &tgt::Statement| {
                matches!(st.kind, StatementKind::GotoCleanup(id) if inline[id])
            };
            if let [st] = block.statements.as_slice()
                && let StatementKind::GotoCleanup(id) = st.kind
                && inline[id]
            {
                *block = copy(id);
            } else if block.statements.iter().any(is_copied_jump) {
                for st in mem::take(&mut block.statements) {
                    if let StatementKind::GotoCleanup(id) = st.kind
                        && inline[id]
                    {
                        let copy = copy(id);
                        block.span = combine_span(&block.span, &copy.span);
                        block.statements.extend(copy.statements);
                    } else {
                        block.statements.push(st);
                    }
                }
            }
        });
        };
    let mut cleanups: IndexVec<CleanupId, Option<tgt::Block>> = mem::take(&mut body.cleanups)
        .into_iter()
        .map(Some)
        .collect();
    for &id in &order {
        let mut block = cleanups[id].take().unwrap();
        replace_jumps(&mut block, &cleanups);
        cleanups[id] = Some(block);
    }
    replace_jumps(&mut body.block, &cleanups);

    // Renumber the shared blocks.
    let mut new_ids = cleanups.map_ref(|_| None);
    for (id, block) in cleanups.into_iter_enumerated() {
        if !inline[id] {
            new_ids[id] = Some(body.cleanups.push(block.unwrap()));
        }
    }
    body.visit_statements(|st| {
        if let StatementKind::GotoCleanup(id) = &mut st.kind {
            *id = new_ids[*id].unwrap();
        }
    });
}

fn translate_body(ctx: &TransformCtx, body: &mut Body) {
    use Body::{Structured, Unstructured};
    let Unstructured(src_body) = body else {
        return;
    };
    trace!("About to translate to ullbc: {:?}", src_body.span);
    // Report the time spent per body size, since this pass is superlinear in the number of blocks.
    let _guard = crate::timing::scope_lazy("ullbc_to_llbc-body", || {
        format!(
            "{:05} blocks or less",
            src_body.body.len().next_power_of_two()
        )
    });

    // Calculate info about the graph and heuristically determine loop and switch exit blocks.
    let start_block = BlockId::ZERO;
    let mut ctx = match ReconstructCtx::build(ctx, src_body) {
        Ok(ctx) => ctx,
        Err(Irreducible(bid)) => {
            let span = src_body.body[bid].terminator.span;
            register_error!(
                ctx,
                span,
                "the control-flow graph of this function is not reducible"
            );
            panic!("can't reconstruct irreducible control-flow")
        }
    };
    // Translate the blocks using the computed data.
    let block = ctx.translate_block(start_block);
    // Translating a cleanup block may jump to new ones.
    let mut cleanups = IndexVec::new();
    while let Some(&block_id) = ctx.cleanups.get(cleanups.next_idx()) {
        cleanups.push(ctx.translate_block(block_id));
    }
    let mut tgt_body = tgt::StructuredBody { block, cleanups };
    inline_small_cleanups(&mut tgt_body);

    let mut tgt_body = tgt::ExprBody {
        span: src_body.span,
        locals: src_body.locals.clone(),
        bound_body_regions: src_body.bound_body_regions,
        body: tgt_body,
        comments: src_body.comments.clone(),
    };
    remove_useless_jump_blocks(&mut tgt_body);

    *body = Structured(tgt_body);
}

pub struct Transform;
impl LlbcPass for Transform {
    fn transform_function(&self, ctx: &TransformCtx, decl: &mut FunDecl) {
        translate_body(ctx, &mut decl.body);
    }
}
