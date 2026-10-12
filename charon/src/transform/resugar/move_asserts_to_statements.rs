//! # Micro-pass: if we want to reconstruct fallible operations, the first step
//! is to move all assert terminators that correspond do dynamic checks into
//! statements, to make them easier to recognize and transform in the next pass.
//! It's important this pass runs before [`crate::transform::control_flow::merge_goto_chains`], to
//! ensure the gotos we substitute the asserts with get merged, but before
//! [`crate::transform::resugar::reconstruct_fallible_operations`], since it will expect the
//! asserts to be in statements.
//! In ULLBC, which keeps unwinding paths, the asserts whose unwinding runs cleanup code (e.g. drops)
//! stay terminators, so that this cleanup still runs when the check fails.

use std::collections::HashSet;

use crate::ast::*;
use crate::transform::TransformCtx;
use crate::ullbc_ast::{BlockId, ExprBody, Statement, StatementKind, TerminatorKind};

use crate::transform::ctx::UllbcPass;

pub struct Transform;
impl UllbcPass for Transform {
    fn should_run(&self, options: &crate::options::TranslateOptions) -> bool {
        options.reconstruct_fallible_operations
    }

    fn transform_body(&self, ctx: &mut TransformCtx, b: &mut ExprBody) {
        // Start by computing the set of blocks which are actually panics.
        // Remark: doing this in two steps because reading the blocks at random
        // while doing in-place updates is not natural to do in Rust.
        let panics = b.as_abort_map();
        // The blocks that only continue unwinding.
        let resumes: HashSet<BlockId> = b
            .body
            .iter_enumerated()
            .filter(|(_, block)| {
                block.statements.iter().all(|st| {
                    matches!(
                        st.kind,
                        StatementKind::Nop
                            | StatementKind::StorageLive(_)
                            | StatementKind::StorageDead(_)
                    )
                }) && matches!(block.terminator.kind, TerminatorKind::UnwindResume)
            })
            .map(|(id, _)| id)
            .collect();

        for block in b.body.iter_mut() {
            let TerminatorKind::Assert {
                assert:
                    Assert {
                        check_kind: Some(_),
                        ..
                    },
                target,
                on_unwind,
            } = &block.terminator.kind
            else {
                continue;
            };
            // A statement can't unwind: in ULLBC, which keeps unwinding paths, keep the asserts whose
            // unwinding runs cleanup code (e.g. drops), which would otherwise be skipped when the
            // check fails.
            if ctx.options.ullbc && !panics.contains_key(on_unwind) && !resumes.contains(on_unwind)
            {
                continue;
            }

            let new_terminator = TerminatorKind::Goto { target: *target };
            let old_terminator = std::mem::replace(&mut block.terminator.kind, new_terminator);
            let TerminatorKind::Assert {
                assert, on_unwind, ..
            } = old_terminator
            else {
                unreachable!();
            };

            let on_failure = panics
                .get(&on_unwind)
                .cloned()
                .unwrap_or(AbortKind::Panic(None));

            block.statements.push(Statement {
                kind: StatementKind::Assert { assert, on_failure },
                span: block.terminator.span,
                comments_before: block.terminator.comments_before.clone(),
            });
        }
    }
}
