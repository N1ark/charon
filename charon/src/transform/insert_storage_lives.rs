//! Add missing StorageLives -- in MIR, some locals are considered "always" initialised, and have
//! no StorageLive and StorageDead instructions associated; this always includes the arguments
//! and the return value, but also sometimes includes other locals. We make sure these additional
//! locals get initialised at the start of the function.
use std::collections::HashSet;

use itertools::Itertools;

use crate::ast::*;
use crate::transform::TransformCtx;
use crate::ullbc_ast::{BlockId, RawStatement, Statement};

use super::ctx::UllbcPass;

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_ctx(&self, ctx: &mut TransformCtx) {
        ctx.for_each_fun_decl(|_ctx, fun| {
            let Ok(Body::Unstructured(body)) = &mut fun.body else {
                return;
            };

            let mentioned_locals = body
                .body
                .iter()
                .flat_map(|b| {
                    b.statements.iter().filter_map(|stt| match stt.content {
                        RawStatement::StorageDead(loc) | RawStatement::StorageLive(loc) => {
                            Some(loc)
                        }
                        _ => None,
                    })
                })
                .collect::<HashSet<_>>();

            // We are only interested in locals that are neither the return value (index 0),
            // nor the arguments (indices 1..=arg_count).
            let always_init_locals = body
                .locals
                .locals
                .iter()
                .filter_map(|local| {
                    if !mentioned_locals.contains(&local.index)
                        && (local.index > body.locals.arg_count)
                    {
                        Some(local.index)
                    } else {
                        None
                    }
                })
                .collect_vec();

            // Insert StorageLive instructions for the always initialised locals.
            let first_block = body.body.get_mut(BlockId::ZERO).unwrap();
            let first_span = if let Some(fst) = first_block.statements.first() {
                fst.span
            } else {
                first_block.terminator.span
            };
            let mut new_statements = Vec::new();
            for local in always_init_locals {
                new_statements.push(Statement::new(first_span, RawStatement::StorageLive(local)));
            }
            let mut statements = Vec::new();
            statements.append(&mut new_statements);
            statements.append(&mut first_block.statements);
            first_block.statements = statements;
        });
    }
}
