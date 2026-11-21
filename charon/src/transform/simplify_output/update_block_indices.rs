//! Renumber rechable blocks to be consecutive and in topological order (ignoring loop backedges).
use std::mem;

use crate::ids::*;
use crate::transform::TransformCtx;
use crate::ullbc_ast::*;

use crate::transform::ctx::UllbcPass;

pub struct Transform;
impl UllbcPass for Transform {
    fn transform_body(&self, _ctx: &TransformCtx, b: &mut ExprBody) {
        // Compute the reachable blocks in DFS postorder, exploring the distinct targets of each
        // block in order.
        let mut discovered: IndexVec<BlockId, bool> = b.body.map_ref(|_| false);
        let mut finished: IndexVec<BlockId, bool> = b.body.map_ref(|_| false);
        let mut postorder = Vec::new();
        let mut stack = vec![START_BLOCK_ID];
        while let Some(&id) = stack.last() {
            if !mem::replace(&mut discovered[id], true) {
                let targets = b.body[id].targets();
                for (i, &target) in targets.iter().enumerate() {
                    if !discovered[target] && !targets[..i].contains(&target) {
                        stack.push(target);
                    }
                }
            } else {
                stack.pop();
                if !mem::replace(&mut finished[id], true) {
                    postorder.push(id);
                }
            }
        }

        let mut old_blocks = mem::take(&mut b.body).map(Some);
        let mut id_map: IndexVec<BlockId, Option<BlockId>> = old_blocks.map_ref(|_| None);
        for id in postorder.into_iter().rev() {
            let new_id = b.body.push(old_blocks[id].take().unwrap());
            id_map[id] = Some(new_id);
        }

        // Update the ids.
        b.visit_block_ids_mut(|id: &mut BlockId| *id = id_map[*id].unwrap());
    }
}
