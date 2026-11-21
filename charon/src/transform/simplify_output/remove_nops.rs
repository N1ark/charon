//! Remove the useless no-ops.
use crate::ast::*;
use crate::options::TranslateOptions;
use crate::transform::ctx::FunDeclPass;

pub struct Transform;
impl FunDeclPass for Transform {
    fn transform_function(&self, _options: &TranslateOptions, fun: &mut FunDecl) {
        match &mut fun.body {
            Body::Unstructured(body) => {
                for blk in &mut body.body {
                    blk.statements
                        .retain(|st| !(st.kind.is_nop() && st.comments_before.is_empty()))
                }
            }
            Body::Structured(body) => body.body.visit_blocks_bwd(|blk: &mut llbc_ast::Block| {
                blk.statements
                    .retain(|st| !(st.kind.is_nop() && st.comments_before.is_empty()))
            }),
            _ => {}
        }
    }
}
