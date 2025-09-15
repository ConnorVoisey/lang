use crate::{
    error::{ErrRender, ToErrRender},
    lexer::{Span, Token},
    types::{TypeId, TypeKind},
};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum UnifyError {
    // #[error("Duplicate function name definitions: {name}")]
    // OccursCheckFailed(TypeId, TypeId),
    #[error("Type mismatch, cannot use type {type_a_str} as type {type_b_str}")]
    Mismatch {
        type_a_str: String,
        type_a_span: Span,
        type_b_str: String,
        type_b_span: Span,
    },
    // Mismatch(TypeId, TypeKind, TypeId, TypeKind),
}

impl ToErrRender for UnifyError {
    fn to_err_render<'a>(&'a self, src_code: &'a str, file_label: &'a str) -> ErrRender<'a> {
        match self {
            UnifyError::Mismatch {
                type_a_str: _,
                type_a_span,
                type_b_str: _,
                type_b_span,
            } => ErrRender {
                title: self.to_string(),
                span: Some(Span {
                    start: type_a_span.start.min(type_b_span.start),
                    end: type_a_span.end.max(type_b_span.end),
                }),
                description: Some(String::from(
                    "These two types are incompatible. Try casting one of them into the other.",
                )),
                src_code,
                file_label,
            },
        }
    }
}
