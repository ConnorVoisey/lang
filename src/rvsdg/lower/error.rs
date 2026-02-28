use crate::{error::ToDiagnostic, lexer::Span};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum LoweringError {
    #[error("Struct field assignment is not yet supported")]
    StructFieldAssignment { span: Span },

    #[error("Struct field lvalue is not yet supported")]
    StructFieldLvalue { span: Span },

    #[error("Enum variant access is not yet supported")]
    EnumVariantAccess { span: Span },

    #[error("Unexpected expression in RVSDG lowering")]
    UnexpectedExpression { description: String, span: Span },
}

impl ToDiagnostic for LoweringError {
    fn to_diagnostic(&self, file_id: usize) -> Diagnostic<usize> {
        match self {
            LoweringError::StructFieldAssignment { span } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message("struct field assignment used here"),
                ])
                .with_notes(vec![String::from(
                    "Struct field assignment is not yet implemented in the compiler.",
                )]),
            LoweringError::StructFieldLvalue { span } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message("struct field lvalue used here"),
                ])
                .with_notes(vec![String::from(
                    "Struct field lvalue pointers are not yet implemented in the compiler.",
                )]),
            LoweringError::EnumVariantAccess { span } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message("enum variant access used here"),
                ])
                .with_notes(vec![String::from(
                    "Enum variant access (::) is not yet implemented in the compiler.",
                )]),
            LoweringError::UnexpectedExpression { span, .. } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message("unexpected expression"),
                ]),
        }
    }
}
