use crate::{
    error::ToDiagnostic,
    lexer::{Span, Token},
};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum SymbolError {
    #[error("Duplicate function name definitions: {name}")]
    FnDuplicateDefs { token: Token, name: String },

    #[error("Duplicate struct name definitions: {name}")]
    StructDuplicateDefs { token: Token, name: String },

    #[error("{symbol_kind} `{name}` cannot be used as a type")]
    NotAType {
        name: String,
        symbol_kind: String,
        span: Span,
    },

    #[error("Feature not yet implemented: {description}")]
    NotYetImplemented { description: String, span: Span },
}

impl ToDiagnostic for SymbolError {
    fn to_diagnostic(&self, file_id: usize) -> Diagnostic<usize> {
        match self {
            SymbolError::FnDuplicateDefs { token, .. } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("Duplicate function"),
                ])
                .with_notes(vec![String::from(
                    "A function with this name has already been declared. Try renaming it.",
                )]),

            SymbolError::StructDuplicateDefs { token, .. } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("Duplicate struct"),
                ])
                .with_notes(vec![String::from(
                    "A struct with this name has already been declared. Try renaming it.",
                )]),
            SymbolError::NotAType { span, .. } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end).with_message("not a type"),
                ])
                .with_notes(vec![String::from(
                    "Only struct and enum names can be used as types.",
                )]),
            SymbolError::NotYetImplemented { span, .. } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end).with_message("not yet supported"),
                ]),
        }
    }
}
