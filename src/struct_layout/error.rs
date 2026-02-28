use crate::{error::ToDiagnostic, lexer::Span};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum StructLayoutError {
    #[error("Cyclic struct dependency detected")]
    CyclicDependency { struct_spans: Vec<Span> },

    #[error("Cannot compute layout: {description}")]
    UnsupportedType { description: String, span: Span },

    #[error("Internal layout error: {description}")]
    InternalError { description: String },
}

impl ToDiagnostic for StructLayoutError {
    fn to_diagnostic(&self, file_id: usize) -> Diagnostic<usize> {
        match self {
            StructLayoutError::CyclicDependency { struct_spans } => {
                let mut labels: Vec<Label<usize>> = struct_spans
                    .iter()
                    .map(|span| {
                        Label::primary(file_id, span.start..span.end)
                            .with_message("part of the cycle")
                    })
                    .collect();
                if labels.is_empty() {
                    labels.push(Label::primary(file_id, 0..0).with_message("cycle detected"));
                }
                Diagnostic::error()
                    .with_message(self.to_string())
                    .with_labels(labels)
                    .with_notes(vec![String::from(
                        "Recursive struct types are not allowed. Use references (&) to break the cycle.",
                    )])
            }
            StructLayoutError::UnsupportedType { span, .. } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message("unsupported type in struct field"),
                ]),
            StructLayoutError::InternalError { .. } => Diagnostic::error()
                .with_message(self.to_string())
                .with_notes(vec![String::from(
                    "This is a compiler bug. Please report it.",
                )]),
        }
    }
}
