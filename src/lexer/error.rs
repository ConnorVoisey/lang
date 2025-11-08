use crate::{error::ToDiagnostic, lexer::Span};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use std::{io, num::ParseIntError};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum LexerError {
    #[error("Failed to read src code file")]
    CannotReadFile(#[from] io::Error),

    #[error("Unclosed string")]
    UnclosedString { span: Span },

    #[error("Unhandled character: `{char}`")]
    UnhandledChar { span: Span, char: char },

    #[error("Unhandled backslash character: `\\{char}`")]
    UnhandledSlashChar { span: Span, char: char },

    #[error("Failed to parse digit char array into int")]
    ParseDigitStrToInt(#[from] ParseIntError),

    #[error("Unknown lexer error")]
    Unknown,
}

impl ToDiagnostic for LexerError {
    fn to_diagnostic(&self, file_id: usize) -> Diagnostic<usize> {
        match self {
            LexerError::CannotReadFile(_) => Diagnostic::error()
                .with_message(self.to_string())
                .with_notes(vec![String::from(
                    "Check that the source file exists and is readable.",
                )]),

            LexerError::UnclosedString { span } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message("Unclosed string literal"),
                ])
                .with_notes(vec![String::from("Try closing the string with `\"`.")]),

            LexerError::UnhandledChar { span, char } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![Label::primary(file_id, span.start..span.end)])
                .with_notes(vec![format!("Unhandled character: `{}`", char)]),

            LexerError::UnhandledSlashChar { span, .. } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![Label::primary(file_id, span.start..span.end)])
                .with_notes(vec![self.to_string()]),

            LexerError::ParseDigitStrToInt(_) => Diagnostic::error()
                .with_message(self.to_string())
                .with_notes(vec![String::from(
                    "Internal error: failed to parse digits.",
                )]),

            LexerError::Unknown => Diagnostic::error().with_message("Unknown lexer error"),
        }
    }
}
