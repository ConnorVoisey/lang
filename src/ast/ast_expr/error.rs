use crate::{
    error::ToDiagnostic,
    lexer::{Span, Token},
};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum MatchParseError {
    #[error("Unexpected end of input")]
    UnexpectedEndOfInput,

    #[error("Expected `{{` after match expr")]
    ExpectedOpenAfterMatchExpr { token: Token },

    #[error("Expected `=>` after match expr { Target")]
    ExpectedFatArrow { token: Token },
}
impl ToDiagnostic for MatchParseError {
    fn to_diagnostic(&self, file_id: usize) -> Diagnostic<usize> {
        match self {
            MatchParseError::UnexpectedEndOfInput => {
                Diagnostic::error().with_message("Unexpected end of input")
            }
            MatchParseError::ExpectedOpenAfterMatchExpr { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("Expected `{{` here instead"),
                ])
                .with_notes(vec![String::from("e.g. match { true => 1, false => 0 }")]),
            MatchParseError::ExpectedFatArrow { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("Expected `=>` here instead"),
                ])
                .with_notes(vec![String::from("e.g. match { true => 1, false => 0 }")]),
            TypeParseError::ArrayExpectedIntAfterType { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("Expected integer here instead"),
                ])
                .with_notes(vec![String::from("Arrays are defined like this [I32; 5]")]),
            TypeParseError::ArrayExpectedClose { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("Expected `]` here instead"),
                ])
                .with_notes(vec![String::from("Arrays are defined like this [I32; 5]")]),
            TypeParseError::NotTypeToken { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("Expected type here"),
                ])
                .with_notes(vec![String::from(
                    "Type could be I32, [I32; 5] or anything type like",
                )]),
        }
    }
}
