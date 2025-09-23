use crate::{ast::Ast, error::ToDiagnostic, lexer::Token};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AstParseError {
    #[error("Unexpected end of input")]
    UnexpectedEndOfInput,

    #[error("Import declared multiple times `{str_val}`")]
    ImportDeclaredMultipleTimes { token: Token, str_val: String },

    #[error("Expected string or `}}` in import body")]
    ImportExpectedStrOrClose { token: Token },

    #[error("Expected `{{` after import key word")]
    ImportExpectedCurlyBracketOpen { token: Token },

    #[error("Expected `\"C\"` after export key word")]
    ExportExpectedStrC { token: Token },

    #[error("Expected `{{` after export key word")]
    ExportExpectedCurlyBracketOpen { token: Token },

    #[error("Duplicate function name definitions: {name}")]
    FnDuplicateStructNames { token: Token, name: String },

    #[error("Duplicate struct name definitions: {name}")]
    StructDuplicateStructNames { token: Token, name: String },

    #[error("Expected `{{` after struct key word")]
    StructExpectedCurlyOpen { token: Token },

    #[error("Expected identifier after `{{` in struct parsing")]
    StructExpectedIdent { token: Token },

    #[error("Unhandled token case {token:?}")]
    UnhandledToken { token: Token },
}

impl ToDiagnostic for AstParseError {
    fn to_diagnostic(&self, file_id: usize) -> Diagnostic<usize> {
        match self {
            AstParseError::UnhandledToken { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("Unhandled token"),
                ])
                .with_notes(vec![String::from(
                    "This token case has not been implemented in the AST parser yet.",
                )]),

            AstParseError::ImportDeclaredMultipleTimes { token, .. } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("Duplicate import"),
                ])
                .with_notes(vec![String::from("Remove one of the imports.")]),

            AstParseError::ImportExpectedStrOrClose { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![Label::primary(
                    file_id,
                    token.span.start..token.span.end,
                )])
                .with_notes(vec![String::from(
                    "Import statements must either be a string literal or a closing brace `}`.",
                )]),

            AstParseError::StructExpectedCurlyOpen { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![Label::primary(
                    file_id,
                    token.span.start..token.span.end,
                )])
                .with_notes(vec![String::from(
                    "Expected a `{` after `struct Name`, e.g. `struct Foo {}`.",
                )]),

            AstParseError::StructExpectedIdent { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![Label::primary(
                    file_id,
                    token.span.start..token.span.end,
                )])
                .with_notes(vec![String::from(
                    "Expected an identifier after `struct`, e.g. `struct Foo {}`.",
                )]),

            // Default: basic diagnostic with message
            other => Diagnostic::error().with_message(other.to_string()),
        }
    }
}
