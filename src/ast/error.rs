use crate::{
    error::{ErrRender, ToErrRender},
    lexer::Token,
};
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

impl ToErrRender for AstParseError {
    fn to_err_render<'a>(&'a self, src_code: &'a str, file_label: &'a str) -> ErrRender<'a> {
        match self {
            AstParseError::UnhandledToken { token } => ErrRender {
                title: self.to_string(),
                span: Some(token.span.clone()),
                description: Some(String::from(
                    "This case has not been handled for ast parsing yet.",
                )),
                src_code,
                file_label,
            },
            AstParseError::ImportDeclaredMultipleTimes { token, str_val: _ } => ErrRender {
                title: self.to_string(),
                span: Some(token.span.clone()),
                description: Some(String::from("Remove one of them")),
                src_code,
                file_label,
            },
            AstParseError::ImportExpectedStrOrClose { token } => ErrRender {
                title: self.to_string(),
                span: Some(token.span.clone()),
                description: Some(String::from(
                    "Import statements should either be string of the import or a `}` to clone the import block.",
                )),
                src_code,
                file_label,
            },
            AstParseError::ImportExpectedCurlyBracketOpen { token } => todo!(),
            AstParseError::StructExpectedCurlyOpen { token } => ErrRender {
                title: self.to_string(),
                span: Some(token.span.clone()),
                description: Some(String::from(
                    "Expected an { after `struct Ident`, e.g. `struct Foo {}",
                )),
                src_code,
                file_label,
            },
            AstParseError::StructExpectedIdent { token } => ErrRender {
                title: self.to_string(),
                span: Some(token.span.clone()),
                description: Some(String::from(
                    "Expected an identifer after `struct`, e.g. `struct Foo {}",
                )),
                src_code,
                file_label,
            },
            t => {
                dbg!(t);
                panic!();
            }
        }
    }
}
