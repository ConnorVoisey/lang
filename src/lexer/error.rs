use crate::{
    error::{ErrRender, ToErrRender},
    lexer::Span,
};
use std::{io, num::ParseIntError};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum LexerError {
    #[error("Failed to read src code file")]
    CannotReadFile(#[from] io::Error),

    #[error("Unclosed string, found {span:?})")]
    UnclosedString { span: Span },

    #[error("Unhandled char case: `{char}`")]
    UnhandledChar { span: Span, char: char },

    #[error("Failed to parse digit char array into int")]
    ParseDigitStrToInt(#[from] ParseIntError),

    #[error("unknown data store error")]
    Unknown,
}

impl ToErrRender for LexerError {
    fn to_err_render<'a>(&'a self, src_code: &'a str, file_label: &'a str) -> ErrRender<'a> {
        match self {
            LexerError::CannotReadFile(_) => todo!(),
            LexerError::UnclosedString { span } => ErrRender {
                title: self.to_string(),
                span: Some(span.clone()),
                description: Some(String::from("Try closing the string with `\"`")),
                src_code,
                file_label,
            },
            LexerError::UnhandledChar { span, char: _ } => ErrRender {
                title: self.to_string(),
                span: Some(span.clone()),
                description: None,
                src_code,
                file_label,
            },
            LexerError::ParseDigitStrToInt(_) => ErrRender {
                title: self.to_string(),
                span: None,
                description: Some(String::from(
                    "Internal error, should have been able to parse string",
                )),
                src_code,
                file_label,
            },
            LexerError::Unknown => todo!(),
        }
    }
}
