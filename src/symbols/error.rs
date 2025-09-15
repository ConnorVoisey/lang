use crate::{
    error::{ErrRender, ToErrRender},
    lexer::Token,
};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum SymbolError {
    #[error("Duplicate function name definitions: {name}")]
    FnDuplicateDefs { token: Token, name: String },

    #[error("Duplicate struct name definitions: {name}")]
    StructDuplicateDefs { token: Token, name: String },
}

impl ToErrRender for SymbolError {
    fn to_err_render<'a>(&'a self, src_code: &'a str, file_label: &'a str) -> ErrRender<'a> {
        match self {
            SymbolError::FnDuplicateDefs { token, name: _ } => ErrRender {
                title: self.to_string(),
                span: Some(token.span.clone()),
                description: Some(String::from(
                    "A function with this name has already been declared within this scope. Try renaming the function",
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
