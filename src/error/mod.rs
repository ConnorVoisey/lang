use crate::{
    ast::error::AstParseError,
    lexer::{Span, error::LexerError},
    types::error::UnifyError,
};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum CompliationError {
    #[error("Failed to read src code file")]
    Disconnect(#[from] LexerError),

    #[error("Lexing error")]
    LexingError(Vec<LexerError>),

    #[error("Ast parsing error")]
    AstParseError(Vec<AstParseError>),

    #[error("Type Checking error")]
    TypeCheckingError(Vec<UnifyError>),

    #[error("unknown data store error")]
    Unknown,
}

pub trait ToErrRender {
    fn to_err_render<'a>(&'a self, src_code: &'a str, file_label: &'a str) -> ErrRender<'a>;
}

impl CompliationError {
    pub fn display_error(&self, src_code: &str, file_label: &str) {
        let mut files = SimpleFiles::new();
        let file_id = files.add(file_label, src_code);

        let mut errs = vec![];
        match self {
            CompliationError::Disconnect(_) => todo!(),
            CompliationError::LexingError(lexer_errors) => {
                for err in lexer_errors {
                    errs.push(err.to_err_render(src_code, file_label));
                }
            }
            CompliationError::AstParseError(ast_errs) => {
                for err in ast_errs {
                    errs.push(err.to_err_render(src_code, file_label));
                }
            }
            CompliationError::TypeCheckingError(type_errs) => {
                for err in type_errs {
                    errs.push(err.to_err_render(src_code, file_label));
                }
            }
            CompliationError::Unknown => todo!(),
        }

        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config {
            before_label_lines: 3,
            after_label_lines: 3,
            ..Default::default()
        };

        for err in errs {
            let mut diagnostic = Diagnostic::error().with_message(err.title);
            // .with_code("E0308")
            if let Some(span) = err.span {
                diagnostic = diagnostic.with_labels(vec![
                    Label::primary(file_id, span.start..span.end).with_message("Here"),
                ]);
            }
            if let Some(description) = err.description {
                diagnostic = diagnostic.with_notes(vec![description]);
            }

            term::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();
        }
    }
}

pub struct ErrRender<'a> {
    pub title: String,
    pub src_code: &'a str,
    pub span: Option<Span>,
    pub file_label: &'a str,
    pub description: Option<String>,
}
