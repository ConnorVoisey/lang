use crate::{
    ast::error::AstParseError,
    lexer::{Span, error::LexerError},
    types::error::UnifyError,
};
use colored::Colorize;
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
        match self {
            CompliationError::Disconnect(_) => todo!(),
            CompliationError::LexingError(lexer_errors) => {
                for err in lexer_errors {
                    err.to_err_render(src_code, file_label).render_error();
                }
            }
            CompliationError::AstParseError(errs) => {
                for err in errs {
                    err.to_err_render(src_code, file_label).render_error();
                }
            }
            CompliationError::TypeCheckingError(errs) => {
                for err in errs {
                    err.to_err_render(src_code, file_label).render_error();
                }
            }
            CompliationError::Unknown => todo!(),
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

const ERROR_CONTEXT_LINE: usize = 3;

impl<'a> ErrRender<'a> {
    fn build_new_lines_vec(&self) -> Vec<usize> {
        self.src_code
            .char_indices()
            .filter_map(|(i, c)| match c {
                '\n' => Some(i),
                _ => None,
            })
            .collect()
    }

    fn get_context_line(&self, new_lines: &[usize]) -> Option<usize> {
        match &self.span {
            None => None,
            Some(span) => {
                for (i, new_line_offset) in new_lines.iter().enumerate() {
                    if span.start <= *new_line_offset {
                        return Some(i);
                    }
                }
                None
            }
        }
    }
    fn print_context(&self, span: Span) {
        let new_lines = self.build_new_lines_vec();
        let line_index = self.get_context_line(&new_lines).unwrap();

        dbg!(line_index);
        let ctx_start_i = line_index.max(ERROR_CONTEXT_LINE) - ERROR_CONTEXT_LINE;
        let ctx_end_i = (line_index + ERROR_CONTEXT_LINE + 1).min(new_lines.len() - 1);
        let digits = (ctx_end_i + 2).checked_ilog10().unwrap() as usize;
        for line_i in (ctx_start_i)..(ctx_end_i) {
            let line_start = if line_i == 0 {
                0
            } else {
                new_lines[line_i - 1]
            };
            let line_end = new_lines[line_i];
            let line_num = line_i;
            println!(
                "{} {}",
                format!("{line_num:width$}|", width = digits + 1).blue(),
                &self.src_code[line_start + 1..line_end]
            );
            if line_i == line_index {
                let offset = span.start - new_lines[line_i.max(1) - 1].min(span.start);
                let span_len = span.end - span.start;
                // TODO: check if the span is over multiple lines
                println!(
                    "{}{}",
                    (0..offset + digits + 2).map(|_| ' ').collect::<String>(),
                    (0..span_len).map(|_| '^').collect::<String>().red(),
                );
            }
        }
    }

    pub fn render_error(&self) {
        println!("\n{}", self.file_label.red());
        println!("{}", self.title.red());
        if let Some(span) = &self.span {
            self.print_context(span.clone());
        }
        if let Some(des) = &self.description {
            println!("{}", des.red());
        }
        println!()
    }
}
