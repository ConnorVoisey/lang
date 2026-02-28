use crate::rvsdg::lower::error::LoweringError;
use crate::struct_layout::error::StructLayoutError;
use crate::symbols::error::SymbolError;
use crate::type_checker::error::TypeCheckingError;
use crate::{ast::error::AstParseError, lexer::error::LexerError};
use codespan_reporting::diagnostic::Diagnostic;
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

    #[error("Symbol resolution error")]
    SymbolError(Vec<SymbolError>),

    #[error("Type Checking error")]
    TypeCheckingError(Vec<TypeCheckingError>),

    #[error("Struct layout error")]
    StructLayoutError(Vec<StructLayoutError>),

    #[error("RVSDG lowering error")]
    LoweringError(Vec<LoweringError>),

    #[error("Linking failed")]
    LinkingError(String),

    #[error("unknown data store error")]
    Unknown,
}

pub trait ToDiagnostic {
    fn to_diagnostic(&self, file_id: usize) -> Diagnostic<usize>;
}

impl CompliationError {
    pub fn display(&self, src_code: &str, file_label: &str) {
        let mut files = SimpleFiles::new();
        let file_id = files.add(file_label, src_code);

        let diagnostics: Vec<Diagnostic<usize>> = match self {
            CompliationError::Disconnect(_) => vec![],
            CompliationError::LexingError(errs) => {
                errs.iter().map(|e| e.to_diagnostic(file_id)).collect()
            }
            CompliationError::AstParseError(errs) => {
                errs.iter().map(|e| e.to_diagnostic(file_id)).collect()
            }
            CompliationError::SymbolError(errs) => {
                errs.iter().map(|e| e.to_diagnostic(file_id)).collect()
            }
            CompliationError::TypeCheckingError(errs) => {
                errs.iter().map(|e| e.to_diagnostic(file_id)).collect()
            }
            CompliationError::StructLayoutError(errs) => {
                errs.iter().map(|e| e.to_diagnostic(file_id)).collect()
            }
            CompliationError::LoweringError(errs) => {
                errs.iter().map(|e| e.to_diagnostic(file_id)).collect()
            }
            CompliationError::LinkingError(_) | CompliationError::Unknown => vec![],
        };

        let writer = StandardStream::stderr(ColorChoice::Always);
        let config = codespan_reporting::term::Config {
            before_label_lines: 3,
            after_label_lines: 3,
            ..Default::default()
        };

        for diagnostic in diagnostics {
            term::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();
        }
    }
}
