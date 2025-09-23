use crate::{error::ToDiagnostic, lexer::Span};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum TypeCheckingError {
    #[error(
        "Tried calling a function with invalid args, expected {fn_arg_def_str} got {call_type_str}"
    )]
    FnInvalidArg {
        call_type_str: String,
        call_type_span: Span,
        fn_arg_def_str: String,
        fn_arg_def_span: Span,
    },

    #[error(
        "Tried calling a function with the incorect amonut of arguments, expected {expected_arg_count}, got {got_arg_count}"
    )]
    MissingFnArgCall {
        expected_arg_count: usize,
        got_arg_count: usize,
        calling_span: Span,
        fn_def_str: String,
        fn_def_span: Span,
    },

    #[error("Type mismatch, cannot use type {type_a_str} as type {type_b_str}")]
    Mismatch {
        type_a_str: String,
        type_a_span: Span,
        type_b_str: String,
        type_b_span: Span,
    },
}

impl ToDiagnostic for TypeCheckingError {
    fn to_diagnostic(&self, file_id: usize) -> Diagnostic<usize> {
        match self {
            TypeCheckingError::FnInvalidArg {
                call_type_span,
                fn_arg_def_span,
                ..
            } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, call_type_span.start..call_type_span.end)
                        .with_message("call site"),
                    Label::secondary(file_id, fn_arg_def_span.start..fn_arg_def_span.end)
                        .with_message("parameter definition"),
                ])
                .with_notes(vec![String::from(
                    "These types are not compatible. Consider casting into the expected type.",
                )]),

            TypeCheckingError::MissingFnArgCall {
                calling_span,
                fn_def_span,
                ..
            } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, calling_span.start..calling_span.end)
                        .with_message("call site"),
                    Label::secondary(file_id, fn_def_span.start..fn_def_span.end)
                        .with_message("function definition"),
                ])
                .with_notes(vec![String::from(
                    "Try adding the missing arguments or removing the parameter.",
                )]),

            TypeCheckingError::Mismatch {
                type_a_span,
                type_b_span,
                ..
            } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, type_a_span.start..type_a_span.end)
                        .with_message("here"),
                    Label::secondary(file_id, type_b_span.start..type_b_span.end)
                        .with_message("here"),
                ])
                .with_notes(vec![String::from(
                    "These two types are incompatible. Try casting one of them into the other.",
                )]),
        }
    }
}
