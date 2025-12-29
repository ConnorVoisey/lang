use crate::{error::ToDiagnostic, lexer::Span};
use codespan_reporting::diagnostic::{Diagnostic, Label};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum TypeCheckingError {
    #[error("The array's inner type cannot be infered from usage")]
    ArrayNoInnerType { creation_span: Span },

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
        "Functions return type did not match its signature, expect {expected_type_str} got {got_type_str}"
    )]
    FnInvalidReturnType {
        got_type_str: String,
        call_type_span: Span,
        expected_type_str: String,
        fn_return_span: Span,
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

    #[error("Cannot assign type {assigned_type_str} to variable of type {var_type_str}")]
    AssignmentMismatch {
        assigned_type_str: String,
        assigned_type_span: Span,
        var_type_str: String,
        var_decl_span: Span,
    },

    #[error("While loop condition must be Bool, got {got_type_str}")]
    WhileConditionNotBool {
        got_type_str: String,
        condition_span: Span,
    },

    #[error("If condition must be Bool, got {got_type_str}")]
    IfConditionNotBool {
        got_type_str: String,
        condition_span: Span,
    },

    #[error("Cannot call non-function type {got_type_str}")]
    CallNonFunction {
        got_type_str: String,
        call_span: Span,
    },

    #[error(
        "If/else branches must have the same return type: if returns {if_type_str}, but else returns {else_type_str}"
    )]
    IfElseBranchMismatch {
        if_type_str: String,
        if_span: Span,
        else_type_str: String,
        else_span: Span,
    },

    #[error("Comparison operator requires Int operands, got {left_type_str} and {right_type_str}")]
    ComparisonTypeMismatch {
        left_type_str: String,
        left_span: Span,
        right_type_str: String,
        right_span: Span,
    },

    #[error("Break statement outside of loop")]
    BreakOutsideLoop { break_span: Span },
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
            TypeCheckingError::FnInvalidReturnType {
                call_type_span,
                fn_return_span,
                ..
            } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, call_type_span.start..call_type_span.end)
                        .with_message("call site"),
                    Label::secondary(file_id, fn_return_span.start..fn_return_span.end)
                        .with_message("return definition"),
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
            TypeCheckingError::AssignmentMismatch {
                assigned_type_span,
                var_decl_span,
                ..
            } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, assigned_type_span.start..assigned_type_span.end)
                        .with_message("cannot assign this"),
                    Label::secondary(file_id, var_decl_span.start..var_decl_span.end)
                        .with_message("variable declared here"),
                ])
                .with_notes(vec![String::from(
                    "The type of the value being assigned doesn't match the variable's type.",
                )]),
            TypeCheckingError::WhileConditionNotBool { condition_span, .. } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, condition_span.start..condition_span.end)
                        .with_message("condition must be Bool"),
                ])
                .with_notes(vec![String::from(
                    "While loop conditions must evaluate to a boolean value.",
                )]),
            TypeCheckingError::IfConditionNotBool { condition_span, .. } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, condition_span.start..condition_span.end)
                        .with_message("condition must be Bool"),
                ])
                .with_notes(vec![String::from(
                    "If conditions must evaluate to a boolean value.",
                )]),
            TypeCheckingError::CallNonFunction { call_span, .. } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, call_span.start..call_span.end)
                        .with_message("cannot call this"),
                ])
                .with_notes(vec![String::from(
                    "Only functions can be called with () syntax.",
                )]),
            TypeCheckingError::IfElseBranchMismatch {
                if_span, else_span, ..
            } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, if_span.start..if_span.end)
                        .with_message("if branch returns this type"),
                    Label::secondary(file_id, else_span.start..else_span.end)
                        .with_message("else branch returns different type"),
                ])
                .with_notes(vec![String::from(
                    "All branches of an if expression must return the same type.",
                )]),
            TypeCheckingError::ComparisonTypeMismatch {
                left_span,
                right_span,
                ..
            } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, left_span.start..left_span.end)
                        .with_message("left operand"),
                    Label::secondary(file_id, right_span.start..right_span.end)
                        .with_message("right operand"),
                ])
                .with_notes(vec![String::from(
                    "Comparison operators (<, >, <=, >=) require integer operands.",
                )]),
            TypeCheckingError::BreakOutsideLoop { break_span } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, break_span.start..break_span.end)
                        .with_message("cannot break here"),
                ])
                .with_notes(vec![String::from(
                    "Break statements can only be used inside while loops.",
                )]),
            TypeCheckingError::ArrayNoInnerType { creation_span } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, creation_span.start..creation_span.end)
                        .with_message("array instantiated here"),
                ])
                .with_notes(vec![String::from(
                    "Adding an element to this array will give it a type",
                )]),
        }
    }
}
