use crate::{
    error::ToDiagnostic,
    lexer::{Span, Token},
};
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

    #[error("{}", self.to_string())]
    TypeParse(TypeParseError),

    #[error("Duplicate function name definitions: {name}")]
    FnDuplicateStructNames { token: Token, name: String },

    #[error("Duplicate struct name definitions: {name}")]
    StructDuplicateStructNames { token: Token, name: String },

    #[error("Expected `{{` after struct key word")]
    StructExpectedCurlyOpen { token: Token },

    #[error("Expected identifier after `{{` in struct parsing")]
    StructExpectedIdent { token: Token },

    #[error("Expected `,` or `}}` within struct parsing")]
    StructExpectedCommaOrClose { token: Token },

    #[error("Duplicate enum name definitions: {name}")]
    EnumDuplicateStructNames { token: Token, name: String },

    #[error("Expected `{{` after enum key word")]
    EnumExpectedCurlyOpen { token: Token },

    #[error("Expected identifier after `{{` in enum parsing")]
    EnumExpectedIdent { token: Token },

    #[error("Unhandled token case {token:?}")]
    UnhandledToken { token: Token },

    // function-specific parse errors (you added some previously; keep them)
    #[error("Expected identifier after `fn`")]
    FnExpectedIdent { token: Token },

    #[error("Expected `(` after function name")]
    FnExpectedParenOpen { token: Token },

    #[error("Expected parameter or `)` in parameter list")]
    FnExpectedParamOrClose { token: Token },

    #[error("Expected `,` or `)` between parameters")]
    FnExpectedCommaOrClose { token: Token },

    // Expression / delimiter errors used by the Pratt parser
    #[error("Expected `)` to close this `(`")]
    ExpectedClosingBracket { token: Token },

    #[error("Expected `]` to close this `[`")]
    ExpectedClosingSquareBracket { token: Token },

    #[error("Expected expression here")]
    ExpectedExpression { token: Token },

    #[error("Prefix operator missing right-hand-side expression")]
    PrefixExprMissingRhs { token: Token },

    #[error("`if` missing opening `{{` for block")]
    IfExpectedCurlyOpen { token: Token },

    #[error("`if` missing condition expression")]
    IfExpectedCondition { token: Token },

    #[error("Unexpected token in expression: {token:?}")]
    UnexpectedTokenInExpr { token: Token },

    #[error("Expected operator here")]
    ExpectedOperator { token: Token },

    #[error("Not a valid assignment target")]
    InvalidAssignmentTarget { span: Span },

    #[error("Expected identifier after `let`")]
    LetExpectedIdent { token: Token },

    #[error("Expected `)` to close enum variant type")]
    EnumExpectedClosingBracket { token: Token },

    #[error("Unexpected token after enum variant")]
    EnumUnexpectedTokenAfterVariant { token: Token },

    #[error("Unexpected token in enum body")]
    EnumUnexpectedToken { token: Token },

    #[error("Expected `:` after field name in struct instantiation")]
    StructCreateExpectedColon { token: Token },

    #[error("Expected `;` after extern function declaration")]
    ExternFnExpectedSemiColon { token: Token },
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
            AstParseError::ImportExpectedCurlyBracketOpen { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![Label::primary(
                    file_id,
                    token.span.start..token.span.end,
                )])
                .with_notes(vec![String::from(
                    "Expected a `{` after `import`, e.g. `import Foo { ... }`.",
                )]),
            AstParseError::ExportExpectedStrC { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![Label::primary(
                    file_id,
                    token.span.start..token.span.end,
                )])
                .with_notes(vec![String::from(
                    "Expected string literal \"C\" after `export`.",
                )]),
            AstParseError::ExportExpectedCurlyBracketOpen { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![Label::primary(
                    file_id,
                    token.span.start..token.span.end,
                )])
                .with_notes(vec![String::from(
                    "Expected a `{` after `export`, e.g. `export \"C\" { ... }`.",
                )]),
            AstParseError::FnDuplicateStructNames { token, name } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message(format!("duplicate function name `{}`", name)),
                ])
                .with_notes(vec![String::from(
                    "A function with this name already exists. Try renaming it.",
                )]),
            AstParseError::EnumDuplicateStructNames { token, name } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message(format!("duplicate enum name `{}`", name)),
                ])
                .with_notes(vec![String::from(
                    "A enum with this name already exists. Try renaming it.",
                )]),
            AstParseError::EnumExpectedCurlyOpen { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![Label::primary(
                    file_id,
                    token.span.start..token.span.end,
                )])
                .with_notes(vec![String::from(
                    "Expected a `{` after `enum Name`, e.g. `enum Foo {}`.",
                )]),
            AstParseError::EnumExpectedIdent { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![Label::primary(
                    file_id,
                    token.span.start..token.span.end,
                )])
                .with_notes(vec![String::from(
                    "Expected an identifier after `enum`, e.g. `enum Foo {}`.",
                )]),
            AstParseError::StructExpectedCommaOrClose { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![Label::primary(
                    file_id,
                    token.span.start..token.span.end,
                )])
                .with_notes(vec![String::from(
                    "Expected an either `,` to add another field or `}}` to end struct definition",
                )]),
            AstParseError::StructDuplicateStructNames { token, name } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message(format!("duplicate struct name `{}`", name)),
                ])
                .with_notes(vec![String::from(
                    "A struct with this name already exists. Try renaming it.",
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
            AstParseError::FnExpectedIdent { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("expected identifier here"),
                ])
                .with_notes(vec![String::from(
                    "Functions must have a name, e.g. `fn my_func() {}`.",
                )]),
            AstParseError::FnExpectedParenOpen { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("expected `(` here"),
                ])
                .with_notes(vec![String::from(
                    "Function definitions require parentheses after the name, e.g. `fn foo() {}`.",
                )]),
            AstParseError::FnExpectedParamOrClose { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("expected parameter or `)` here"),
                ])
                .with_notes(vec![String::from(
                    "Functions must have zero or more parameters inside `(...)`.",
                )]),
            AstParseError::FnExpectedCommaOrClose { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("expected `,` or `)` here"),
                ])
                .with_notes(vec![String::from(
                    "Separate parameters with `,`, or close the list with `)`.",
                )]),
            AstParseError::ExpectedClosingBracket { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("expected `)` here"),
                ])
                .with_notes(vec![String::from(
                    "This `(` must be closed with a `)` to form a grouped expression.",
                )]),
            AstParseError::ExpectedClosingSquareBracket { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("expected `]` here"),
                ])
                .with_notes(vec![String::from(
                    "This `[` must be closed with a `]` to form the index expression.",
                )]),
            AstParseError::ExpectedExpression { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![Label::primary(
                    file_id,
                    token.span.start..token.span.end,
                )])
                .with_notes(vec![String::from("An expression was expected here.")]),
            AstParseError::PrefixExprMissingRhs { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![Label::primary(
                    file_id,
                    token.span.start..token.span.end,
                )])
                .with_notes(vec![String::from(
                    "A right-hand-side expression is required after this prefix operator.",
                )]),
            AstParseError::IfExpectedCurlyOpen { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("expected `{` after if condition"),
                ])
                .with_notes(vec![String::from("Use `{ ... }` to start the `if` body.")]),
            AstParseError::IfExpectedCondition { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("expected condition expression here"),
                ])
                .with_notes(vec![String::from(
                    "Provide a boolean expression after `if`.",
                )]),
            AstParseError::UnexpectedTokenInExpr { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("unexpected token in expression"),
                ]),
            AstParseError::ExpectedOperator { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("expected operator here"),
                ])
                .with_notes(vec![String::from(
                    "Binary operators like `+`, `-`, `*`, `/` are expected here.",
                )]),
            AstParseError::UnexpectedEndOfInput => {
                Diagnostic::error().with_message("Unexpected end of input")
            }
            AstParseError::InvalidAssignmentTarget { span } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, span.start..span.end)
                        .with_message("cannot assign to this expression"),
                ])
                .with_notes(vec![String::from(
                    "Only variables, array elements, and struct fields can be assigned to.",
                )]),
            AstParseError::TypeParse(type_parse_error) => type_parse_error.to_diagnostic(file_id),
            AstParseError::LetExpectedIdent { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("expected identifier here"),
                ])
                .with_notes(vec![String::from(
                    "Variable declarations require a name, e.g. `let x = 5;`.",
                )]),
            AstParseError::EnumExpectedClosingBracket { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("expected `)` here"),
                ])
                .with_notes(vec![String::from(
                    "Enum variant types must be closed with `)`, e.g. `Variant(I32)`.",
                )]),
            AstParseError::EnumUnexpectedTokenAfterVariant { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("unexpected token here"),
                ])
                .with_notes(vec![String::from(
                    "Expected `,` to add another variant or `}` to close the enum definition.",
                )]),
            AstParseError::EnumUnexpectedToken { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("unexpected token in enum body"),
                ])
                .with_notes(vec![String::from(
                    "Expected a variant name, `,`, or `}` inside enum definition.",
                )]),
            AstParseError::StructCreateExpectedColon { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("expected `:` here"),
                ])
                .with_notes(vec![String::from(
                    "Struct fields are initialized with `field_name: value`, e.g. `Foo { x: 5 }`.",
                )]),
            AstParseError::ExternFnExpectedSemiColon { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("expected `;` here"),
                ])
                .with_notes(vec![String::from(
                    "Extern function declarations must end with `;`, e.g. `fn printf(fmt: CStr);`.",
                )]),
        }
    }
}

#[derive(Error, Debug)]
pub enum TypeParseError {
    #[error("Unexpected end of input")]
    UnexpectedEndOfInput,

    #[error("Expected `;` after [Type")]
    ArrayExpectedSemiColonAfterType { token: Token },

    #[error("Expected integer after [Type;")]
    ArrayExpectedIntAfterType { token: Token },

    #[error("Expected `]` after [Type; size")]
    ArrayExpectedClose { token: Token },

    #[error("Expected type decleration")]
    NotTypeToken { token: Token },
}
impl ToDiagnostic for TypeParseError {
    fn to_diagnostic(&self, file_id: usize) -> Diagnostic<usize> {
        match self {
            TypeParseError::UnexpectedEndOfInput => {
                Diagnostic::error().with_message("Unexpected end of input")
            }
            TypeParseError::ArrayExpectedSemiColonAfterType { token } => Diagnostic::error()
                .with_message(self.to_string())
                .with_labels(vec![
                    Label::primary(file_id, token.span.start..token.span.end)
                        .with_message("Expected `;` here instead"),
                ])
                .with_notes(vec![String::from("Arrays are defined like this [I32; 5]")]),
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
