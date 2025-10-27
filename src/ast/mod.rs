use crate::{
    ast::{ast_fn::AstFunc, ast_struct::AstStruct, error::AstParseError},
    error::CompliationError,
    interner::{IdentId, SharedInterner},
    lexer::{Span, Token, TokenKind},
    symbols::{SymbolId, SymbolTable},
};

pub mod ast_block;
pub mod ast_expr;
pub mod ast_fn;
pub mod ast_import;
pub mod ast_struct;
pub mod error;

#[derive(Debug, Clone, PartialEq)]
pub enum VarType {
    Void,
    Bool,
    Int,
    Uint,
    Str,
    CStr,
    CChar,
    Array {
        var_type: Box<VarType>,
        count: usize,
    },
    Custom((IdentId, Option<SymbolId>)),
    Ref(Box<VarType>),
}

#[derive(Debug)]
pub struct Ast {
    pub errs: Vec<AstParseError>,
    pub imports: Vec<String>,
    pub fns: Vec<AstFunc>,
    pub extern_fns: Vec<AstFunc>,
    pub structs: Vec<AstStruct>,
    pub tokens: Vec<Token>,
    pub next_token_i: usize,
    pub interner: SharedInterner,
}

impl Ast {
    fn curr_token_i(&self) -> usize {
        self.next_token_i - 1
    }
    fn curr_token(&self) -> Option<&Token> {
        self.tokens.get(self.curr_token_i())
    }
    fn next_token(&mut self) -> Option<&Token> {
        let token = self.tokens.get(self.next_token_i);
        self.next_token_i += 1;
        token
    }

    fn peek_token(&self) -> Option<&Token> {
        self.tokens.get(self.next_token_i)
    }
    fn peek_n_token(&self, amount: usize) -> Option<&Token> {
        self.tokens.get(self.next_token_i + amount - 1)
    }
    fn skip_past_semi(&mut self) {
        while let Some(token) = self.next_token() {
            if let TokenKind::SemiColon = token.kind {
                return;
            }
        }
    }

    fn parse_extern_block(&mut self, symbols: &mut SymbolTable) {
        debug_assert!(
            matches!(
                self.curr_token(),
                Some(Token {
                    kind: TokenKind::ExternKeyWord,
                    ..
                })
            ),
            "Called parsed extern block not on an extern key word"
        );

        // expect `"C"`
        match self.next_token() {
            Some(Token {
                kind: TokenKind::Str(str_val),
                ..
            }) if str_val == "C" => (),
            Some(token) => {
                let cloned_token = token.clone();
                self.errs.push(AstParseError::ExportExpectedStrC {
                    token: cloned_token,
                });
                return;
            }
            None => {
                self.errs.push(AstParseError::UnexpectedEndOfInput);
                return;
            }
        };

        // expect `{`
        match self.next_token() {
            Some(Token {
                kind: TokenKind::CurlyBracketOpen,
                ..
            }) => (),
            Some(token) => {
                let cloned_token = token.clone();
                self.errs
                    .push(AstParseError::ExportExpectedCurlyBracketOpen {
                        token: cloned_token,
                    });
                return;
            }
            None => {
                self.errs.push(AstParseError::UnexpectedEndOfInput);
                return;
            }
        };

        // started parsing the exports, expect `}` or fn key word
        while let Some(token) = self.next_token() {
            match &token.kind {
                TokenKind::FnKeyWord => {
                    let fn_dec = self.parse_fn_dec(symbols);
                    match self.next_token() {
                        Some(Token {
                            kind: TokenKind::SemiColon,
                            ..
                        }) => (),
                        t => {
                            dbg!(t);
                            panic!("Expected `;` after extern c func def");
                        }
                    }
                    if let Some(func) = fn_dec {
                        self.extern_fns.push(func);
                    }
                }
                TokenKind::CurlyBracketClose => break,
                _ => {
                    let cloned_token = token.clone();
                    self.errs.push(AstParseError::ImportExpectedStrOrClose {
                        token: cloned_token,
                    });
                    return;
                }
            }
        }
    }

    fn parse_var_type(&mut self) -> (VarType, Span) {
        match self.next_token() {
            Some(Token {
                kind: TokenKind::SquareBracketOpen,
                span,
            }) => {
                let span_cloned = span.clone();
                let (inner_type, inner_span) = self.parse_var_type();

                if let Some(Token {
                    kind: TokenKind::SemiColon,
                    ..
                }) = self.peek_token()
                {
                } else {
                    todo!("add diagnostics, expected semi colon after [expr")
                }
                self.next_token();

                let count = if let Some(Token {
                    kind: TokenKind::Int(int_val),
                    ..
                }) = self.next_token()
                {
                    int_val.clone()
                } else {
                    todo!("add diagnostics, expected int after [I32;")
                };

                if let Some(Token {
                    kind: TokenKind::SquareBracketClose,
                    ..
                }) = self.next_token()
                {
                } else {
                    todo!("add diagnostics, expected ] after [I32; 5")
                };
                (
                    VarType::Array {
                        var_type: Box::new(inner_type),
                        count: count as usize,
                    },
                    Span {
                        start: span_cloned.start,
                        end: inner_span.end,
                    },
                )
            }
            Some(Token {
                kind: TokenKind::Amp,
                span,
            }) => {
                let span_cloned = span.clone();
                let (inner_type, inner_span) = self.parse_var_type();
                (
                    VarType::Ref(Box::new(inner_type)),
                    Span {
                        start: span_cloned.start,
                        end: inner_span.end,
                    },
                )
            }
            Some(Token {
                kind: TokenKind::Ident(ident_id),
                span,
            }) => {
                let ident_cloned = ident_id.clone();
                let ident_cloned_2 = ident_cloned.clone();
                let span_cloned = span.clone();
                let var_type = match self.interner.read().resolve(ident_cloned) {
                    "Int" => VarType::Int,
                    "Uint" => VarType::Uint,
                    "Str" => VarType::Str,
                    "CStr" => VarType::CStr,
                    "CChar" => VarType::CChar,
                    "Bool" => VarType::Bool,
                    _ => VarType::Custom((ident_cloned_2, None)),
                };
                (var_type, span_cloned)
            }
            Some(t) => {
                dbg!(t);
                todo!()
            }
            None => todo!(),
        }
    }

    pub fn from_tokens(
        tokens: Vec<Token>,
        interner: SharedInterner,
        symbols: &mut SymbolTable,
    ) -> Result<Self, CompliationError> {
        let mut ast = Self::new(tokens, interner);
        while let Some(token) = ast.next_token() {
            match &token.kind {
                TokenKind::ImportKeyWord => {
                    ast.parse_imports();
                }
                TokenKind::ExternKeyWord => {
                    ast.parse_extern_block(symbols);
                }
                TokenKind::StructKeyWord => {
                    ast.parse_struct(symbols);
                }
                TokenKind::FnKeyWord => {
                    ast.parse_fn(symbols);
                }
                _ => {
                    let token_clone = token.clone();
                    ast.errs
                        .push(AstParseError::UnhandledToken { token: token_clone });
                    ast.skip_past_semi();
                    continue;
                }
            };
        }

        Ok(ast)
    }

    pub fn new(tokens: Vec<Token>, interner: SharedInterner) -> Self {
        Self {
            errs: vec![],
            imports: vec![],
            fns: vec![],
            extern_fns: vec![],
            structs: vec![],
            tokens,
            next_token_i: 0,
            interner,
        }
    }
}
