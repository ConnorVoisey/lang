use crate::{
    ast::{Ast, VarType, ast_block::AstBlock, error::AstParseError},
    interner::IdentId,
    lexer::{Span, Token, TokenKind},
    symbols::{SymbolId, SymbolKind, SymbolTable},
};

#[derive(Debug)]
pub struct AstFnArg {
    pub ident_id: IdentId,
    pub var_type: VarType,
    pub symbol_id: SymbolId,
}

#[derive(Debug)]
pub struct AstFunc {
    pub fn_token_at: usize,
    pub ident_id: IdentId,
    pub symbol_id: SymbolId,
    pub args: Vec<AstFnArg>,
    pub return_type: VarType,
    pub return_type_span: Span,
    pub body: Option<AstBlock>,
}

impl Ast {
    pub fn parse_fn_dec(&mut self, symbols: &mut SymbolTable) -> Option<AstFunc> {
        let start_token_i = self.curr_token_i();
        debug_assert!(
            matches!(
                self.curr_token(),
                Some(Token {
                    kind: TokenKind::FnKeyWord,
                    ..
                })
            ),
            "Called parsed fn dec not on an fn key word"
        );

        let fn_token_at = self.curr_token_i();
        // expect ident as fn name
        let ident_id = *match self.next_token() {
            Some(Token {
                kind: TokenKind::Ident(ident_id),
                ..
            }) => ident_id,
            Some(token) => {
                let cloned_token = token.clone();
                self.errs
                    .push(AstParseError::ExportExpectedCurlyBracketOpen {
                        token: cloned_token,
                    });
                return None;
            }
            None => {
                self.errs.push(AstParseError::UnexpectedEndOfInput);
                return None;
            }
        };
        if symbols.lookup(ident_id).is_some() {
            self.errs.push(AstParseError::FnDuplicateStructNames {
                token: self.curr_token().unwrap().clone(),
                name: self.interner.read().resolve(ident_id).to_string(),
            });
        }

        // expect `(`
        match self.next_token() {
            Some(Token {
                kind: TokenKind::BracketOpen,
                ..
            }) => (),
            Some(token) => {
                let t = token.clone();
                self.errs
                    .push(AstParseError::FnExpectedParenOpen { token: t });
                return None;
            }
            None => {
                self.errs.push(AstParseError::UnexpectedEndOfInput);
                return None;
            }
        };

        // TODO: parse fn body, call fn self.parse_block or self.parse_fn_body
        let args = self.parse_fn_args(symbols);
        let (return_type, return_type_span) = self.parse_var_type();

        let fn_name_span = self.tokens[start_token_i + 1].span.clone();
        let full_signature_span = Span {
            start: self.tokens[start_token_i].span.start,
            end: self.tokens[self.curr_token_i()].span.end,
        };

        Some(AstFunc {
            fn_token_at,
            ident_id,
            symbol_id: symbols.declare(
                ident_id,
                SymbolKind::Fn(crate::symbols::FnSymbolData {
                    fn_type_id: None,
                    return_type_id: None,
                    return_type_span: return_type_span.clone(),
                    full_signature_span,
                }),
                fn_name_span,
            ),
            args,
            return_type,
            return_type_span,
            body: None,
        })
    }

    pub fn parse_fn_args(&mut self, symbols: &mut SymbolTable) -> Vec<AstFnArg> {
        debug_assert!(
            matches!(
                self.curr_token(),
                Some(Token {
                    kind: TokenKind::BracketOpen,
                    ..
                })
            ),
            "Called parsed fn args not on an `(`"
        );

        let mut args = vec![];
        loop {
            match self.next_token() {
                Some(Token {
                    kind: TokenKind::Ident(id),
                    span: ident_span,
                }) => {
                    let ident_id = *id;
                    let ident_span = ident_span.clone();
                    let (var_type, type_span) = self.parse_var_type();
                    args.push(AstFnArg {
                        ident_id,
                        symbol_id: symbols.declare(
                            ident_id,
                            SymbolKind::FnArg(crate::symbols::FnArgSymbolData {
                                type_id: None,
                                is_used: false,
                                is_mutable: false,
                                type_span,
                            }),
                            ident_span.clone(),
                        ),
                        var_type,
                    });
                    match self.peek_token() {
                        Some(Token {
                            kind: TokenKind::Comma,
                            ..
                        }) => {
                            self.next_token();
                        }
                        Some(Token {
                            kind: TokenKind::BracketClose,
                            ..
                        }) => (),
                        Some(token) => {
                            let t = token.clone();
                            self.errs
                                .push(AstParseError::FnExpectedCommaOrClose { token: t });
                            return args;
                        }
                        None => {
                            self.errs.push(AstParseError::UnexpectedEndOfInput);
                            return args;
                        }
                    }
                }
                Some(Token {
                    kind: TokenKind::BracketClose,
                    ..
                }) => {
                    return args;
                }

                Some(token) => {
                    let t = token.clone();
                    self.errs
                        .push(AstParseError::FnExpectedParamOrClose { token: t });
                    return args;
                }

                None => {
                    return args;
                }
            }
        }
    }
    pub fn parse_fn(&mut self, symbols: &mut SymbolTable) {
        debug_assert!(
            matches!(
                self.curr_token(),
                Some(Token {
                    kind: TokenKind::FnKeyWord,
                    ..
                })
            ),
            "Called parsed fn not on a fnKeyWord"
        );

        let mut fn_dec = match self.parse_fn_dec(symbols) {
            Some(v) => v,
            None => {
                return;
            }
        };

        self.next_token();
        fn_dec.body = self.parse_block(symbols, true);
        self.fns.push(fn_dec);
    }
}
