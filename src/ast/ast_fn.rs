use crate::{
    ast::{Ast, VarType, ast_block::AstBlock, error::AstParseError},
    interner::IdentId,
    lexer::{Token, TokenKind},
    symbols::{SymbolId, SymbolKind, SymbolTable},
    types::TypeId,
};

#[derive(Debug)]
pub struct AstFnArg {
    pub ident_id: IdentId,
    pub var_type: VarType,
    pub type_id: Option<TypeId>,
    pub symbol_id: SymbolId,
}

#[derive(Debug)]
pub struct AstFunc {
    pub fn_token_at: usize,
    pub ident_id: IdentId,
    pub symbol_id: SymbolId,
    pub type_id: Option<TypeId>,
    pub args: Vec<AstFnArg>,
    pub return_type: VarType,
    pub return_type_id: Option<TypeId>,
    pub body: Option<AstBlock>,
}

impl Ast {
    pub fn parse_fn_dec(&mut self, symbols: &mut SymbolTable) -> Option<AstFunc> {
        assert!(
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
            Some(t) => {
                dbg!(t);
                todo!();
            }
            None => {
                self.errs.push(AstParseError::UnexpectedEndOfInput);
                return None;
            }
        };

        // TODO: parse fn body, call fn self.parse_block or self.parse_fn_body
        let args = self.parse_fn_args(symbols);
        let return_type = self.parse_var_type();

        Some(AstFunc {
            fn_token_at,
            ident_id,
            symbol_id: symbols.declare(
                ident_id,
                SymbolKind::Fn {
                    fn_type_id: None,
                    param_type_ids: vec![],
                    return_type_id: None,
                },
            ),
            type_id: None,
            args,
            return_type,
            return_type_id: None,
            body: None,
        })
    }

    pub fn parse_fn_args(&mut self, symbols: &mut SymbolTable) -> Vec<AstFnArg> {
        assert!(
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
                    ..
                }) => {
                    let ident_id = *id;
                    let var_type = self.parse_var_type();
                    args.push(AstFnArg {
                        ident_id,
                        symbol_id: symbols.declare(
                            ident_id,
                            SymbolKind::FnArg {
                                type_id: None,
                                is_used: false,
                                is_mutable: false,
                            },
                        ),
                        var_type,
                        type_id: None,
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
                        t => {
                            dbg!(t);
                            todo!("expected more either `,` or `)`")
                        }
                    }
                }
                Some(Token {
                    kind: TokenKind::BracketClose,
                    ..
                }) => {
                    return args;
                }
                Some(t) => {
                    dbg!(t);
                    todo!();
                }
                None => {
                    return args;
                }
            }
        }
    }
    pub fn parse_fn(&mut self, symbols: &mut SymbolTable) {
        assert!(
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
                panic!("Failed to get fn_dec");
            }
        };

        self.next_token();
        fn_dec.body = self.parse_block(symbols);
        self.fns.push(fn_dec);
    }
}
