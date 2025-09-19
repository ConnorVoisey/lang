use crate::{
    ast::{Ast, ast_expr::AstExpr},
    interner::IdentId,
    lexer::{Token, TokenKind},
    symbols::{SymbolId, SymbolKind, SymbolTable},
    types::TypeId,
};

#[derive(Debug)]
pub struct AstBlock {
    pub block_open_token_at: usize,
    pub block_close_token_at: usize,
    pub statements: Vec<AstStatement>,
    pub type_id: Option<TypeId>,
}
#[derive(Debug)]
pub enum StatementKind {
    Decleration {
        symbol_id: SymbolId,
        ident_id: IdentId,
        ident_token_at: usize,
        expr: AstExpr,
    },
    Assignment {
        ident_id: IdentId,
        ident_token_at: usize,
        expr: AstExpr,
    },
    Expr(AstExpr),
    ExplicitReturn(AstExpr),
    BlockReturn(AstExpr),
}
#[derive(Debug)]
pub struct AstStatement {
    pub start_token_at: usize,
    pub kind: StatementKind,
}

impl Ast {
    pub fn parse_block(&mut self, symbols: &mut SymbolTable) -> Option<AstBlock> {
        assert!(
            matches!(
                self.curr_token(),
                Some(Token {
                    kind: TokenKind::CurlyBracketOpen,
                    ..
                })
            ),
            "Called parsed block not on a `{{`"
        );
        let block_open_token_at = self.curr_token_i();
        let mut statements = vec![];
        while let Some(tok) = self.next_token() {
            match &tok.kind {
                TokenKind::CurlyBracketClose => {
                    break;
                }
                _ => {
                    if let Some(statement) = self.parse_statement(symbols) {
                        let need_break =
                            matches!(&statement.kind, StatementKind::BlockReturn(_));
                        statements.push(statement);
                        if need_break {
                            break;
                        }
                    }
                }
            };
        }

        Some(AstBlock {
            block_open_token_at,
            block_close_token_at: self.curr_token_i(),
            statements,
            type_id: None,
        })
    }

    pub fn parse_statement(&mut self, symbols: &mut SymbolTable) -> Option<AstStatement> {
        let start_token_at = self.curr_token_i();
        match self.curr_token() {
            Some(Token {
                kind: TokenKind::LetKeyWord,
                ..
            }) => {
                let ident_id = *match self.next_token() {
                    Some(Token {
                        kind: TokenKind::Ident(ident_id),
                        ..
                    }) => ident_id,
                    t => {
                        dbg!(t);
                        todo!();
                    }
                };
                let symbol_id = symbols.declare(
                    ident_id,
                    SymbolKind::Var {
                        type_id: None,
                        is_used: false,
                        is_mutable: false,
                    },
                );
                assert!(
                    matches!(
                        self.next_token(),
                        Some(Token {
                            kind: TokenKind::Assign,
                            ..
                        })
                    ),
                    "Attempted to define a variable but missed the `=` after the ident"
                );
                self.next_token();
                Some(AstStatement {
                    start_token_at,
                    kind: StatementKind::Decleration {
                        ident_id,
                        symbol_id,
                        ident_token_at: start_token_at + 1,
                        expr: self.parse_expr(0, symbols)?,
                    },
                })
            }
            Some(Token {
                kind: TokenKind::ReturnKeyWord,
                ..
            }) => {
                self.next_token();
                Some(AstStatement {
                    start_token_at,
                    kind: StatementKind::ExplicitReturn(self.parse_expr(0, symbols)?),
                })
            }
            None => {
                panic!("Unexpected end of input in parse_statement");
            }
            _ => {
                let start_token_at = self.curr_token_i();
                let expr = self.parse_expr(0, symbols)?;
                Some(AstStatement {
                    start_token_at,
                    kind: match self.curr_token() {
                        Some(Token {
                            kind: TokenKind::CurlyBracketClose,
                            ..
                        }) => StatementKind::BlockReturn(expr),
                        _ => StatementKind::Expr(expr),
                    },
                })
            }
        }
    }
}
