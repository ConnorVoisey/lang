use crate::{
    ast::{Ast, ast_expr::AstExpr},
    interner::IdentId,
    lexer::{Token, TokenKind},
    symbols::SymbolId,
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
        symbol_id: Option<SymbolId>,
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
    Return(AstExpr),
}
#[derive(Debug)]
pub struct AstStatement {
    pub start_token_at: usize,
    pub kind: StatementKind,
}

impl Ast {
    pub fn parse_block(&mut self) -> Option<AstBlock> {
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
                    if let Some(statement) = self.parse_statement() {
                        statements.push(statement);
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

    pub fn parse_statement(&mut self) -> Option<AstStatement> {
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
                Some(AstStatement {
                    start_token_at,
                    kind: StatementKind::Decleration {
                        ident_id,
                        symbol_id: None,
                        ident_token_at: start_token_at + 1,
                        expr: self.parse_expr(0)?,
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
                    kind: StatementKind::Return(self.parse_expr(0)?),
                })
            }
            None => {
                panic!("Unexpected end of input in parse_statement");
            }
            _ => {
                let start_token_at = self.curr_token_i();
                Some(AstStatement {
                    start_token_at,
                    kind: StatementKind::Expr(self.parse_expr(0)?),
                })
            }
        }
    }
}
