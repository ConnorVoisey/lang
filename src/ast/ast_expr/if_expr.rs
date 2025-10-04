use crate::{
    ast::{
        Ast,
        ast_expr::{AstExpr, ExprKind, Op},
        error::AstParseError,
    },
    lexer::{Span, Token, TokenKind},
    symbols::SymbolTable,
};

impl Ast {
    pub fn parse_if_expr(
        &mut self,
        symbols: &mut SymbolTable,
        cur_token: &Token,
        start_token_at: usize,
    ) -> Option<AstExpr> {
        self.next_token();
        let condition = match self.parse_expr(0, symbols) {
            Some(c) => c,
            None => {
                let tok = self.curr_token().cloned().unwrap_or(cur_token.clone());
                self.errs
                    .push(AstParseError::IfExpectedCondition { token: tok });
                return None;
            }
        };

        // expect '{'
        match self.curr_token() {
            Some(Token {
                kind: TokenKind::CurlyBracketOpen,
                ..
            }) => { /* okay - parse_block will consume it */ }
            Some(tok) => {
                self.errs
                    .push(AstParseError::IfExpectedCurlyOpen { token: tok.clone() });
                // try to continue; parse_block may fail and add more errors
            }
            None => {
                self.errs.push(AstParseError::UnexpectedEndOfInput);
                return None;
            }
        }

        let block = match self.parse_block(symbols, false) {
            Some(b) => b,
            None => {
                // parse_block will have pushed errors already
                return None;
            }
        };

        let mut else_ifs = vec![];
        let mut unconditional_else = None;
        while let Some(token) = self.peek_token() {
            match token {
                Token {
                    kind: TokenKind::ElseKeyWord,
                    ..
                } => {
                    self.next_token(); // consume 'else'
                    match self.peek_token() {
                        Some(Token {
                            kind: TokenKind::IfKeyWord,
                            ..
                        }) => {
                            // else if
                            self.next_token(); // consume 'if'
                            match self.parse_expr(0, symbols) {
                                Some(cond) => {
                                    let blk = match self.parse_block(symbols, false) {
                                        Some(b) => b,
                                        None => {
                                            // parse_block pushed errors
                                            break;
                                        }
                                    };
                                    else_ifs.push((cond, blk));
                                }
                                None => {
                                    // parse_expr pushed an error
                                    break;
                                }
                            }
                        }
                        Some(Token {
                            kind: TokenKind::CurlyBracketOpen,
                            ..
                        }) => {
                            self.next_token(); // consume '{'
                            unconditional_else = self.parse_block(symbols, false);
                        }
                        _ => {
                            // unexpected token after else — record and stop
                            if let Some(tok) = self.peek_token().cloned() {
                                self.errs
                                    .push(AstParseError::UnexpectedTokenInExpr { token: tok });
                            }
                            break;
                        }
                    }
                }
                _ => break,
            }
        }

        Some(AstExpr {
            span: Span {
                start: self.tokens[start_token_at].span.start,
                end: self.tokens[self.curr_token_i()].span.end,
            },
            kind: ExprKind::Op(Box::new(Op::IfCond {
                condition,
                block,
                else_ifs,
                unconditional_else,
            })),
            type_id: None,
        })
    }
}
