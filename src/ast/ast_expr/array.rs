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
    pub fn parse_array_expr(
        &mut self,
        min_bp: u8,
        symbols: &mut SymbolTable,
        is_direct_if_cond: bool,
    ) -> Option<AstExpr> {
        debug_assert!(
            matches!(
                self.curr_token(),
                Some(Token {
                    kind: TokenKind::SquareBracketOpen,
                    ..
                })
            ),
            "Called parse_array_expr not on a `[` {:?}",
            self.curr_token()
        );
        let start_i = self.curr_token().unwrap().span.start;
        self.next_token();

        let args = if let Some(Token {
            kind: TokenKind::SquareBracketClose,
            ..
        }) = self.peek_token()
        {
            Vec::new()
        } else {
            let mut args = Vec::new();
            loop {
                if let Some(arg) = self.parse_expr(0, symbols, false) {
                    args.push(arg);
                } else {
                    // parse_expr pushed an error; attempt to continue
                }
                match self.curr_token() {
                    Some(Token {
                        kind: TokenKind::Comma,
                        ..
                    }) => {
                        self.next_token(); // consume comma, continue parsing args
                        continue;
                    }
                    Some(Token {
                        kind: TokenKind::SquareBracketClose,
                        ..
                    }) => break,
                    Some(tok) => {
                        self.errs.push(AstParseError::ExpectedClosingSquareBracket {
                            token: tok.clone(),
                        });
                        break;
                    }
                    None => {
                        self.errs.push(AstParseError::UnexpectedEndOfInput);
                        return None;
                    }
                };
            }
            args
        };

        Some(AstExpr {
            span: Span {
                start: start_i,
                end: self.curr_token().unwrap().span.end,
            },
            type_id: None,
            kind: ExprKind::Op(Box::new(Op::ArrayInit { args })),
        })
    }
}
