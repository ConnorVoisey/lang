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
    pub fn parse_func_call(
        &mut self,
        symbols: &mut SymbolTable,
        start_token_at: usize,
        lhs: AstExpr,
    ) -> Option<AstExpr> {
        debug_assert!(
            matches!(
                self.tokens.get(self.curr_token_i() - 1),
                Some(Token {
                    kind: TokenKind::BracketOpen,
                    ..
                })
            ),
            "Called parse_func_call not on a `(` {:?}",
            self.curr_token()
        );

        let mut args = vec![];

        // empty arg list: immediate ')'
        if let Some(Token {
            kind: TokenKind::BracketClose,
            ..
        }) = self.curr_token()
        {
            self.next_token(); // consume ')'
            return Some(AstExpr {
                span: Span {
                    start: self.tokens[start_token_at].span.start,
                    end: self.tokens[self.curr_token_i()].span.end,
                },
                kind: ExprKind::Op(Box::new(Op::FnCall { ident: lhs, args })),
                type_id: None,
            });
        }

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
                    kind: TokenKind::BracketClose,
                    ..
                }) => break,
                Some(tok) => {
                    self.errs
                        .push(AstParseError::ExpectedClosingBracket { token: tok.clone() });
                    break;
                }
                None => {
                    self.errs.push(AstParseError::UnexpectedEndOfInput);
                    return None;
                }
            };
        }

        // consume ')'
        if matches!(
            self.curr_token(),
            Some(Token {
                kind: TokenKind::BracketClose,
                ..
            })
        ) {
            self.next_token();
        } else {
            // error already recorded
        }

        Some(AstExpr {
            span: Span {
                start: self.tokens[start_token_at].span.start,
                end: self.tokens[self.curr_token_i()].span.end,
            },
            kind: ExprKind::Op(Box::new(Op::FnCall { ident: lhs, args })),
            type_id: None,
        })
    }
}

#[cfg(test)]
mod test {
    use crate::ast::ast_expr::debug::{DebugAtom, DebugExprKind, DebugOp, parse_debug};
    use pretty_assertions::assert_eq;

    #[test]
    fn fn_call() {
        let debug_expr = parse_debug("foo(bar) + 5;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Add {
            left: DebugExprKind::Op(Box::new(DebugOp::FnCall {
                ident: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
                args: vec![DebugExprKind::Atom(DebugAtom::Ident("bar".to_string()))],
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(5)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn fn_call_multi_param() {
        let debug_expr = parse_debug("foo(bar, baz, 5);");
        let expected = DebugExprKind::Op(Box::new(DebugOp::FnCall {
            ident: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
            args: vec![
                DebugExprKind::Atom(DebugAtom::Ident("bar".to_string())),
                DebugExprKind::Atom(DebugAtom::Ident("baz".to_string())),
                DebugExprKind::Atom(DebugAtom::Int(5)),
            ],
        }));
        assert_eq!(debug_expr, expected);
    }
    #[test]
    fn nested_fn_calls() {
        let debug_expr = parse_debug("foo(bar(baz), 1);");
        let expected = DebugExprKind::Op(Box::new(DebugOp::FnCall {
            ident: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
            args: vec![
                DebugExprKind::Op(Box::new(DebugOp::FnCall {
                    ident: DebugExprKind::Atom(DebugAtom::Ident("bar".to_string())),
                    args: vec![DebugExprKind::Atom(DebugAtom::Ident("baz".to_string()))],
                })),
                DebugExprKind::Atom(DebugAtom::Int(1)),
            ],
        }));
        assert_eq!(debug_expr, expected);
    }
}
