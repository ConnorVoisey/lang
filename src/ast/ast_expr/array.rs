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
    pub fn parse_array_expr(&mut self, symbols: &mut SymbolTable) -> Option<AstExpr> {
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
        let mut expr_count = 1;

        let args = if let Some(Token {
            kind: TokenKind::SquareBracketClose,
            ..
        }) = self.curr_token()
        {
            Vec::new()
        } else {
            let mut args = Vec::new();
            loop {
                if let Some(arg) = self.parse_expr(0, symbols, false) {
                    expr_count += arg.expr_count;
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
            expr_count,
            kind: ExprKind::Op(Box::new(Op::ArrayInit { args })),
        })
    }

    pub fn parse_array_access(
        &mut self,
        symbols: &mut SymbolTable,
        start_token_at: usize,
        lhs: AstExpr,
    ) -> Option<AstExpr> {
        debug_assert!(
            matches!(
                self.tokens.get(self.curr_token_i() - 1),
                Some(Token {
                    kind: TokenKind::SquareBracketOpen,
                    ..
                })
            ),
            "Called parse_array_access not on a `[` {:?}",
            self.curr_token()
        );
        let right = self.parse_expr(0, symbols, false)?;
        if !matches!(
            self.curr_token(),
            Some(Token {
                kind: TokenKind::SquareBracketClose,
                ..
            })
        ) {
            todo!("handle error, array access not closed")
        }
        self.next_token();
        Some(AstExpr {
            span: Span {
                start: self.tokens[start_token_at].span.start,
                end: self.tokens[self.curr_token_i()].span.end,
            },
            expr_count: lhs.expr_count + 1 + right.expr_count,
            kind: ExprKind::Op(Box::new(Op::ArrayAccess { left: lhs, right })),
            type_id: None,
        })
    }
}

#[cfg(test)]
mod test {
    use crate::ast::ast_expr::debug::{DebugAtom, DebugExprKind, DebugOp, parse_debug};
    use pretty_assertions::assert_eq;

    // ===== Array Initialization Tests =====

    #[test]
    fn empty_array() {
        let debug_expr = parse_debug("[];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayInit { args: vec![] }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn single_element_array() {
        let debug_expr = parse_debug("[1];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayInit {
            args: vec![DebugExprKind::Atom(DebugAtom::Int(1))],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn multiple_elements() {
        let debug_expr = parse_debug("[1, 2, 3, 4];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayInit {
            args: vec![
                DebugExprKind::Atom(DebugAtom::Int(1)),
                DebugExprKind::Atom(DebugAtom::Int(2)),
                DebugExprKind::Atom(DebugAtom::Int(3)),
                DebugExprKind::Atom(DebugAtom::Int(4)),
            ],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn array_with_expressions() {
        let debug_expr = parse_debug("[1 + 2, 3 * 4];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayInit {
            args: vec![
                DebugExprKind::Op(Box::new(DebugOp::Add {
                    left: DebugExprKind::Atom(DebugAtom::Int(1)),
                    right: DebugExprKind::Atom(DebugAtom::Int(2)),
                })),
                DebugExprKind::Op(Box::new(DebugOp::Multiply {
                    left: DebugExprKind::Atom(DebugAtom::Int(3)),
                    right: DebugExprKind::Atom(DebugAtom::Int(4)),
                })),
            ],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn array_with_identifiers() {
        let debug_expr = parse_debug("[foo, bar, baz];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayInit {
            args: vec![
                DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
                DebugExprKind::Atom(DebugAtom::Ident("bar".to_string())),
                DebugExprKind::Atom(DebugAtom::Ident("baz".to_string())),
            ],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn array_trailing_comma() {
        let debug_expr = parse_debug("[1, 2,];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayInit {
            args: vec![
                DebugExprKind::Atom(DebugAtom::Int(1)),
                DebugExprKind::Atom(DebugAtom::Int(2)),
            ],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn nested_arrays() {
        let debug_expr = parse_debug("[[1, 2], [3, 4]];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayInit {
            args: vec![
                DebugExprKind::Op(Box::new(DebugOp::ArrayInit {
                    args: vec![
                        DebugExprKind::Atom(DebugAtom::Int(1)),
                        DebugExprKind::Atom(DebugAtom::Int(2)),
                    ],
                })),
                DebugExprKind::Op(Box::new(DebugOp::ArrayInit {
                    args: vec![
                        DebugExprKind::Atom(DebugAtom::Int(3)),
                        DebugExprKind::Atom(DebugAtom::Int(4)),
                    ],
                })),
            ],
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Array Access Tests =====

    #[test]
    fn simple_access() {
        let debug_expr = parse_debug("arr[0];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
            left: DebugExprKind::Atom(DebugAtom::Ident("arr".to_string())),
            right: DebugExprKind::Atom(DebugAtom::Int(0)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn access_with_expression() {
        let debug_expr = parse_debug("arr[1 + 2];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
            left: DebugExprKind::Atom(DebugAtom::Ident("arr".to_string())),
            right: DebugExprKind::Op(Box::new(DebugOp::Add {
                left: DebugExprKind::Atom(DebugAtom::Int(1)),
                right: DebugExprKind::Atom(DebugAtom::Int(2)),
            })),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn access_with_identifier() {
        let debug_expr = parse_debug("arr[idx];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
            left: DebugExprKind::Atom(DebugAtom::Ident("arr".to_string())),
            right: DebugExprKind::Atom(DebugAtom::Ident("idx".to_string())),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn chained_access() {
        let debug_expr = parse_debug("arr[0][1];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
            left: DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
                left: DebugExprKind::Atom(DebugAtom::Ident("arr".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Int(0)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(1)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn array_init_then_access() {
        let debug_expr = parse_debug("[1, 2, 3][0];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
            left: DebugExprKind::Op(Box::new(DebugOp::ArrayInit {
                args: vec![
                    DebugExprKind::Atom(DebugAtom::Int(1)),
                    DebugExprKind::Atom(DebugAtom::Int(2)),
                    DebugExprKind::Atom(DebugAtom::Int(3)),
                ],
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(0)),
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Integration Tests =====

    #[test]
    fn array_access_in_arithmetic() {
        let debug_expr = parse_debug("arr[0] + 5;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Add {
            left: DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
                left: DebugExprKind::Atom(DebugAtom::Ident("arr".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Int(0)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(5)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn function_return_array_access() {
        let debug_expr = parse_debug("get_array()[0];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
            left: DebugExprKind::Op(Box::new(DebugOp::FnCall {
                ident: DebugExprKind::Atom(DebugAtom::Ident("get_array".to_string())),
                args: vec![],
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(0)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn struct_field_array_access() {
        let debug_expr = parse_debug("obj.arr[0];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
            left: DebugExprKind::Op(Box::new(DebugOp::Dot {
                left: DebugExprKind::Atom(DebugAtom::Ident("obj".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Ident("arr".to_string())),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(0)),
        }));
        assert_eq!(debug_expr, expected);
    }
}
