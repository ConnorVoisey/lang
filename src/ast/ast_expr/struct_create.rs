use crate::{
    ast::{
        Ast,
        ast_expr::{AstExpr, ExprKind, Op},
    },
    lexer::{Span, Token, TokenKind},
    symbols::SymbolTable,
};

impl Ast {
    pub fn parse_struct_create(
        &mut self,
        symbols: &mut SymbolTable,
        start_token_at: usize,
        lhs: AstExpr,
    ) -> Option<AstExpr> {
        debug_assert!(
            matches!(
                self.tokens.get(self.curr_token_i() - 1),
                Some(Token {
                    kind: TokenKind::CurlyBracketOpen,
                    ..
                })
            ),
            "Called parse_struct_create not on a `{{` {:?}",
            self.tokens.get(self.curr_token_i() - 1),
        );
        let mut args = vec![];

        // Parse fields if not empty
        if !matches!(
            self.curr_token(),
            Some(Token {
                kind: TokenKind::CurlyBracketClose,
                ..
            })
        ) {
            while let Some(Token {
                kind: TokenKind::Ident(ident_id),
                ..
            }) = self.curr_token()
            {
                let ident_cloned = *ident_id;
                match self.next_token() {
                    Some(Token {
                        kind: TokenKind::Colon,
                        ..
                    }) => {
                        self.next_token();
                        let expr = self.parse_expr(0, symbols, false)?;
                        args.push((ident_cloned, expr));
                        // After parse_expr, cursor is at comma or '}'
                        if let Some(Token {
                            kind: TokenKind::Comma,
                            ..
                        }) = self.curr_token()
                        {
                            self.next_token();
                        }
                    }
                    _t => {
                        dbg!(self.curr_token(), self.peek_token(),);
                        todo!();
                    }
                }
            }
        }

        // Consume '}'
        if matches!(
            self.curr_token(),
            Some(Token {
                kind: TokenKind::CurlyBracketClose,
                ..
            })
        ) {
            self.next_token();
        } else {
            // TODO: proper error handling
        }

        Some(AstExpr {
            span: Span {
                start: self.tokens[start_token_at].span.start,
                end: self.tokens[self.curr_token_i()].span.end,
            },
            kind: ExprKind::Op(Box::new(Op::StructCreate {
                ident: lhs,
                symbol_id: None,
                args,
            })),
            type_id: None,
        })
    }
}

#[cfg(test)]
mod test {
    use crate::ast::ast_expr::debug::{DebugAtom, DebugExprKind, DebugOp, parse_debug};
    use pretty_assertions::assert_eq;

    #[test]
    fn struct_create_empty() {
        let debug_expr = parse_debug("Foo {};");
        let expected = DebugExprKind::Op(Box::new(DebugOp::StructCreate {
            ident: DebugExprKind::Atom(DebugAtom::Ident("Foo".to_string())),
            args: vec![],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn struct_create_single_field() {
        let debug_expr = parse_debug("Foo { num: 20 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::StructCreate {
            ident: DebugExprKind::Atom(DebugAtom::Ident("Foo".to_string())),
            args: vec![("num".to_string(), DebugExprKind::Atom(DebugAtom::Int(20)))],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn struct_create_multiple_fields() {
        let debug_expr = parse_debug("Point { x: 10, y: 20 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::StructCreate {
            ident: DebugExprKind::Atom(DebugAtom::Ident("Point".to_string())),
            args: vec![
                ("x".to_string(), DebugExprKind::Atom(DebugAtom::Int(10))),
                ("y".to_string(), DebugExprKind::Atom(DebugAtom::Int(20))),
            ],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn struct_create_trailing_comma() {
        let debug_expr = parse_debug("Foo { num: 42, };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::StructCreate {
            ident: DebugExprKind::Atom(DebugAtom::Ident("Foo".to_string())),
            args: vec![("num".to_string(), DebugExprKind::Atom(DebugAtom::Int(42)))],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn struct_create_nested() {
        let debug_expr = parse_debug("Outer { inner: Inner { val: 5 } };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::StructCreate {
            ident: DebugExprKind::Atom(DebugAtom::Ident("Outer".to_string())),
            args: vec![(
                "inner".to_string(),
                DebugExprKind::Op(Box::new(DebugOp::StructCreate {
                    ident: DebugExprKind::Atom(DebugAtom::Ident("Inner".to_string())),
                    args: vec![("val".to_string(), DebugExprKind::Atom(DebugAtom::Int(5)))],
                })),
            )],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn struct_create_with_expressions() {
        let debug_expr = parse_debug("Foo { num: 10 + 20 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::StructCreate {
            ident: DebugExprKind::Atom(DebugAtom::Ident("Foo".to_string())),
            args: vec![(
                "num".to_string(),
                DebugExprKind::Op(Box::new(DebugOp::Add {
                    left: DebugExprKind::Atom(DebugAtom::Int(10)),
                    right: DebugExprKind::Atom(DebugAtom::Int(20)),
                })),
            )],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn struct_create_chained_with_dot() {
        let debug_expr = parse_debug("Foo { num: 20 }.num;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Dot {
            left: DebugExprKind::Op(Box::new(DebugOp::StructCreate {
                ident: DebugExprKind::Atom(DebugAtom::Ident("Foo".to_string())),
                args: vec![("num".to_string(), DebugExprKind::Atom(DebugAtom::Int(20)))],
            })),
            right: DebugExprKind::Atom(DebugAtom::Ident("num".to_string())),
        }));
        assert_eq!(debug_expr, expected);
    }
}
