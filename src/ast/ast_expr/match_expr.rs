use crate::{
    ast::{
        Ast,
        ast_expr::{AstExpr, ExprKind, Op, error::MatchParseError},
        error::AstParseError,
    },
    interner::IdentId,
    lexer::{Span, Token, TokenKind},
    symbols::{SymbolId, SymbolTable},
};

#[derive(Debug)]
pub enum MatchOn {
    Int(i128),
    Bool(bool),
    Str(String),
    Ident((IdentId, Option<SymbolId>)),
    Struct {
        ident_id: IdentId,
        symbol_id: Option<SymbolId>,
        args: Vec<(IdentId, MatchOn)>,
        disgard_rest: bool,
    },
    Enum {
        ident_id: IdentId,
        symbol_id: Option<SymbolId>,
        variant_id: IdentId,
        params: Box<Option<MatchOn>>,
    },
}

#[derive(Debug)]
pub struct MatchBranch {
    pub on: MatchOn,
    pub on_span: Span,
    pub expr: AstExpr,
}

impl Ast {
    fn push_match_err(&mut self, err: MatchParseError) {
        self.errs.push(AstParseError::MatchParse(err));
    }
    fn parse_match_branch(&mut self, symbols: &mut SymbolTable) -> Option<MatchBranch> {
        let on = self.parse_match_on()?;

        match self.next_token() {
            Some(Token {
                kind: TokenKind::FatArrow,
                ..
            }) => (),
            Some(token) => {
                let token = token.clone();
                self.push_match_err(MatchParseError::ExpectedFatArrow { token: token });
                return None;
            }
            None => {
                self.push_match_err(MatchParseError::UnexpectedEndOfInput);
                return None;
            }
        };

        let expr = self.parse_expr(0, symbols, false)?;

        Some(MatchBranch { on, expr })
    }
    fn parse_match_on(&mut self) -> Option<MatchOn> {
        todo!()
    }

    pub fn parse_match(
        &mut self,
        symbols: &mut SymbolTable,
        start_token_at: usize,
    ) -> Option<AstExpr> {
        debug_assert!(
            matches!(
                self.tokens.get(self.curr_token_i() - 1),
                Some(Token {
                    kind: TokenKind::MatchKeyWord,
                    ..
                })
            ),
            "Called parse_match not on a `match` keyword. Got: {:?}",
            self.tokens.get(self.curr_token_i() - 1),
        );
        self.next_token();
        let on = self.parse_expr(0, symbols, false)?;
        let mut cases = vec![];
        match self.curr_token() {
            Some(Token {
                kind: TokenKind::CurlyBracketOpen,
                ..
            }) => (),
            Some(token) => {
                self.push_match_err(MatchParseError::ExpectedOpenAfterMatchExpr {
                    token: token.clone(),
                });
                return None;
            }
            None => {
                self.push_match_err(MatchParseError::UnexpectedEndOfInput);
                return None;
            }
        }
        let mut expr_count = 1;
        loop {
            let curr_token = self.peek_token();
            match curr_token {
                Some(Token {
                    kind: TokenKind::CurlyBracketClose,
                    ..
                }) => {
                    self.next_token();
                    break;
                }
                Some(_) => {
                    let match_branch = self.parse_match_branch(symbols)?;
                    expr_count += match_branch.expr.expr_count;
                    cases.push(match_branch);
                }
                None => {
                    self.next_token();
                    self.push_match_err(MatchParseError::UnexpectedEndOfInput);
                    return None;
                }
            };
        }

        Some(AstExpr {
            span: Span {
                start: self.tokens[start_token_at].span.start,
                end: self.tokens[self.curr_token_i()].span.end,
            },
            expr_count,
            kind: ExprKind::Op(Box::new(Op::Match { on, cases })),
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
