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
        debug_assert!(
            matches!(
                self.tokens.get(self.curr_token_i()),
                Some(Token {
                    kind: TokenKind::IfKeyWord,
                    ..
                })
            ),
            "Called parse_if_expr not on a `if` keyword, got {:?}",
            self.tokens.get(self.curr_token_i()),
        );
        self.next_token();
        let condition = match self.parse_expr(0, symbols, true) {
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
                            self.next_token(); // consume 'if'
                            match self.parse_expr(0, symbols, true) {
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
                            self.next_token(); // consume peeked '{'
                            unconditional_else = self.parse_block(symbols, false);
                            break;
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

#[cfg(test)]
mod test {
    use crate::ast::ast_expr::debug::{
        DebugAtom, DebugExprKind, DebugOp, DebugStatement, parse_debug,
    };
    use pretty_assertions::assert_eq;

    // ===== Basic If Tests =====

    #[test]
    fn simple_if_with_bool() {
        let debug_expr = parse_debug("if true { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Atom(DebugAtom::Bool(true)),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_with_comparison() {
        let debug_expr = parse_debug("if 5 < 10 { 42 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::LessThan {
                left: DebugExprKind::Atom(DebugAtom::Int(5)),
                right: DebugExprKind::Atom(DebugAtom::Int(10)),
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(42)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_with_identifier_condition() {
        let debug_expr = parse_debug("if foo { bar };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Ident("bar".to_string())),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== If-Else Tests =====

    #[test]
    fn if_else_basic() {
        let debug_expr = parse_debug("if true { 1 } else { 2 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Atom(DebugAtom::Bool(true)),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: Some(vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(2)),
                is_fn_return: false,
            }]),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_else_if_chain() {
        let debug_expr = parse_debug("if x < 0 { 1 } else if x < 10 { 2 } else { 3 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::LessThan {
                left: DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Int(0)),
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![(
                DebugExprKind::Op(Box::new(DebugOp::LessThan {
                    left: DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
                    right: DebugExprKind::Atom(DebugAtom::Int(10)),
                })),
                vec![DebugStatement::BlockReturn {
                    expr: DebugExprKind::Atom(DebugAtom::Int(2)),
                    is_fn_return: false,
                }],
            )],
            unconditional_else: Some(vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(3)),
                is_fn_return: false,
            }]),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn multiple_else_if_no_final_else() {
        let debug_expr = parse_debug("if a { 1 } else if b { 2 } else if c { 3 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Atom(DebugAtom::Ident("a".to_string())),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![
                (
                    DebugExprKind::Atom(DebugAtom::Ident("b".to_string())),
                    vec![DebugStatement::BlockReturn {
                        expr: DebugExprKind::Atom(DebugAtom::Int(2)),
                        is_fn_return: false,
                    }],
                ),
                (
                    DebugExprKind::Atom(DebugAtom::Ident("c".to_string())),
                    vec![DebugStatement::BlockReturn {
                        expr: DebugExprKind::Atom(DebugAtom::Int(3)),
                        is_fn_return: false,
                    }],
                ),
            ],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Nested If Tests =====

    #[test]
    fn nested_if_expressions() {
        let debug_expr = parse_debug("if a { if b { 1 } else { 2 } };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Atom(DebugAtom::Ident("a".to_string())),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Op(Box::new(DebugOp::IfCond {
                    condition: DebugExprKind::Atom(DebugAtom::Ident("b".to_string())),
                    block: vec![DebugStatement::BlockReturn {
                        expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                        is_fn_return: false,
                    }],
                    else_ifs: vec![],
                    unconditional_else: Some(vec![DebugStatement::BlockReturn {
                        expr: DebugExprKind::Atom(DebugAtom::Int(2)),
                        is_fn_return: false,
                    }]),
                })),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Edge Case: Function Calls in Condition =====

    #[test]
    fn if_with_function_call_condition() {
        let debug_expr = parse_debug("if is_valid() { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::FnCall {
                ident: DebugExprKind::Atom(DebugAtom::Ident("is_valid".to_string())),
                args: vec![],
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_with_function_call_with_args() {
        let debug_expr = parse_debug("if check(x, y) { 42 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::FnCall {
                ident: DebugExprKind::Atom(DebugAtom::Ident("check".to_string())),
                args: vec![
                    DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
                    DebugExprKind::Atom(DebugAtom::Ident("y".to_string())),
                ],
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(42)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_with_chained_method_call() {
        let debug_expr = parse_debug("if obj.method() { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::FnCall {
                ident: DebugExprKind::Op(Box::new(DebugOp::Dot {
                    left: DebugExprKind::Atom(DebugAtom::Ident("obj".to_string())),
                    right: DebugExprKind::Atom(DebugAtom::Ident("method".to_string())),
                })),
                args: vec![],
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Edge Case: Array Access in Condition =====

    #[test]
    fn if_with_array_access_condition() {
        let debug_expr = parse_debug("if arr[0] { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
                left: DebugExprKind::Atom(DebugAtom::Ident("arr".to_string())),
                args: vec![DebugExprKind::Atom(DebugAtom::Int(0))],
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_with_array_access_comparison() {
        let debug_expr = parse_debug("if arr[i] < 10 { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::LessThan {
                left: DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
                    left: DebugExprKind::Atom(DebugAtom::Ident("arr".to_string())),
                    args: vec![DebugExprKind::Atom(DebugAtom::Ident("i".to_string()))],
                })),
                right: DebugExprKind::Atom(DebugAtom::Int(10)),
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Edge Case: Struct Field Access in Condition =====

    #[test]
    fn if_with_dot_access_condition() {
        let debug_expr = parse_debug("if obj.field { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::Dot {
                left: DebugExprKind::Atom(DebugAtom::Ident("obj".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Ident("field".to_string())),
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_with_chained_dot_access() {
        let debug_expr = parse_debug("if a.b.c { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::Dot {
                left: DebugExprKind::Op(Box::new(DebugOp::Dot {
                    left: DebugExprKind::Atom(DebugAtom::Ident("a".to_string())),
                    right: DebugExprKind::Atom(DebugAtom::Ident("b".to_string())),
                })),
                right: DebugExprKind::Atom(DebugAtom::Ident("c".to_string())),
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Edge Case: Complex Expressions in Condition =====

    #[test]
    fn if_with_arithmetic_in_condition() {
        let debug_expr = parse_debug("if x + y * 2 { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::Add {
                left: DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
                right: DebugExprKind::Op(Box::new(DebugOp::Multiply {
                    left: DebugExprKind::Atom(DebugAtom::Ident("y".to_string())),
                    right: DebugExprKind::Atom(DebugAtom::Int(2)),
                })),
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_with_parenthesized_condition() {
        let debug_expr = parse_debug("if (x < 5) { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::LessThan {
                left: DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Int(5)),
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_with_eq() {
        let debug_expr = parse_debug("if read_amount == buffer_size { break; };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::Equivalent {
                left: DebugExprKind::Atom(DebugAtom::Ident("read_amount".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Ident("buffer_size".to_string())),
            })),
            block: vec![DebugStatement::Break],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Edge Case: Array Literal in Condition =====

    #[test]
    fn if_with_array_literal_in_condition() {
        let debug_expr = parse_debug("if [1, 2, 3] { 42 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::ArrayInit {
                args: vec![
                    DebugExprKind::Atom(DebugAtom::Int(1)),
                    DebugExprKind::Atom(DebugAtom::Int(2)),
                    DebugExprKind::Atom(DebugAtom::Int(3)),
                ],
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(42)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_with_empty_array_in_condition() {
        let debug_expr = parse_debug("if [] { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::ArrayInit { args: vec![] })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Critical Edge Case: Struct Instantiation vs Block Ambiguity =====

    #[test]
    fn if_identifier_then_block_not_struct() {
        // This is the critical case: "if foo { ... }" should be if-expression,
        // NOT "if (foo { ... })" (struct instantiation)
        // The is_direct_if_cond parameter ensures the { starts a block, not a struct
        let debug_expr = parse_debug("if foo { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_with_explicit_struct_in_parens() {
        // If you want a struct in the condition, you need parens
        let debug_expr = parse_debug("if (Point { x: 1, y: 2 }) { 42 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::StructCreate {
                ident: DebugExprKind::Atom(DebugAtom::Ident("Point".to_string())),
                args: vec![
                    ("x".to_string(), DebugExprKind::Atom(DebugAtom::Int(1))),
                    ("y".to_string(), DebugExprKind::Atom(DebugAtom::Int(2))),
                ],
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(42)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_with_struct_field_comparison() {
        let debug_expr = parse_debug("if (Point { x: 1, y: 2 }.x < 5) { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::LessThan {
                left: DebugExprKind::Op(Box::new(DebugOp::Dot {
                    left: DebugExprKind::Op(Box::new(DebugOp::StructCreate {
                        ident: DebugExprKind::Atom(DebugAtom::Ident("Point".to_string())),
                        args: vec![
                            ("x".to_string(), DebugExprKind::Atom(DebugAtom::Int(1))),
                            ("y".to_string(), DebugExprKind::Atom(DebugAtom::Int(2))),
                        ],
                    })),
                    right: DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
                })),
                right: DebugExprKind::Atom(DebugAtom::Int(5)),
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== If as Expression in Different Contexts =====

    #[test]
    fn if_in_array_literal() {
        let debug_expr = parse_debug("[if true { 1 } else { 2 }, 3];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayInit {
            args: vec![
                DebugExprKind::Op(Box::new(DebugOp::IfCond {
                    condition: DebugExprKind::Atom(DebugAtom::Bool(true)),
                    block: vec![DebugStatement::BlockReturn {
                        expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                        is_fn_return: false,
                    }],
                    else_ifs: vec![],
                    unconditional_else: Some(vec![DebugStatement::BlockReturn {
                        expr: DebugExprKind::Atom(DebugAtom::Int(2)),
                        is_fn_return: false,
                    }]),
                })),
                DebugExprKind::Atom(DebugAtom::Int(3)),
            ],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_as_function_argument() {
        let debug_expr = parse_debug("foo(if x { 1 } else { 2 });");
        let expected = DebugExprKind::Op(Box::new(DebugOp::FnCall {
            ident: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
            args: vec![DebugExprKind::Op(Box::new(DebugOp::IfCond {
                condition: DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
                block: vec![DebugStatement::BlockReturn {
                    expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                    is_fn_return: false,
                }],
                else_ifs: vec![],
                unconditional_else: Some(vec![DebugStatement::BlockReturn {
                    expr: DebugExprKind::Atom(DebugAtom::Int(2)),
                    is_fn_return: false,
                }]),
            }))],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_in_arithmetic() {
        let debug_expr = parse_debug("if x { 1 } else { 2 } + 5;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Add {
            left: DebugExprKind::Op(Box::new(DebugOp::IfCond {
                condition: DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
                block: vec![DebugStatement::BlockReturn {
                    expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                    is_fn_return: false,
                }],
                else_ifs: vec![],
                unconditional_else: Some(vec![DebugStatement::BlockReturn {
                    expr: DebugExprKind::Atom(DebugAtom::Int(2)),
                    is_fn_return: false,
                }]),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(5)),
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Complex Block Content =====

    #[test]
    fn if_with_multiple_statements_in_block() {
        let debug_expr = parse_debug("if true { let x = 5; x };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Atom(DebugAtom::Bool(true)),
            block: vec![
                DebugStatement::Declaration {
                    ident: "x".to_string(),
                    expr: DebugExprKind::Atom(DebugAtom::Int(5)),
                },
                DebugStatement::BlockReturn {
                    expr: DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
                    is_fn_return: false,
                },
            ],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_with_nested_blocks() {
        let debug_expr = parse_debug("if x { { 1 } };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Op(Box::new(DebugOp::Block {
                    statements: vec![DebugStatement::BlockReturn {
                        expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                        is_fn_return: false,
                    }],
                })),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Chained Comparisons in Condition =====

    #[test]
    fn if_with_chained_comparison() {
        let debug_expr = parse_debug("if 0 < x <= 10 { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::LessThanEq {
                left: DebugExprKind::Op(Box::new(DebugOp::LessThan {
                    left: DebugExprKind::Atom(DebugAtom::Int(0)),
                    right: DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
                })),
                right: DebugExprKind::Atom(DebugAtom::Int(10)),
            })),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Negation in Condition =====

    #[test]
    fn if_with_negation() {
        let debug_expr = parse_debug("if -x { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Atom(
                DebugAtom::Ident("x".to_string()),
            )))),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn if_with_reference() {
        let debug_expr = parse_debug("if &x { 1 };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::IfCond {
            condition: DebugExprKind::Op(Box::new(DebugOp::Ref(DebugExprKind::Atom(
                DebugAtom::Ident("x".to_string()),
            )))),
            block: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Atom(DebugAtom::Int(1)),
                is_fn_return: false,
            }],
            else_ifs: vec![],
            unconditional_else: None,
        }));
        assert_eq!(debug_expr, expected);
    }
}
