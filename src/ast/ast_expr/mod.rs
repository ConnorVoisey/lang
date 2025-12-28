use crate::{
    ast::{Ast, ast_block::AstBlock, error::AstParseError},
    interner::IdentId,
    lexer::{Span, Token, TokenKind},
    symbols::{SymbolId, SymbolTable},
    types::TypeId,
};

pub mod array;
pub mod debug;
pub mod error;
pub mod func;
pub mod if_expr;
pub mod struct_create;

#[derive(Debug)]
pub struct AstExpr {
    pub span: Span,
    pub kind: ExprKind,
    pub type_id: Option<TypeId>,
}
#[derive(Debug)]
pub enum Atom {
    Ident((IdentId, Option<SymbolId>)),
    Bool(bool),
    Int(i32),
    Str(usize),
    CStr(usize),
}

#[derive(Debug)]
pub enum Op {
    Add {
        left: AstExpr,
        right: AstExpr,
    },
    Divide {
        left: AstExpr,
        right: AstExpr,
    },
    Minus {
        left: AstExpr,
        right: AstExpr,
    },
    LessThan {
        left: AstExpr,
        right: AstExpr,
    },
    LessThanEq {
        left: AstExpr,
        right: AstExpr,
    },
    GreaterThan {
        left: AstExpr,
        right: AstExpr,
    },
    GreaterThanEq {
        left: AstExpr,
        right: AstExpr,
    },
    Neg(AstExpr),
    Ref(AstExpr),
    Multiply {
        left: AstExpr,
        right: AstExpr,
    },
    FnCall {
        ident: AstExpr,
        args: Vec<AstExpr>,
    },
    Dot {
        left: AstExpr,
        right: AstExpr,
    },
    DoubleColon {
        left: AstExpr,
        right: AstExpr,
    },
    Block(AstBlock),
    Equivalent {
        left: AstExpr,
        right: AstExpr,
    },
    ArrayInit {
        args: Vec<AstExpr>,
    },
    ArrayAccess {
        left: AstExpr,
        right: AstExpr,
    },
    BracketOpen {
        left: AstExpr,
        right: AstExpr,
    },
    IfCond {
        condition: AstExpr,
        block: AstBlock,
        else_ifs: Vec<(AstExpr, AstBlock)>,
        unconditional_else: Option<AstBlock>,
    },
    StructCreate {
        ident: AstExpr,
        symbol_id: Option<SymbolId>,
        args: Vec<(IdentId, AstExpr)>,
    },
}

#[derive(Debug)]
pub enum ExprKind {
    Atom(Atom),
    Op(Box<Op>),
}

impl Ast {
    pub fn parse_expr(
        &mut self,
        min_bp: u8,
        symbols: &mut SymbolTable,
        is_direct_if_cond: bool,
    ) -> Option<AstExpr> {
        let start_token_at = self.curr_token_i();

        // make sure we have a token
        let cur_token = match self.curr_token() {
            Some(t) => t.clone(),
            None => {
                self.errs.push(AstParseError::UnexpectedEndOfInput);
                return None;
            }
        };

        let mut lhs = match &cur_token.kind {
            TokenKind::CurlyBracketOpen => {
                // '{' expr '}'
                self.parse_block(symbols, false).map(|block| AstExpr {
                    span: Span {
                        start: start_token_at,
                        end: self.curr_token_i(),
                    },
                    kind: ExprKind::Op(Box::new(Op::Block(block))),
                    type_id: None,
                })
            }
            TokenKind::BracketOpen => {
                // '(' expr ')'
                self.next_token();
                let lhs = self.parse_expr(0, symbols, false);
                match self.curr_token() {
                    Some(Token {
                        kind: TokenKind::BracketClose,
                        ..
                    }) => { /* ok */ }
                    Some(tok) => {
                        self.errs
                            .push(AstParseError::ExpectedClosingBracket { token: tok.clone() });
                    }
                    None => {
                        self.errs.push(AstParseError::UnexpectedEndOfInput);
                        return lhs;
                    }
                }
                lhs
            }
            TokenKind::SquareBracketOpen => self.parse_array_expr(symbols),

            TokenKind::Subtract => {
                let ((), r_bp) = prefix_binding_power(&TokenKind::Subtract);
                self.next_token();
                let rhs = match self.parse_expr(r_bp, symbols, is_direct_if_cond) {
                    Some(e) => e,
                    None => {
                        // token for message: use current token if available, otherwise a dummy
                        let tok = self.curr_token().cloned().unwrap_or(Token {
                            kind: TokenKind::Subtract,
                            span: Span {
                                start: self.tokens[start_token_at].span.start,
                                end: self.tokens[start_token_at].span.end,
                            },
                        });
                        self.errs
                            .push(AstParseError::PrefixExprMissingRhs { token: tok });
                        return None;
                    }
                };
                // keep prior behavior
                self.next_token_i -= 1;
                Some(AstExpr {
                    span: Span {
                        start: self.tokens[start_token_at].span.start,
                        end: self.tokens[self.curr_token_i()].span.end,
                    },
                    kind: ExprKind::Op(Box::new(Op::Neg(rhs))),
                    type_id: None,
                })
            }

            TokenKind::Int(val) => Some(AstExpr {
                span: Span {
                    start: self.tokens[start_token_at].span.start,
                    end: self.tokens[self.curr_token_i()].span.end,
                },
                kind: ExprKind::Atom(Atom::Int(*val)),
                type_id: None,
            }),

            TokenKind::FalseKeyWord => Some(AstExpr {
                span: Span {
                    start: self.tokens[start_token_at].span.start,
                    end: self.tokens[self.curr_token_i()].span.end,
                },
                kind: ExprKind::Atom(Atom::Bool(false)),
                type_id: None,
            }),

            TokenKind::TrueKeyWord => Some(AstExpr {
                span: Span {
                    start: self.tokens[start_token_at].span.start,
                    end: self.tokens[self.curr_token_i()].span.end,
                },
                kind: ExprKind::Atom(Atom::Bool(true)),
                type_id: None,
            }),

            TokenKind::CStr(_) => Some(AstExpr {
                span: Span {
                    start: self.tokens[start_token_at].span.start,
                    end: self.tokens[self.curr_token_i()].span.end,
                },
                kind: ExprKind::Atom(Atom::CStr(self.curr_token_i())),
                type_id: None,
            }),

            TokenKind::Str(_) => Some(AstExpr {
                span: Span {
                    start: self.tokens[start_token_at].span.start,
                    end: self.tokens[self.curr_token_i()].span.end,
                },
                kind: ExprKind::Atom(Atom::Str(self.curr_token_i())),
                type_id: None,
            }),

            TokenKind::Ident(ident_id) => Some(AstExpr {
                span: Span {
                    start: self.tokens[start_token_at].span.start,
                    end: self.tokens[self.curr_token_i()].span.end,
                },
                kind: ExprKind::Atom(Atom::Ident((*ident_id, None))),
                type_id: None,
            }),

            TokenKind::Amp => {
                let ((), r_bp) = prefix_binding_power(&TokenKind::Amp);
                self.next_token();
                let rhs = match self.parse_expr(r_bp, symbols, is_direct_if_cond) {
                    Some(e) => e,
                    None => {
                        let tok = self.curr_token().cloned().unwrap_or(cur_token.clone());
                        self.errs
                            .push(AstParseError::PrefixExprMissingRhs { token: tok });
                        return None;
                    }
                };
                self.next_token_i -= 1;
                Some(AstExpr {
                    span: Span {
                        start: self.tokens[start_token_at].span.start,
                        end: self.tokens[self.curr_token_i()].span.end,
                    },
                    kind: ExprKind::Op(Box::new(Op::Ref(rhs))),
                    type_id: None,
                })
            }

            TokenKind::IfKeyWord => self.parse_if_expr(symbols, &cur_token, start_token_at),

            // default / not handled
            _ => {
                // push a helpful error instead of panicking
                if let Some(tok) = self.curr_token().cloned() {
                    self.errs
                        .push(AstParseError::UnexpectedTokenInExpr { token: tok });
                } else {
                    self.errs.push(AstParseError::UnexpectedEndOfInput);
                }
                return None;
            }
        };

        self.next_token();

        // postfix / infix loop
        loop {
            let op_token_kind = match self.curr_token() {
                None => break,
                Some(v) => match &v.kind {
                    t if t.is_op() => t.clone(),
                    TokenKind::BracketClose => break,
                    TokenKind::CurlyBracketClose => break,
                    TokenKind::SemiColon => break,
                    TokenKind::Comma => break,
                    _ => {
                        self.errs
                            .push(AstParseError::ExpectedOperator { token: v.clone() });
                        break;
                    }
                },
            };

            if let Some((l_bp, ())) = postfix_binding_power(&op_token_kind) {
                if l_bp < min_bp {
                    break;
                }
                self.next_token(); // consume postfix opener

                lhs = match op_token_kind {
                    TokenKind::SquareBracketOpen => {
                        self.parse_array_access(symbols, start_token_at, lhs?)
                    }

                    TokenKind::BracketOpen => self.parse_func_call(symbols, start_token_at, lhs?),

                    TokenKind::CurlyBracketOpen => {
                        if !is_direct_if_cond {
                            // Parse as struct if:
                            // 1. Not in an if-condition context, OR
                            // 2. In a subexpression (min_bp > 0), which means we're parsing
                            //    something like the RHS of an operator
                            self.parse_struct_create(symbols, start_token_at, lhs?)
                        } else {
                            // Top-level of an if-condition: { starts the if-block
                            self.next_token_i -= 1;
                            break;
                        }
                    }

                    _ => {
                        // fallback, should not happen — record and continue
                        if let Some(tok) = self.curr_token().cloned() {
                            self.errs
                                .push(AstParseError::UnexpectedTokenInExpr { token: tok });
                        }
                        lhs
                    }
                };
                continue;
            }

            if let Some((l_bp, r_bp)) = infix_binding_power(&op_token_kind) {
                if l_bp < min_bp {
                    break;
                }

                self.next_token(); // consume operator
                // Don't propagate is_direct_if_cond - let subexpressions parse normally
                // The flag only applies at the top level to distinguish `if x {` from `if x < y {`
                let rhs = self.parse_expr(r_bp, symbols, is_direct_if_cond);
                if rhs.is_none() {
                    // parse_expr pushed an error already — try to continue
                    // preserve lhs as-is or mark an error
                }
                let kind = match &op_token_kind {
                    TokenKind::Add => Op::Add {
                        left: lhs?,
                        right: rhs.unwrap_or(AstExpr {
                            span: Span { start: 0, end: 0 },
                            kind: ExprKind::Atom(Atom::Int(0)),
                            type_id: None,
                        }),
                    },
                    TokenKind::Subtract => Op::Minus {
                        left: lhs?,
                        right: rhs.unwrap_or(AstExpr {
                            span: Span { start: 0, end: 0 },
                            kind: ExprKind::Atom(Atom::Int(0)),
                            type_id: None,
                        }),
                    },
                    TokenKind::Slash => Op::Divide {
                        left: lhs?,
                        right: rhs.unwrap_or(AstExpr {
                            span: Span { start: 0, end: 0 },
                            kind: ExprKind::Atom(Atom::Int(0)),
                            type_id: None,
                        }),
                    },
                    TokenKind::Astrix => Op::Multiply {
                        left: lhs?,
                        right: rhs.unwrap_or(AstExpr {
                            span: Span { start: 0, end: 0 },
                            kind: ExprKind::Atom(Atom::Int(0)),
                            type_id: None,
                        }),
                    },
                    TokenKind::Dot => Op::Dot {
                        left: lhs?,
                        right: rhs.unwrap_or(AstExpr {
                            span: Span { start: 0, end: 0 },
                            kind: ExprKind::Atom(Atom::Int(0)),
                            type_id: None,
                        }),
                    },
                    TokenKind::DoubleColon => Op::DoubleColon {
                        left: lhs?,
                        right: rhs.unwrap_or(AstExpr {
                            span: Span { start: 0, end: 0 },
                            kind: ExprKind::Atom(Atom::Int(0)),
                            type_id: None,
                        }),
                    },
                    TokenKind::Equivalent => Op::Equivalent {
                        left: lhs?,
                        right: rhs.unwrap_or(AstExpr {
                            span: Span { start: 0, end: 0 },
                            kind: ExprKind::Atom(Atom::Int(0)),
                            type_id: None,
                        }),
                    },
                    TokenKind::LessThan => Op::LessThan {
                        left: lhs?,
                        right: rhs.unwrap_or(AstExpr {
                            span: Span { start: 0, end: 0 },
                            kind: ExprKind::Atom(Atom::Int(0)),
                            type_id: None,
                        }),
                    },
                    TokenKind::LessThanEq => Op::LessThanEq {
                        left: lhs?,
                        right: rhs.unwrap_or(AstExpr {
                            span: Span { start: 0, end: 0 },
                            kind: ExprKind::Atom(Atom::Int(0)),
                            type_id: None,
                        }),
                    },
                    TokenKind::GreaterThan => Op::GreaterThan {
                        left: lhs?,
                        right: rhs.unwrap_or(AstExpr {
                            span: Span { start: 0, end: 0 },
                            kind: ExprKind::Atom(Atom::Int(0)),
                            type_id: None,
                        }),
                    },
                    TokenKind::GreaterThanEq => Op::GreaterThanEq {
                        left: lhs?,
                        right: rhs.unwrap_or(AstExpr {
                            span: Span { start: 0, end: 0 },
                            kind: ExprKind::Atom(Atom::Int(0)),
                            type_id: None,
                        }),
                    },
                    _ => {
                        // unknown operator - record error
                        if let Some(tok) = self.curr_token().cloned() {
                            self.errs
                                .push(AstParseError::ExpectedOperator { token: tok });
                        }
                        unreachable!();
                    }
                };
                lhs = Some(AstExpr {
                    span: Span {
                        start: self.tokens[start_token_at].span.start,
                        end: self.tokens[self.curr_token_i()].span.end,
                    },
                    kind: ExprKind::Op(Box::new(kind)),
                    type_id: None,
                });
                continue;
            }

            break;
        }

        lhs
    }
}

// Operator precedence from lowest to highest:
// 1. Equality: == (not yet fully implemented) - would be (1, 2)
// 2. Comparison: <, <=, >, >= (all same level) - (3, 4)
// 3. Addition/Subtraction: +, - - (5, 6)
// 4. Multiplication/Division: *, / - (7, 8)
// 5. Prefix: -, & - ((), 11)
// 6. Postfix/Member access: (), [], {}, . (all same level) - (13, ()) for postfix, (13, 14) for dot
//
// For left-associative infix: (n, n+1)
// For right-associative infix: (n, n-1)
// For prefix: ((), right_bp)
// For postfix: (left_bp, ())

fn prefix_binding_power(op_token: &TokenKind) -> ((), u8) {
    match op_token {
        TokenKind::Subtract | TokenKind::Amp => ((), 11),
        _ => panic!("bad op: {:?}", op_token),
    }
}

fn postfix_binding_power(op_token: &TokenKind) -> Option<(u8, ())> {
    let res = match op_token {
        TokenKind::SquareBracketOpen | TokenKind::BracketOpen | TokenKind::CurlyBracketOpen => {
            (13, ())
        }
        _ => return None,
    };
    Some(res)
}

fn infix_binding_power(op_token: &TokenKind) -> Option<(u8, u8)> {
    match op_token {
        TokenKind::Equivalent => Some((1, 2)),
        // Comparison operators - all at the same precedence level
        TokenKind::LessThan
        | TokenKind::LessThanEq
        | TokenKind::GreaterThan
        | TokenKind::GreaterThanEq => Some((3, 4)),

        // Addition and Subtraction
        TokenKind::Add | TokenKind::Subtract => Some((5, 6)),

        // Multiplication and Division
        TokenKind::Astrix | TokenKind::Slash => Some((7, 8)),

        // Dot operator - same level as postfix operators, left-associative
        TokenKind::Dot => Some((13, 14)),
        TokenKind::DoubleColon => Some((13, 14)),

        _ => None,
    }
}

#[cfg(test)]
mod test {
    use crate::ast::ast_expr::debug::{
        DebugAtom, DebugExprKind, DebugOp, DebugStatement, parse_debug,
    };
    use pretty_assertions::assert_eq;

    #[test]
    fn basic_expr() {
        let debug_expr = parse_debug("1 + 2 - 3 * 4 / 5;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Minus {
            left: DebugExprKind::Op(Box::new(DebugOp::Add {
                left: DebugExprKind::Atom(DebugAtom::Int(1)),
                right: DebugExprKind::Atom(DebugAtom::Int(2)),
            })),
            right: DebugExprKind::Op(Box::new(DebugOp::Divide {
                left: DebugExprKind::Op(Box::new(DebugOp::Multiply {
                    left: DebugExprKind::Atom(DebugAtom::Int(3)),
                    right: DebugExprKind::Atom(DebugAtom::Int(4)),
                })),
                right: DebugExprKind::Atom(DebugAtom::Int(5)),
            })),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn bracketed() {
        let debug_expr = parse_debug("(1 + (2 - 3) * (4 / 5));");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Add {
            left: DebugExprKind::Atom(DebugAtom::Int(1)),
            right: DebugExprKind::Op(Box::new(DebugOp::Multiply {
                left: DebugExprKind::Op(Box::new(DebugOp::Minus {
                    left: DebugExprKind::Atom(DebugAtom::Int(2)),
                    right: DebugExprKind::Atom(DebugAtom::Int(3)),
                })),
                right: DebugExprKind::Op(Box::new(DebugOp::Divide {
                    left: DebugExprKind::Atom(DebugAtom::Int(4)),
                    right: DebugExprKind::Atom(DebugAtom::Int(5)),
                })),
            })),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn squared_brackets() {
        let debug_expr = parse_debug("foo[5 - 1];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
            left: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
            right: DebugExprKind::Op(Box::new(DebugOp::Minus {
                left: DebugExprKind::Atom(DebugAtom::Int(5)),
                right: DebugExprKind::Atom(DebugAtom::Int(1)),
            })),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn multi_squared_brackets() {
        let debug_expr = parse_debug("foo[5 - 1][2][bar];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
            left: DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
                left: DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
                    left: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
                    right: DebugExprKind::Op(Box::new(DebugOp::Minus {
                        left: DebugExprKind::Atom(DebugAtom::Int(5)),
                        right: DebugExprKind::Atom(DebugAtom::Int(1)),
                    })),
                })),
                right: DebugExprKind::Atom(DebugAtom::Int(2)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Ident("bar".to_string())),
        }));
        assert_eq!(debug_expr, expected);
    }
    #[test]
    fn unary_negation() {
        let debug_expr = parse_debug("-42;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Atom(
            DebugAtom::Int(42),
        ))));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn less_than() {
        let debug_expr = parse_debug("5 < 3;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::LessThan {
            left: DebugExprKind::Atom(DebugAtom::Int(5)),
            right: DebugExprKind::Atom(DebugAtom::Int(3)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn double_negation() {
        let debug_expr = parse_debug("--5;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Op(Box::new(
            DebugOp::Neg(DebugExprKind::Atom(DebugAtom::Int(5))),
        )))));
        assert_eq!(debug_expr, expected);
    }
    #[test]
    fn precedence_mixed() {
        let debug_expr = parse_debug("1 + 2 * 3 + 4;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Add {
            left: DebugExprKind::Op(Box::new(DebugOp::Add {
                left: DebugExprKind::Atom(DebugAtom::Int(1)),
                right: DebugExprKind::Op(Box::new(DebugOp::Multiply {
                    left: DebugExprKind::Atom(DebugAtom::Int(2)),
                    right: DebugExprKind::Atom(DebugAtom::Int(3)),
                })),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(4)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn chained_dots() {
        let debug_expr = parse_debug("foo.bar.baz.last;");
        // Dot should be left-associative: ((foo.bar).baz).last
        let expected = DebugExprKind::Op(Box::new(DebugOp::Dot {
            left: DebugExprKind::Op(Box::new(DebugOp::Dot {
                left: DebugExprKind::Op(Box::new(DebugOp::Dot {
                    left: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
                    right: DebugExprKind::Atom(DebugAtom::Ident("bar".to_string())),
                })),
                right: DebugExprKind::Atom(DebugAtom::Ident("baz".to_string())),
            })),
            right: DebugExprKind::Atom(DebugAtom::Ident("last".to_string())),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn mixed_call_index_dot() {
        let debug_expr = parse_debug("foo(bar)[baz].qux;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Dot {
            left: DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
                left: DebugExprKind::Op(Box::new(DebugOp::FnCall {
                    ident: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
                    args: vec![DebugExprKind::Atom(DebugAtom::Ident("bar".to_string()))],
                })),
                right: DebugExprKind::Atom(DebugAtom::Ident("baz".to_string())),
            })),
            right: DebugExprKind::Atom(DebugAtom::Ident("qux".to_string())),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn chained_double_colons() {
        let debug_expr = parse_debug("foo::bar::baz::last;");
        // `::` should have the same parsing rules as `.`, TODO: add test with both `::` and `.`
        // parsing in one expression
        let expected = DebugExprKind::Op(Box::new(DebugOp::DoubleColon {
            left: DebugExprKind::Op(Box::new(DebugOp::DoubleColon {
                left: DebugExprKind::Op(Box::new(DebugOp::DoubleColon {
                    left: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
                    right: DebugExprKind::Atom(DebugAtom::Ident("bar".to_string())),
                })),
                right: DebugExprKind::Atom(DebugAtom::Ident("baz".to_string())),
            })),
            right: DebugExprKind::Atom(DebugAtom::Ident("last".to_string())),
        }));
        assert_eq!(debug_expr, expected);
    }
    #[test]
    fn string_and_cstr_literals() {
        let debug_expr = parse_debug(r#"foo("bar", c"baz");"#);
        let expected = DebugExprKind::Op(Box::new(DebugOp::FnCall {
            ident: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
            args: vec![
                DebugExprKind::Atom(DebugAtom::Str("bar".to_string())),
                DebugExprKind::Atom(DebugAtom::CStr("baz".to_string())),
            ],
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Binding Power / Precedence Tests =====

    #[test]
    fn binding_mul_over_add() {
        // Multiplication should bind tighter than addition: 1 + 2 * 3 = 1 + (2 * 3)
        let debug_expr = parse_debug("1 + 2 * 3;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Add {
            left: DebugExprKind::Atom(DebugAtom::Int(1)),
            right: DebugExprKind::Op(Box::new(DebugOp::Multiply {
                left: DebugExprKind::Atom(DebugAtom::Int(2)),
                right: DebugExprKind::Atom(DebugAtom::Int(3)),
            })),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn binding_div_over_sub() {
        // Division should bind tighter than subtraction: 10 - 6 / 2 = 10 - (6 / 2)
        let debug_expr = parse_debug("10 - 6 / 2;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Minus {
            left: DebugExprKind::Atom(DebugAtom::Int(10)),
            right: DebugExprKind::Op(Box::new(DebugOp::Divide {
                left: DebugExprKind::Atom(DebugAtom::Int(6)),
                right: DebugExprKind::Atom(DebugAtom::Int(2)),
            })),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn binding_add_left_assoc() {
        // Addition is left-associative: 1 + 2 + 3 = (1 + 2) + 3
        let debug_expr = parse_debug("1 + 2 + 3;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Add {
            left: DebugExprKind::Op(Box::new(DebugOp::Add {
                left: DebugExprKind::Atom(DebugAtom::Int(1)),
                right: DebugExprKind::Atom(DebugAtom::Int(2)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(3)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn binding_mul_left_assoc() {
        // Multiplication is left-associative: 2 * 3 * 4 = (2 * 3) * 4
        let debug_expr = parse_debug("2 * 3 * 4;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Multiply {
            left: DebugExprKind::Op(Box::new(DebugOp::Multiply {
                left: DebugExprKind::Atom(DebugAtom::Int(2)),
                right: DebugExprKind::Atom(DebugAtom::Int(3)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(4)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn binding_comparison_same_precedence() {
        // All comparison operators have same precedence and are left-associative
        // 1 < 2 <= 3 = (1 < 2) <= 3
        let debug_expr = parse_debug("1 < 2 <= 3;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::LessThanEq {
            left: DebugExprKind::Op(Box::new(DebugOp::LessThan {
                left: DebugExprKind::Atom(DebugAtom::Int(1)),
                right: DebugExprKind::Atom(DebugAtom::Int(2)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(3)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn binding_comparison_over_arithmetic() {
        // Comparison should bind looser than arithmetic: 1 + 2 < 3 * 4 = (1 + 2) < (3 * 4)
        let debug_expr = parse_debug("1 + 2 < 3 * 4;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::LessThan {
            left: DebugExprKind::Op(Box::new(DebugOp::Add {
                left: DebugExprKind::Atom(DebugAtom::Int(1)),
                right: DebugExprKind::Atom(DebugAtom::Int(2)),
            })),
            right: DebugExprKind::Op(Box::new(DebugOp::Multiply {
                left: DebugExprKind::Atom(DebugAtom::Int(3)),
                right: DebugExprKind::Atom(DebugAtom::Int(4)),
            })),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn binding_all_comparisons_same() {
        // Test that >, >=, <, <= all have the same precedence
        let debug_expr = parse_debug("1 > 2 >= 3 < 4 <= 5;");
        // Should parse as: (((1 > 2) >= 3) < 4) <= 5
        let expected = DebugExprKind::Op(Box::new(DebugOp::LessThanEq {
            left: DebugExprKind::Op(Box::new(DebugOp::LessThan {
                left: DebugExprKind::Op(Box::new(DebugOp::GreaterThanEq {
                    left: DebugExprKind::Op(Box::new(DebugOp::GreaterThan {
                        left: DebugExprKind::Atom(DebugAtom::Int(1)),
                        right: DebugExprKind::Atom(DebugAtom::Int(2)),
                    })),
                    right: DebugExprKind::Atom(DebugAtom::Int(3)),
                })),
                right: DebugExprKind::Atom(DebugAtom::Int(4)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(5)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn binding_prefix_over_infix() {
        // Prefix operators should bind tighter than binary operators: -1 + 2 = (-1) + 2
        let debug_expr = parse_debug("-1 + 2;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Add {
            left: DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Atom(DebugAtom::Int(
                1,
            ))))),
            right: DebugExprKind::Atom(DebugAtom::Int(2)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn binding_prefix_over_mul() {
        // Prefix should bind tighter than multiplication too: -2 * 3 = (-2) * 3
        let debug_expr = parse_debug("-2 * 3;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Multiply {
            left: DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Atom(DebugAtom::Int(
                2,
            ))))),
            right: DebugExprKind::Atom(DebugAtom::Int(3)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn binding_postfix_over_prefix() {
        // Postfix should bind tighter than prefix: -foo() = -(foo())
        let debug_expr = parse_debug("-foo();");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Op(Box::new(
            DebugOp::FnCall {
                ident: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
                args: vec![],
            },
        )))));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn binding_ref_over_dot() {
        // Reference prefix should bind looser than dot: &foo.bar = &(foo.bar)
        let debug_expr = parse_debug("&foo.bar;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Ref(DebugExprKind::Op(Box::new(
            DebugOp::Dot {
                left: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Ident("bar".to_string())),
            },
        )))));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn binding_dot_same_as_postfix() {
        // Dot and array access should have same precedence, left-to-right: foo.bar[0] = (foo.bar)[0]
        let debug_expr = parse_debug("foo.bar[0];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
            left: DebugExprKind::Op(Box::new(DebugOp::Dot {
                left: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Ident("bar".to_string())),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(0)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn binding_call_same_as_dot() {
        // Function call and dot should have same precedence: foo.bar() = (foo.bar)()
        let debug_expr = parse_debug("foo.bar();");
        let expected = DebugExprKind::Op(Box::new(DebugOp::FnCall {
            ident: DebugExprKind::Op(Box::new(DebugOp::Dot {
                left: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Ident("bar".to_string())),
            })),
            args: vec![],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn binding_complex_expression() {
        // Test a complex expression: -arr[i + 1].x * 2 < 10
        // Should be: (-(((arr[i + 1]).x) * 2)) < 10
        let debug_expr = parse_debug("-arr[i + 1].x * 2 < 10;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::LessThan {
            left: DebugExprKind::Op(Box::new(DebugOp::Multiply {
                left: DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Op(Box::new(
                    DebugOp::Dot {
                        left: DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
                            left: DebugExprKind::Atom(DebugAtom::Ident("arr".to_string())),
                            right: DebugExprKind::Op(Box::new(DebugOp::Add {
                                left: DebugExprKind::Atom(DebugAtom::Ident("i".to_string())),
                                right: DebugExprKind::Atom(DebugAtom::Int(1)),
                            })),
                        })),
                        right: DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
                    },
                ))))),
                right: DebugExprKind::Atom(DebugAtom::Int(2)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(10)),
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Associativity Edge Cases =====

    #[test]
    fn subtraction_left_assoc() {
        // Subtraction is left-associative: 10 - 5 - 2 = (10 - 5) - 2 = 3
        let debug_expr = parse_debug("10 - 5 - 2;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Minus {
            left: DebugExprKind::Op(Box::new(DebugOp::Minus {
                left: DebugExprKind::Atom(DebugAtom::Int(10)),
                right: DebugExprKind::Atom(DebugAtom::Int(5)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(2)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn division_left_assoc() {
        // Division is left-associative: 100 / 10 / 2 = (100 / 10) / 2 = 5
        let debug_expr = parse_debug("100 / 10 / 2;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Divide {
            left: DebugExprKind::Op(Box::new(DebugOp::Divide {
                left: DebugExprKind::Atom(DebugAtom::Int(100)),
                right: DebugExprKind::Atom(DebugAtom::Int(10)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(2)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn mixed_add_sub_left_assoc() {
        // Mixed addition and subtraction: 10 + 5 - 3 + 1 = ((10 + 5) - 3) + 1
        let debug_expr = parse_debug("10 + 5 - 3 + 1;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Add {
            left: DebugExprKind::Op(Box::new(DebugOp::Minus {
                left: DebugExprKind::Op(Box::new(DebugOp::Add {
                    left: DebugExprKind::Atom(DebugAtom::Int(10)),
                    right: DebugExprKind::Atom(DebugAtom::Int(5)),
                })),
                right: DebugExprKind::Atom(DebugAtom::Int(3)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(1)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn mixed_mul_div_left_assoc() {
        // Mixed multiplication and division: 20 * 3 / 4 * 2 = ((20 * 3) / 4) * 2
        let debug_expr = parse_debug("20 * 3 / 4 * 2;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Multiply {
            left: DebugExprKind::Op(Box::new(DebugOp::Divide {
                left: DebugExprKind::Op(Box::new(DebugOp::Multiply {
                    left: DebugExprKind::Atom(DebugAtom::Int(20)),
                    right: DebugExprKind::Atom(DebugAtom::Int(3)),
                })),
                right: DebugExprKind::Atom(DebugAtom::Int(4)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(2)),
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Prefix Operator Edge Cases =====

    #[test]
    fn double_negation_in_expression() {
        // Double negation in addition: --5 + 3
        let debug_expr = parse_debug("--5 + 3;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Add {
            left: DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Op(Box::new(
                DebugOp::Neg(DebugExprKind::Atom(DebugAtom::Int(5))),
            ))))),
            right: DebugExprKind::Atom(DebugAtom::Int(3)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn negation_of_negation_multiply() {
        // Negation in multiplication: -2 * -3 = (-2) * (-3)
        let debug_expr = parse_debug("-2 * -3;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Multiply {
            left: DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Atom(DebugAtom::Int(
                2,
            ))))),
            right: DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Atom(DebugAtom::Int(
                3,
            ))))),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn reference_of_negation() {
        // Reference of negation: &-x = &(-x)
        let debug_expr = parse_debug("&-x;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Ref(DebugExprKind::Op(Box::new(
            DebugOp::Neg(DebugExprKind::Atom(DebugAtom::Ident("x".to_string()))),
        )))));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn negation_of_reference() {
        // Negation of reference: -&x = -(&x)
        // Note: & has same precedence as -, so this parses right-to-left
        let debug_expr = parse_debug("-&x;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Op(Box::new(
            DebugOp::Ref(DebugExprKind::Atom(DebugAtom::Ident("x".to_string()))),
        )))));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn reference_in_arithmetic() {
        let debug_expr = parse_debug("&x + &y;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Add {
            left: DebugExprKind::Op(Box::new(DebugOp::Ref(DebugExprKind::Atom(
                DebugAtom::Ident("x".to_string()),
            )))),
            right: DebugExprKind::Op(Box::new(DebugOp::Ref(DebugExprKind::Atom(
                DebugAtom::Ident("y".to_string()),
            )))),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn reference_of_expression() {
        let debug_expr = parse_debug("&(x + y);");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Ref(DebugExprKind::Op(Box::new(
            DebugOp::Add {
                left: DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Ident("y".to_string())),
            },
        )))));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn triple_negation() {
        let debug_expr = parse_debug("---x;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Op(Box::new(
            DebugOp::Neg(DebugExprKind::Op(Box::new(DebugOp::Neg(
                DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
            )))),
        )))));
        assert_eq!(debug_expr, expected);
    }

    // ===== Atomic/Minimal Expression Tests =====

    #[test]
    fn just_integer() {
        let debug_expr = parse_debug("42;");
        let expected = DebugExprKind::Atom(DebugAtom::Int(42));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn just_identifier() {
        let debug_expr = parse_debug("foo;");
        let expected = DebugExprKind::Atom(DebugAtom::Ident("foo".to_string()));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn just_true() {
        let debug_expr = parse_debug("true;");
        let expected = DebugExprKind::Atom(DebugAtom::Bool(true));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn just_false() {
        let debug_expr = parse_debug("false;");
        let expected = DebugExprKind::Atom(DebugAtom::Bool(false));
        assert_eq!(debug_expr, expected);
    }

    // ===== Complex Postfix Chains =====

    #[test]
    fn complex_postfix_chain() {
        let debug_expr = parse_debug("obj.method()[0].field(arg);");
        let expected = DebugExprKind::Op(Box::new(DebugOp::FnCall {
            ident: DebugExprKind::Op(Box::new(DebugOp::Dot {
                left: DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
                    left: DebugExprKind::Op(Box::new(DebugOp::FnCall {
                        ident: DebugExprKind::Op(Box::new(DebugOp::Dot {
                            left: DebugExprKind::Atom(DebugAtom::Ident("obj".to_string())),
                            right: DebugExprKind::Atom(DebugAtom::Ident("method".to_string())),
                        })),
                        args: vec![],
                    })),
                    right: DebugExprKind::Atom(DebugAtom::Int(0)),
                })),
                right: DebugExprKind::Atom(DebugAtom::Ident("field".to_string())),
            })),
            args: vec![DebugExprKind::Atom(DebugAtom::Ident("arg".to_string()))],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn array_of_function_results() {
        let debug_expr = parse_debug("get_arr()[0][1];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
            left: DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
                left: DebugExprKind::Op(Box::new(DebugOp::FnCall {
                    ident: DebugExprKind::Atom(DebugAtom::Ident("get_arr".to_string())),
                    args: vec![],
                })),
                right: DebugExprKind::Atom(DebugAtom::Int(0)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(1)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn deeply_nested_field_access() {
        let debug_expr = parse_debug("a.b.c.d.e.f;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Dot {
            left: DebugExprKind::Op(Box::new(DebugOp::Dot {
                left: DebugExprKind::Op(Box::new(DebugOp::Dot {
                    left: DebugExprKind::Op(Box::new(DebugOp::Dot {
                        left: DebugExprKind::Op(Box::new(DebugOp::Dot {
                            left: DebugExprKind::Atom(DebugAtom::Ident("a".to_string())),
                            right: DebugExprKind::Atom(DebugAtom::Ident("b".to_string())),
                        })),
                        right: DebugExprKind::Atom(DebugAtom::Ident("c".to_string())),
                    })),
                    right: DebugExprKind::Atom(DebugAtom::Ident("d".to_string())),
                })),
                right: DebugExprKind::Atom(DebugAtom::Ident("e".to_string())),
            })),
            right: DebugExprKind::Atom(DebugAtom::Ident("f".to_string())),
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Parentheses Edge Cases =====

    #[test]
    fn deeply_nested_parens() {
        let debug_expr = parse_debug("((((5))));");
        let expected = DebugExprKind::Atom(DebugAtom::Int(5));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn parens_override_precedence() {
        // Parentheses override precedence: (1 + 2) * 3 = 9 (not 7)
        let debug_expr = parse_debug("(1 + 2) * 3;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Multiply {
            left: DebugExprKind::Op(Box::new(DebugOp::Add {
                left: DebugExprKind::Atom(DebugAtom::Int(1)),
                right: DebugExprKind::Atom(DebugAtom::Int(2)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(3)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn parens_with_division() {
        // Parentheses changing associativity: 100 / (10 / 2) = 20 (not 5)
        let debug_expr = parse_debug("100 / (10 / 2);");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Divide {
            left: DebugExprKind::Atom(DebugAtom::Int(100)),
            right: DebugExprKind::Op(Box::new(DebugOp::Divide {
                left: DebugExprKind::Atom(DebugAtom::Int(10)),
                right: DebugExprKind::Atom(DebugAtom::Int(2)),
            })),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn complex_parens_with_multiple_operators() {
        let debug_expr = parse_debug("((1 + 2) * (3 + 4)) / ((5 - 2) + 1);");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Divide {
            left: DebugExprKind::Op(Box::new(DebugOp::Multiply {
                left: DebugExprKind::Op(Box::new(DebugOp::Add {
                    left: DebugExprKind::Atom(DebugAtom::Int(1)),
                    right: DebugExprKind::Atom(DebugAtom::Int(2)),
                })),
                right: DebugExprKind::Op(Box::new(DebugOp::Add {
                    left: DebugExprKind::Atom(DebugAtom::Int(3)),
                    right: DebugExprKind::Atom(DebugAtom::Int(4)),
                })),
            })),
            right: DebugExprKind::Op(Box::new(DebugOp::Add {
                left: DebugExprKind::Op(Box::new(DebugOp::Minus {
                    left: DebugExprKind::Atom(DebugAtom::Int(5)),
                    right: DebugExprKind::Atom(DebugAtom::Int(2)),
                })),
                right: DebugExprKind::Atom(DebugAtom::Int(1)),
            })),
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Greater Than Operator Edge Cases =====

    #[test]
    fn greater_than_basic() {
        let debug_expr = parse_debug("10 > 5;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::GreaterThan {
            left: DebugExprKind::Atom(DebugAtom::Int(10)),
            right: DebugExprKind::Atom(DebugAtom::Int(5)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn greater_than_eq_basic() {
        let debug_expr = parse_debug("10 >= 5;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::GreaterThanEq {
            left: DebugExprKind::Atom(DebugAtom::Int(10)),
            right: DebugExprKind::Atom(DebugAtom::Int(5)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn chained_greater_than() {
        // Chained: 10 > 5 > 2 = (10 > 5) > 2
        let debug_expr = parse_debug("10 > 5 > 2;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::GreaterThan {
            left: DebugExprKind::Op(Box::new(DebugOp::GreaterThan {
                left: DebugExprKind::Atom(DebugAtom::Int(10)),
                right: DebugExprKind::Atom(DebugAtom::Int(5)),
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(2)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn greater_than_with_arithmetic() {
        let debug_expr = parse_debug("x * 2 > y + 3;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::GreaterThan {
            left: DebugExprKind::Op(Box::new(DebugOp::Multiply {
                left: DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Int(2)),
            })),
            right: DebugExprKind::Op(Box::new(DebugOp::Add {
                left: DebugExprKind::Atom(DebugAtom::Ident("y".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Int(3)),
            })),
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Complex Mixed Operator Tests =====

    #[test]
    fn all_binary_operators_mixed() {
        // Mix all operators: 1 + 2 * 3 < 4 - 5 / 6
        // Should parse as: (1 + (2 * 3)) < (4 - (5 / 6))
        let debug_expr = parse_debug("1 + 2 * 3 < 4 - 5 / 6;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::LessThan {
            left: DebugExprKind::Op(Box::new(DebugOp::Add {
                left: DebugExprKind::Atom(DebugAtom::Int(1)),
                right: DebugExprKind::Op(Box::new(DebugOp::Multiply {
                    left: DebugExprKind::Atom(DebugAtom::Int(2)),
                    right: DebugExprKind::Atom(DebugAtom::Int(3)),
                })),
            })),
            right: DebugExprKind::Op(Box::new(DebugOp::Minus {
                left: DebugExprKind::Atom(DebugAtom::Int(4)),
                right: DebugExprKind::Op(Box::new(DebugOp::Divide {
                    left: DebugExprKind::Atom(DebugAtom::Int(5)),
                    right: DebugExprKind::Atom(DebugAtom::Int(6)),
                })),
            })),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn prefix_and_postfix_together() {
        // Prefix negation with postfix operations: -foo().bar[0]
        let debug_expr = parse_debug("-foo().bar[0];");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Op(Box::new(
            DebugOp::ArrayAccess {
                left: DebugExprKind::Op(Box::new(DebugOp::Dot {
                    left: DebugExprKind::Op(Box::new(DebugOp::FnCall {
                        ident: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
                        args: vec![],
                    })),
                    right: DebugExprKind::Atom(DebugAtom::Ident("bar".to_string())),
                })),
                right: DebugExprKind::Atom(DebugAtom::Int(0)),
            },
        )))));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn comparison_of_comparisons() {
        let debug_expr = parse_debug("(x < y) > (a < b);");
        let expected = DebugExprKind::Op(Box::new(DebugOp::GreaterThan {
            left: DebugExprKind::Op(Box::new(DebugOp::LessThan {
                left: DebugExprKind::Atom(DebugAtom::Ident("x".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Ident("y".to_string())),
            })),
            right: DebugExprKind::Op(Box::new(DebugOp::LessThan {
                left: DebugExprKind::Atom(DebugAtom::Ident("a".to_string())),
                right: DebugExprKind::Atom(DebugAtom::Ident("b".to_string())),
            })),
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Function Call Edge Cases =====

    #[test]
    fn empty_function_call() {
        let debug_expr = parse_debug("foo();");
        let expected = DebugExprKind::Op(Box::new(DebugOp::FnCall {
            ident: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
            args: vec![],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn function_with_complex_args() {
        // Function call with complex expressions: foo(a + b, c * d, e())
        let debug_expr = parse_debug("foo(a + b, c * d, e());");
        let expected = DebugExprKind::Op(Box::new(DebugOp::FnCall {
            ident: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
            args: vec![
                DebugExprKind::Op(Box::new(DebugOp::Add {
                    left: DebugExprKind::Atom(DebugAtom::Ident("a".to_string())),
                    right: DebugExprKind::Atom(DebugAtom::Ident("b".to_string())),
                })),
                DebugExprKind::Op(Box::new(DebugOp::Multiply {
                    left: DebugExprKind::Atom(DebugAtom::Ident("c".to_string())),
                    right: DebugExprKind::Atom(DebugAtom::Ident("d".to_string())),
                })),
                DebugExprKind::Op(Box::new(DebugOp::FnCall {
                    ident: DebugExprKind::Atom(DebugAtom::Ident("e".to_string())),
                    args: vec![],
                })),
            ],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn deeply_nested_function_calls() {
        let debug_expr = parse_debug("a(b(c(d())));");
        let expected = DebugExprKind::Op(Box::new(DebugOp::FnCall {
            ident: DebugExprKind::Atom(DebugAtom::Ident("a".to_string())),
            args: vec![DebugExprKind::Op(Box::new(DebugOp::FnCall {
                ident: DebugExprKind::Atom(DebugAtom::Ident("b".to_string())),
                args: vec![DebugExprKind::Op(Box::new(DebugOp::FnCall {
                    ident: DebugExprKind::Atom(DebugAtom::Ident("c".to_string())),
                    args: vec![DebugExprKind::Op(Box::new(DebugOp::FnCall {
                        ident: DebugExprKind::Atom(DebugAtom::Ident("d".to_string())),
                        args: vec![],
                    }))],
                }))],
            }))],
        }));
        assert_eq!(debug_expr, expected);
    }

    // ===== Block Expression Edge Cases =====

    #[test]
    fn block_in_arithmetic() {
        let debug_expr = parse_debug("{ 5 } + 3;");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Add {
            left: DebugExprKind::Op(Box::new(DebugOp::Block {
                statements: vec![DebugStatement::BlockReturn {
                    expr: DebugExprKind::Atom(DebugAtom::Int(5)),
                    is_fn_return: false,
                }],
            })),
            right: DebugExprKind::Atom(DebugAtom::Int(3)),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn nested_blocks() {
        let debug_expr = parse_debug("{ { 42 } };");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Block {
            statements: vec![DebugStatement::BlockReturn {
                expr: DebugExprKind::Op(Box::new(DebugOp::Block {
                    statements: vec![DebugStatement::BlockReturn {
                        expr: DebugExprKind::Atom(DebugAtom::Int(42)),
                        is_fn_return: false,
                    }],
                })),
                is_fn_return: false,
            }],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn block_as_function_argument() {
        let debug_expr = parse_debug("foo({ 1 + 2 });");
        let expected = DebugExprKind::Op(Box::new(DebugOp::FnCall {
            ident: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
            args: vec![DebugExprKind::Op(Box::new(DebugOp::Block {
                statements: vec![DebugStatement::BlockReturn {
                    expr: DebugExprKind::Op(Box::new(DebugOp::Add {
                        left: DebugExprKind::Atom(DebugAtom::Int(1)),
                        right: DebugExprKind::Atom(DebugAtom::Int(2)),
                    })),
                    is_fn_return: false,
                }],
            }))],
        }));
        assert_eq!(debug_expr, expected);
    }
}
