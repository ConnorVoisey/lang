use crate::{
    ast::{Ast, ast_block::AstBlock},
    interner::IdentId,
    lexer::{Span, Token, TokenKind},
    symbols::{SymbolId, SymbolTable},
    types::TypeId,
};

pub mod error;

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
    Block(AstBlock),
    Equivalent {
        left: AstExpr,
        right: AstExpr,
    },
    SquareOpen {
        left: AstExpr,
        args: Vec<AstExpr>,
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
}

#[derive(Debug)]
pub enum ExprKind {
    Atom(Atom),
    Op(Box<Op>),
}

impl Ast {
    pub fn parse_expr(&mut self, min_bp: u8, symbols: &mut SymbolTable) -> Option<AstExpr> {
        let start_token_at = self.curr_token_i();
        let mut lhs = match &self
            .curr_token()
            .expect("called parse expr outside of the token index")
            .kind
        {
            TokenKind::BracketOpen => {
                self.next_token();
                let lhs = self.parse_expr(0, symbols);
                assert!(
                    matches!(
                        self.curr_token(),
                        Some(Token {
                            kind: TokenKind::BracketClose,
                            ..
                        })
                    ),
                    "Parsed bracket expr but didnt end on a close bracket"
                );
                lhs
            }
            TokenKind::Subtract => {
                let ((), r_bp) = prefix_binding_power(&TokenKind::Subtract);
                self.next_token();
                let rhs = self
                    .parse_expr(r_bp, symbols)
                    .expect("Failed to parse prefix expr");
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
            // TokenType::Float(val) => UnverExpr::Atom(UnverAtom::Float(*val)),
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
                let rhs = self
                    .parse_expr(r_bp, symbols)
                    .expect("Failed to parse prefix expr");
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
            TokenKind::IfKeyWord => {
                self.next_token();
                let condition = self
                    .parse_expr(0, symbols)
                    .expect("Failed to parse condition");
                assert!(
                    matches!(
                        self.curr_token(),
                        Some(Token {
                            kind: TokenKind::CurlyBracketOpen,
                            ..
                        })
                    ),
                    "Parsed if condition then didnt have `{{`"
                );
                let block = self.parse_block(symbols).expect("Failed to parse if block");
                let mut else_ifs = vec![];
                let mut unconditional_else = None;
                while let Some(token) = self.peek_token() {
                    match token {
                        Token {
                            kind: TokenKind::ElseKeyWord,
                            ..
                        } => {
                            self.next_token();
                            match self.peek_token() {
                                Some(Token {
                                    kind: TokenKind::IfKeyWord,
                                    ..
                                }) => {
                                    let condition = self.parse_expr(0, symbols).unwrap();
                                    let block = self.parse_block(symbols).unwrap();
                                    else_ifs.push((condition, block));
                                }
                                Some(Token {
                                    kind: TokenKind::CurlyBracketOpen,
                                    ..
                                }) => {
                                    self.next_token();
                                    unconditional_else = self.parse_block(symbols);
                                }
                                _ => break,
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
            t => {
                dbg!(
                    t,
                    self.tokens.get(self.curr_token_i() - 1),
                    self.curr_token(),
                    self.tokens.get(self.curr_token_i() + 1),
                );
                // debug_tokens(tokens, i);
                todo!()
            }
        };
        self.next_token();

        loop {
            let op_token = match self.curr_token() {
                None => break,
                Some(v) => match &v.kind {
                    t if t.is_op() => t,
                    TokenKind::BracketClose => {
                        break;
                    }
                    TokenKind::SemiColon => {
                        // finish parsing expression
                        break;
                    }
                    t => {
                        dbg!(&t);
                        panic!("bad token: {:?}, expected op", t);
                    }
                },
            };
            let op_token = op_token.clone();
            // TODO: dont like this, really don't think this should have to be cloned

            if let Some((l_bp, ())) = postfix_binding_power(&op_token) {
                if l_bp < min_bp {
                    break;
                }
                self.next_token();
                lhs = match op_token {
                    TokenKind::SquareBracketOpen => {
                        let mut args = vec![];
                        loop {
                            if let Some(arg) = self.parse_expr(0, symbols) {
                                args.push(arg);
                            }
                            match self.curr_token() {
                                Some(Token {
                                    kind: TokenKind::Comma,
                                    ..
                                }) => {
                                    self.next_token();
                                    continue;
                                }
                                Some(Token {
                                    kind: TokenKind::SquareBracketClose,
                                    ..
                                }) => break,
                                t => {
                                    break;
                                }
                            };
                        }
                        assert!(
                            matches!(
                                self.curr_token(),
                                Some(Token {
                                    kind: TokenKind::SquareBracketClose,
                                    ..
                                })
                            ),
                            "Parsed square bracket expr but didnt end on a close square bracket"
                        );
                        self.next_token();
                        Some(AstExpr {
                            span: Span {
                                start: self.tokens[start_token_at].span.start,
                                end: self.tokens[self.curr_token_i()].span.end,
                            },
                            kind: ExprKind::Op(Box::new(Op::SquareOpen { left: lhs?, args })),
                            type_id: None,
                        })
                    }
                    TokenKind::BracketOpen => {
                        let mut args = vec![];

                        if let Some(Token {
                            kind: TokenKind::BracketClose,
                            ..
                        }) = self.curr_token()
                        {
                            self.next_token();
                            return Some(AstExpr {
                                span: Span {
                                    start: self.tokens[start_token_at].span.start,
                                    end: self.tokens[self.curr_token_i()].span.end,
                                },
                                kind: ExprKind::Op(Box::new(Op::FnCall { ident: lhs?, args })),
                                type_id: None,
                            });
                        }

                        loop {
                            if let Some(arg) = self.parse_expr(0, symbols) {
                                args.push(arg);
                            }
                            match self.curr_token() {
                                Some(Token {
                                    kind: TokenKind::Comma,
                                    ..
                                }) => {
                                    self.next_token();
                                    continue;
                                }
                                Some(Token {
                                    kind: TokenKind::BracketClose,
                                    ..
                                }) => break,
                                _ => {
                                    break;
                                }
                            };
                        }
                        assert!(
                            matches!(
                                self.curr_token(),
                                Some(Token {
                                    kind: TokenKind::BracketClose,
                                    ..
                                })
                            ),
                            "Parsed bracket expr but didnt end on a close bracket"
                        );
                        self.next_token();
                        Some(AstExpr {
                            span: Span {
                                start: self.tokens[start_token_at].span.start,
                                end: self.tokens[self.curr_token_i()].span.end,
                            },
                            kind: ExprKind::Op(Box::new(Op::FnCall { ident: lhs?, args })),
                            type_id: None,
                        })
                    }
                    t => {
                        dbg!(t);
                        todo!()
                        // not sure what cases are supposed to hit here
                        //     Some(AstExpr {
                        //     start_token_at,
                        //     end_token_at: self.curr_token_i(),
                        //     kind: ExprKind::Op(op.clone(), vec![lhs?]),
                        // })
                    }
                };
                continue;
            }

            if let Some((l_bp, r_bp)) = infix_binding_power(&op_token) {
                if l_bp < min_bp {
                    break;
                }

                self.next_token();
                let rhs = self.parse_expr(r_bp, symbols);

                let kind = match &op_token {
                    TokenKind::Add => Op::Add {
                        left: lhs?,
                        right: rhs?,
                    },
                    TokenKind::Subtract => Op::Minus {
                        left: lhs?,
                        right: rhs?,
                    },
                    TokenKind::Slash => Op::Divide {
                        left: lhs?,
                        right: rhs?,
                    },
                    TokenKind::Astrix => Op::Multiply {
                        left: lhs?,
                        right: rhs?,
                    },
                    TokenKind::Dot => Op::Dot {
                        left: lhs?,
                        right: rhs?,
                    },
                    t => {
                        dbg!(t);
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

fn prefix_binding_power(op_token: &TokenKind) -> ((), u8) {
    match op_token {
        TokenKind::Subtract => ((), 5),
        TokenKind::Amp => ((), 11),
        _ => panic!("bad op: {:?}", op_token),
    }
}

fn postfix_binding_power(op_token: &TokenKind) -> Option<(u8, ())> {
    let res = match op_token {
        // Op::PostQuestion |
        TokenKind::SquareBracketOpen | TokenKind::BracketOpen => (7, ()),
        _ => return None,
    };
    Some(res)
}
fn infix_binding_power(op_token: &TokenKind) -> Option<(u8, u8)> {
    match op_token {
        TokenKind::Add | TokenKind::Subtract => Some((1, 2)),
        TokenKind::Astrix | TokenKind::Slash => Some((3, 4)),
        TokenKind::Dot => Some((10, 9)),
        _ => None,
    }
}

impl Ast {
    pub fn expr_to_debug(&self, expr: &AstExpr) -> DebugExprKind {
        match &expr.kind {
            ExprKind::Atom(atom) => match atom {
                Atom::Ident(v) => DebugExprKind::Atom(DebugAtom::Ident(
                    self.interner.read().resolve(v.0).to_string(),
                )),
                Atom::Int(v) => DebugExprKind::Atom(DebugAtom::Int(*v)),
                Atom::Bool(v) => DebugExprKind::Atom(DebugAtom::Bool(*v)),
                Atom::Str(v) => match &self.tokens[*v].kind {
                    TokenKind::Str(v) => DebugExprKind::Atom(DebugAtom::Str(v.clone())),
                    _ => unreachable!(),
                },
                Atom::CStr(v) => match &self.tokens[*v].kind {
                    TokenKind::CStr(v) => DebugExprKind::Atom(DebugAtom::CStr(v.clone())),
                    _ => unreachable!(),
                },
            },
            ExprKind::Op(op) => DebugExprKind::Op(Box::new(match &**op {
                Op::Add { left, right } => DebugOp::Add {
                    left: self.expr_to_debug(left),
                    right: self.expr_to_debug(right),
                },
                Op::Divide { left, right } => DebugOp::Divide {
                    left: self.expr_to_debug(left),
                    right: self.expr_to_debug(right),
                },
                Op::Minus { left, right } => DebugOp::Minus {
                    left: self.expr_to_debug(left),
                    right: self.expr_to_debug(right),
                },
                Op::Neg(ast_expr) => DebugOp::Neg(self.expr_to_debug(ast_expr)),
                Op::Ref(ast_expr) => DebugOp::Ref(self.expr_to_debug(ast_expr)),
                Op::Multiply { left, right } => DebugOp::Multiply {
                    left: self.expr_to_debug(left),
                    right: self.expr_to_debug(right),
                },
                Op::FnCall { ident, args } => DebugOp::FnCall {
                    ident: self.expr_to_debug(ident),
                    args: args.iter().map(|arg| self.expr_to_debug(arg)).collect(),
                },
                Op::Dot { left, right } => DebugOp::Dot {
                    left: self.expr_to_debug(left),
                    right: self.expr_to_debug(right),
                },
                Op::Block(ast_block) => todo!(),
                Op::Equivalent { left, right } => DebugOp::Equivalent {
                    left: self.expr_to_debug(left),
                    right: self.expr_to_debug(right),
                },
                Op::SquareOpen { left, args } => DebugOp::SquareOpen {
                    left: self.expr_to_debug(left),
                    args: args.iter().map(|arg| self.expr_to_debug(arg)).collect(),
                },
                Op::BracketOpen { left, right } => DebugOp::BracketOpen {
                    left: self.expr_to_debug(left),
                    right: self.expr_to_debug(right),
                },
                Op::IfCond {
                    condition,
                    block,
                    else_ifs,
                    unconditional_else: else_clause,
                } => todo!(),
            })),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum DebugAtom {
    Ident(String),
    Int(i32),
    Bool(bool),
    Str(String),
    CStr(String),
}
#[derive(Debug, PartialEq)]
pub enum DebugExprKind {
    Atom(DebugAtom),
    Op(Box<DebugOp>),
}

#[derive(Debug, PartialEq)]
pub enum DebugOp {
    Add {
        left: DebugExprKind,
        right: DebugExprKind,
    },
    Divide {
        left: DebugExprKind,
        right: DebugExprKind,
    },
    Minus {
        left: DebugExprKind,
        right: DebugExprKind,
    },
    Neg(DebugExprKind),
    Ref(DebugExprKind),
    Multiply {
        left: DebugExprKind,
        right: DebugExprKind,
    },
    FnCall {
        ident: DebugExprKind,
        args: Vec<DebugExprKind>,
    },
    Dot {
        left: DebugExprKind,
        right: DebugExprKind,
    },
    Equivalent {
        left: DebugExprKind,
        right: DebugExprKind,
    },
    SquareOpen {
        left: DebugExprKind,
        args: Vec<DebugExprKind>,
    },
    BracketOpen {
        left: DebugExprKind,
        right: DebugExprKind,
    },
}
#[cfg(test)]
mod test {
    use crate::{
        ast::{
            Ast,
            ast_expr::{DebugAtom, DebugExprKind, DebugOp},
        },
        lexer::Lexer,
    };
    use pretty_assertions::assert_eq;

    fn parse_debug(src: &str) -> DebugExprKind {
        let lexer = Lexer::from_src_str(src.to_string()).unwrap();
        let mut ast = Ast::new(lexer.tokens);
        ast.next_token();
        let expr = ast.parse_expr(0).unwrap();
        ast.expr_to_debug(&expr)
    }

    #[test]
    fn basic_expr() {
        let debug_expr = parse_debug("1 + 2 - 3 * 4 / 5");
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
        let debug_expr = parse_debug("(1 + (2 - 3) * (4 / 5))");
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
        let debug_expr = parse_debug("foo[5 - 1]");
        let expected = DebugExprKind::Op(Box::new(DebugOp::SquareOpen {
            left: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
            args: vec![DebugExprKind::Op(Box::new(DebugOp::Minus {
                left: DebugExprKind::Atom(DebugAtom::Int(5)),
                right: DebugExprKind::Atom(DebugAtom::Int(1)),
            }))],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn multi_squared_brackets() {
        let debug_expr = parse_debug("foo[5 - 1][2][bar]");
        let expected = DebugExprKind::Op(Box::new(DebugOp::SquareOpen {
            left: DebugExprKind::Op(Box::new(DebugOp::SquareOpen {
                left: DebugExprKind::Op(Box::new(DebugOp::SquareOpen {
                    left: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
                    args: vec![DebugExprKind::Op(Box::new(DebugOp::Minus {
                        left: DebugExprKind::Atom(DebugAtom::Int(5)),
                        right: DebugExprKind::Atom(DebugAtom::Int(1)),
                    }))],
                })),
                args: vec![DebugExprKind::Atom(DebugAtom::Int(2))],
            })),
            args: vec![DebugExprKind::Atom(DebugAtom::Ident("bar".to_string()))],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn multi_array() {
        let debug_expr = parse_debug("foo[5 - 1, 2, 12390][2]");
        let expected = DebugExprKind::Op(Box::new(DebugOp::SquareOpen {
            left: DebugExprKind::Op(Box::new(DebugOp::SquareOpen {
                left: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
                args: vec![
                    DebugExprKind::Op(Box::new(DebugOp::Minus {
                        left: DebugExprKind::Atom(DebugAtom::Int(5)),
                        right: DebugExprKind::Atom(DebugAtom::Int(1)),
                    })),
                    DebugExprKind::Atom(DebugAtom::Int(2)),
                    DebugExprKind::Atom(DebugAtom::Int(12390)),
                ],
            })),
            args: vec![DebugExprKind::Atom(DebugAtom::Int(2))],
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn fn_call() {
        let debug_expr = parse_debug("foo(bar) + 5");
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
        let debug_expr = parse_debug("foo(bar, baz, 5)");
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
    fn unary_negation() {
        let debug_expr = parse_debug("-42");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Atom(
            DebugAtom::Int(42),
        ))));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn double_negation() {
        let debug_expr = parse_debug("--5");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Neg(DebugExprKind::Op(Box::new(
            DebugOp::Neg(DebugExprKind::Atom(DebugAtom::Int(5))),
        )))));
        assert_eq!(debug_expr, expected);
    }
    #[test]
    fn precedence_mixed() {
        let debug_expr = parse_debug("1 + 2 * 3 + 4");
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
    fn nested_fn_calls() {
        let debug_expr = parse_debug("foo(bar(baz), 1)");
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

    #[test]
    fn chained_dots() {
        let debug_expr = parse_debug("foo.bar.baz.last");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Dot {
            left: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
            right: DebugExprKind::Op(Box::new(DebugOp::Dot {
                left: DebugExprKind::Atom(DebugAtom::Ident("bar".to_string())),
                right: DebugExprKind::Op(Box::new(DebugOp::Dot {
                    left: DebugExprKind::Atom(DebugAtom::Ident("baz".to_string())),
                    right: DebugExprKind::Atom(DebugAtom::Ident("last".to_string())),
                })),
            })),
        }));
        assert_eq!(debug_expr, expected);
    }

    #[test]
    fn mixed_call_index_dot() {
        let debug_expr = parse_debug("foo(bar)[baz].qux");
        let expected = DebugExprKind::Op(Box::new(DebugOp::Dot {
            left: DebugExprKind::Op(Box::new(DebugOp::SquareOpen {
                left: DebugExprKind::Op(Box::new(DebugOp::FnCall {
                    ident: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
                    args: vec![DebugExprKind::Atom(DebugAtom::Ident("bar".to_string()))],
                })),
                args: vec![DebugExprKind::Atom(DebugAtom::Ident("baz".to_string()))],
            })),
            right: DebugExprKind::Atom(DebugAtom::Ident("qux".to_string())),
        }));
        assert_eq!(debug_expr, expected);
    }
    #[test]
    fn string_and_cstr_literals() {
        let debug_expr = parse_debug(r#"foo("bar", c"baz")"#);
        let expected = DebugExprKind::Op(Box::new(DebugOp::FnCall {
            ident: DebugExprKind::Atom(DebugAtom::Ident("foo".to_string())),
            args: vec![
                DebugExprKind::Atom(DebugAtom::Str("bar".to_string())),
                DebugExprKind::Atom(DebugAtom::CStr("baz".to_string())),
            ],
        }));
        assert_eq!(debug_expr, expected);
    }
}
