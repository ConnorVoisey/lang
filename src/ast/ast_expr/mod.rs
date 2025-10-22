use crate::{
    ast::{Ast, ast_block::AstBlock, error::AstParseError},
    interner::IdentId,
    lexer::{Span, Token, TokenKind},
    symbols::{SymbolId, SymbolTable},
    types::TypeId,
};

pub mod error;
pub mod if_expr;

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

            TokenKind::Subtract => {
                let ((), r_bp) = prefix_binding_power(&TokenKind::Subtract);
                self.next_token();
                let rhs = match self.parse_expr(r_bp, symbols, false) {
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
                let rhs = match self.parse_expr(r_bp, symbols, false) {
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
                        let mut args = vec![];
                        loop {
                            if let Some(arg) = self.parse_expr(0, symbols, false) {
                                args.push(arg);
                            } else {
                                // parse_expr already pushed an error - try to recover
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
                        // ensure we have the close; if not, error already pushed
                        if !matches!(
                            self.curr_token(),
                            Some(Token {
                                kind: TokenKind::SquareBracketClose,
                                ..
                            })
                        ) {
                            // no-op: error already recorded
                        }
                        // consume the close if present
                        if matches!(
                            self.curr_token(),
                            Some(Token {
                                kind: TokenKind::SquareBracketClose,
                                ..
                            })
                        ) {
                            self.next_token();
                        }
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
                                kind: ExprKind::Op(Box::new(Op::FnCall { ident: lhs?, args })),
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
                                    self.errs.push(AstParseError::ExpectedClosingBracket {
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
                            kind: ExprKind::Op(Box::new(Op::FnCall { ident: lhs?, args })),
                            type_id: None,
                        })
                    }

                    TokenKind::CurlyBracketOpen => {
                        // Could be a struct decleration or it could be a block.
                        // Peek ahead to find out
                        if !is_direct_if_cond {
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
                                        t => {
                                            dbg!(t);
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
                                    ident: lhs?,
                                    symbol_id: None,
                                    args,
                                })),
                                type_id: None,
                            })
                        } else {
                            // TODO: this seems quite gross, refactor this at somepoint
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
                let rhs = self.parse_expr(r_bp, symbols, false);
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
        TokenKind::SquareBracketOpen | TokenKind::BracketOpen | TokenKind::CurlyBracketOpen => {
            (7, ())
        }
        _ => return None,
    };
    Some(res)
}
fn infix_binding_power(op_token: &TokenKind) -> Option<(u8, u8)> {
    match op_token {
        TokenKind::Add | TokenKind::Subtract => Some((1, 2)),
        TokenKind::Astrix | TokenKind::Slash => Some((3, 4)),
        TokenKind::Dot => Some((10, 9)),
        TokenKind::LessThan => Some((11, 12)),
        TokenKind::LessThanEq => Some((13, 14)),
        TokenKind::GreaterThan => Some((15, 16)),
        TokenKind::GreaterThanEq => Some((17, 18)),
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
                Op::LessThan { left, right } => DebugOp::LessThan {
                    left: self.expr_to_debug(left),
                    right: self.expr_to_debug(right),
                },
                Op::LessThanEq { left, right } => DebugOp::LessThanEq {
                    left: self.expr_to_debug(left),
                    right: self.expr_to_debug(right),
                },
                Op::GreaterThan { left, right } => DebugOp::GreaterThan {
                    left: self.expr_to_debug(left),
                    right: self.expr_to_debug(right),
                },
                Op::GreaterThanEq { left, right } => DebugOp::GreaterThanEq {
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
                Op::Block(_) => todo!(),
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
                Op::IfCond { .. } => todo!(),
                Op::StructCreate {
                    ident,
                    args,
                    symbol_id: _,
                } => DebugOp::StructCreate {
                    ident: self.expr_to_debug(ident),
                    args: args
                        .iter()
                        .map(|(ident, expr)| {
                            (
                                self.interner.read().resolve(*ident).to_string(),
                                self.expr_to_debug(expr),
                            )
                        })
                        .collect(),
                },
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
    LessThan {
        left: DebugExprKind,
        right: DebugExprKind,
    },
    LessThanEq {
        left: DebugExprKind,
        right: DebugExprKind,
    },
    GreaterThan {
        left: DebugExprKind,
        right: DebugExprKind,
    },
    GreaterThanEq {
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
    StructCreate {
        ident: DebugExprKind,
        args: Vec<(String, DebugExprKind)>,
    },
}
#[cfg(test)]
mod test {
    use crate::{
        ast::{
            Ast,
            ast_expr::{DebugAtom, DebugExprKind, DebugOp},
        },
        interner::{Interner, SharedInterner},
        lexer::Lexer,
        symbols::SymbolTable,
    };
    use parking_lot::RwLock;
    use pretty_assertions::assert_eq;

    fn parse_debug(src: &str) -> DebugExprKind {
        let interner = Interner::new();
        let shared_interner = SharedInterner::new(RwLock::new(interner));
        let mut symbols = SymbolTable::new(shared_interner.clone());
        let lexer = Lexer::from_src_str(src, &shared_interner).unwrap();
        let mut ast = Ast::new(lexer.tokens, shared_interner.clone());
        ast.next_token();
        let expr = ast.parse_expr(0, &mut symbols, false).unwrap();
        ast.expr_to_debug(&expr)
    }

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
        let debug_expr = parse_debug("foo[5 - 1][2][bar];");
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
        let debug_expr = parse_debug("foo[5 - 1, 2, 12390][2];");
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

    #[test]
    fn chained_dots() {
        let debug_expr = parse_debug("foo.bar.baz.last;");
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
        let debug_expr = parse_debug("foo(bar)[baz].qux;");
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
