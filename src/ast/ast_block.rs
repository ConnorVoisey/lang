use crate::{
    ast::{
        Ast,
        ast_expr::{AstExpr, Atom, ExprKind, Op},
        error::AstParseError,
    },
    interner::IdentId,
    lexer::{Span, Token, TokenKind},
    symbols::{SymbolId, SymbolKind, SymbolTable},
    types::TypeId,
};

/// The left-hand side of an assignment statement.
///
/// Structurally a subset of expressions, but with the constraint that every
/// node in the tree must be an assignable memory location. Lvalue validation
/// happens at parse time via `expr_to_lvalue`.
#[derive(Debug)]
pub enum LvalueKind {
    Ident {
        ident_id: IdentId,
        symbol_id: Option<SymbolId>, // filled in by symbol registration
    },
    ArrayAccess {
        base: Box<Lvalue>,
        index: AstExpr,
    },
    FieldAccess {
        base: Box<Lvalue>,
        field: IdentId,
    },
    // Deref(AstExpr),  // *foo() = x — writing through a reference, not yet implemented
}

#[derive(Debug)]
pub struct Lvalue {
    pub span: Span,
    pub kind: LvalueKind,
}

impl Lvalue {
    /// Walk the lvalue tree to find the root `SymbolId` (the named variable being written to).
    /// For a plain ident, that's the ident's symbol. For `arr[i]` or `obj.field`, it's the
    /// symbol of the outermost named variable (`arr` / `obj`).
    pub fn root_symbol(&self) -> Option<SymbolId> {
        match &self.kind {
            LvalueKind::Ident { symbol_id, .. } => *symbol_id,
            LvalueKind::ArrayAccess { base, .. } => base.root_symbol(),
            LvalueKind::FieldAccess { base, .. } => base.root_symbol(),
        }
    }
}

/// Convert a parsed expression into a `Lvalue`.
///
/// Returns `Err(span)` where `span` is the byte-range of the offending
/// sub-expression when the expression cannot be an assignment target.
pub fn expr_to_lvalue(expr: AstExpr) -> Result<Lvalue, Span> {
    let span = expr.span.clone();
    match expr.kind {
        ExprKind::Atom(Atom::Ident((ident_id, symbol_id))) => Ok(Lvalue {
            span,
            kind: LvalueKind::Ident {
                ident_id,
                symbol_id,
            },
        }),
        ExprKind::Op(op) => match *op {
            Op::ArrayAccess { left, right } => {
                let base = expr_to_lvalue(left).map_err(|_| span.clone())?;
                Ok(Lvalue {
                    span,
                    kind: LvalueKind::ArrayAccess {
                        base: Box::new(base),
                        index: right,
                    },
                })
            }
            Op::Dot { left, right } => {
                let base = expr_to_lvalue(left).map_err(|_| span.clone())?;
                match right.kind {
                    ExprKind::Atom(Atom::Ident((field, _))) => Ok(Lvalue {
                        span,
                        kind: LvalueKind::FieldAccess {
                            base: Box::new(base),
                            field,
                        },
                    }),
                    _ => Err(span),
                }
            }
            _ => Err(span),
        },
        _ => Err(span),
    }
}

#[derive(Debug)]
pub struct AstBlock {
    pub block_open_token_at: usize,
    pub block_close_token_at: usize,
    pub statements: Vec<AstStatement>,
    pub type_id: Option<TypeId>,
    pub expr_count: u32,
}
#[derive(Debug)]
pub enum StatementKind {
    Decleration {
        symbol_id: SymbolId,
        ident_id: IdentId,
        ident_token_at: usize,
        expr: AstExpr,
    },
    Assignment {
        lhs: Lvalue,
        rhs: AstExpr,
    },
    Expr(AstExpr),
    ExplicitReturn(AstExpr),
    BlockReturn {
        expr: AstExpr,
        is_fn_return: bool,
    },
    WhileLoop {
        condition: AstExpr,
        block: AstBlock,
    },
    Break {
        span: Span,
    },
}
#[derive(Debug)]
pub struct AstStatement {
    pub start_token_at: usize,
    pub kind: StatementKind,
    pub expr_count: u32,
}

impl Ast {
    pub fn parse_block(
        &mut self,
        symbols: &mut SymbolTable,
        is_fn_return: bool,
    ) -> Option<AstBlock> {
        debug_assert!(
            matches!(
                self.curr_token(),
                Some(Token {
                    kind: TokenKind::CurlyBracketOpen,
                    ..
                })
            ),
            "Called parsed block not on a `{{`, got {:?}",
            self.curr_token()
        );
        let block_open_token_at = self.curr_token_i();
        let mut statements = vec![];
        let mut expr_count = 1;
        while let Some(tok) = self.next_token() {
            match &tok.kind {
                TokenKind::CurlyBracketClose => {
                    break;
                }
                _ => {
                    if let Some(statement) = self.parse_statement(symbols, is_fn_return) {
                        expr_count += statement.expr_count;
                        let need_break =
                            matches!(&statement.kind, StatementKind::BlockReturn { .. });
                        statements.push(statement);
                        if need_break {
                            break;
                        }
                    }
                }
            };
        }

        Some(AstBlock {
            block_open_token_at,
            block_close_token_at: self.curr_token_i(),
            statements,
            type_id: None,
            expr_count,
        })
    }

    pub fn parse_statement(
        &mut self,
        symbols: &mut SymbolTable,
        is_fn_return: bool,
    ) -> Option<AstStatement> {
        let start_token_i = self.curr_token_i();
        match self.curr_token() {
            None => {
                self.errs.push(AstParseError::UnexpectedEndOfInput);
                None
            }
            Some(Token {
                kind: TokenKind::LetKeyWord,
                ..
            }) => {
                let (ident_id, ident_span) = match self.next_token() {
                    Some(Token {
                        kind: TokenKind::Ident(ident_id),
                        span,
                    }) => (*ident_id, span.clone()),
                    Some(t) => {
                        let cloned_token = t.clone();
                        self.errs.push(AstParseError::LetExpectedIdent {
                            token: cloned_token,
                        });
                        return None;
                    }
                    None => {
                        self.errs.push(AstParseError::UnexpectedEndOfInput);
                        return None;
                    }
                };
                let symbol_id = symbols.declare(
                    ident_id,
                    SymbolKind::Var(crate::symbols::VarSymbolData {
                        type_id: None,
                        is_used: false,
                        is_mutable: false,
                    }),
                    ident_span,
                );
                assert!(
                    matches!(
                        self.next_token(),
                        Some(Token {
                            kind: TokenKind::Assign,
                            ..
                        })
                    ),
                    "Attempted to define a variable but missed the `=` after the ident"
                );
                self.next_token();
                let expr = self.parse_expr(0, symbols, false)?;
                Some(AstStatement {
                    start_token_at: start_token_i,
                    expr_count: expr.expr_count,
                    kind: StatementKind::Decleration {
                        ident_id,
                        symbol_id,
                        ident_token_at: start_token_i + 1,
                        expr,
                    },
                })
            }
            Some(Token {
                kind: TokenKind::ReturnKeyWord,
                ..
            }) => {
                self.next_token();
                let expr = self.parse_expr(0, symbols, false)?;
                Some(AstStatement {
                    start_token_at: start_token_i,
                    expr_count: expr.expr_count,
                    kind: StatementKind::ExplicitReturn(expr),
                })
            }
            Some(Token {
                kind: TokenKind::BreakKeyWord,
                ..
            }) => {
                self.next_token();
                Some(AstStatement {
                    start_token_at: start_token_i,
                    kind: StatementKind::Break {
                        span: self.curr_token().unwrap().span.clone(),
                    },
                    expr_count: 1,
                })
            }
            Some(Token {
                kind: TokenKind::WhileKeyWord,
                ..
            }) => {
                let start_token_at = self.curr_token_i();
                self.next_token();
                let condition = self.parse_expr(0, symbols, true)?;
                let block = self.parse_block(symbols, false)?;
                Some(AstStatement {
                    start_token_at,
                    expr_count: condition.expr_count + block.expr_count,
                    kind: StatementKind::WhileLoop { condition, block },
                })
            }
            _ => {
                let start_token_at = self.curr_token_i();
                let expr = self.parse_expr(0, symbols, false)?;
                match self.curr_token() {
                    Some(Token {
                        kind: TokenKind::Assign,
                        ..
                    }) => {
                        let lhs = match expr_to_lvalue(expr) {
                            Ok(lvalue) => lvalue,
                            Err(span) => {
                                self.errs
                                    .push(AstParseError::InvalidAssignmentTarget { span });
                                return None;
                            }
                        };
                        self.next_token();
                        let rhs = self.parse_expr(0, symbols, false)?;
                        Some(AstStatement {
                            start_token_at,
                            expr_count: rhs.expr_count + 1,
                            kind: StatementKind::Assignment { lhs, rhs },
                        })
                    }
                    _ => Some(AstStatement {
                        start_token_at,
                        expr_count: expr.expr_count + 1,
                        kind: match self.curr_token() {
                            Some(Token {
                                kind: TokenKind::CurlyBracketClose,
                                ..
                            }) => StatementKind::BlockReturn { expr, is_fn_return },
                            _ => StatementKind::Expr(expr),
                        },
                    }),
                }
            }
        }
    }
}
