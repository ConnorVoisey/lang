use crate::{
    ast::{
        Ast,
        ast_block::{AstStatement, Lvalue, LvalueKind, StatementKind},
        ast_expr::{AstExpr, Atom, ExprKind, Op, match_expr::MatchOn},
    },
    interner::{Interner, SharedInterner},
    lexer::{Lexer, TokenKind},
    symbols::SymbolTable,
};
use parking_lot::RwLock;

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
                Op::DoubleColon { left, right } => DebugOp::DoubleColon {
                    left: self.expr_to_debug(left),
                    right: self.expr_to_debug(right),
                },
                Op::Block(block) => DebugOp::Block {
                    statements: block
                        .statements
                        .iter()
                        .map(|stmt| self.statement_to_debug(stmt))
                        .collect(),
                },
                Op::Equivalent { left, right } => DebugOp::Equivalent {
                    left: self.expr_to_debug(left),
                    right: self.expr_to_debug(right),
                },
                Op::NotEquivalent { left, right } => DebugOp::NotEquivalent {
                    left: self.expr_to_debug(left),
                    right: self.expr_to_debug(right),
                },
                Op::BinInverse(expr) => DebugOp::BinInverse(self.expr_to_debug(expr)),
                Op::ArrayAccess { left, right } => DebugOp::ArrayAccess {
                    left: self.expr_to_debug(left),
                    right: self.expr_to_debug(right),
                },
                Op::ArrayInit { args } => DebugOp::ArrayInit {
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
                    unconditional_else,
                } => DebugOp::IfCond {
                    condition: self.expr_to_debug(condition),
                    block: block
                        .statements
                        .iter()
                        .map(|stmt| self.statement_to_debug(stmt))
                        .collect(),
                    else_ifs: else_ifs
                        .iter()
                        .map(|(cond, blk)| {
                            (
                                self.expr_to_debug(cond),
                                blk.statements
                                    .iter()
                                    .map(|stmt| self.statement_to_debug(stmt))
                                    .collect(),
                            )
                        })
                        .collect(),
                    unconditional_else: unconditional_else.as_ref().map(|blk| {
                        blk.statements
                            .iter()
                            .map(|stmt| self.statement_to_debug(stmt))
                            .collect()
                    }),
                },
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
                Op::Match { on, cases } => DebugOp::Match {
                    on: self.expr_to_debug(on),
                    cases: cases
                        .iter()
                        .map(|branch| DebugMatchBranch {
                            on: self.match_on_to_debug(&branch.on),
                            expr: self.expr_to_debug(&branch.expr),
                        })
                        .collect(),
                },
            })),
        }
    }

    fn match_on_to_debug(&self, match_on: &MatchOn) -> DebugMatchOn {
        match match_on {
            MatchOn::Int(v) => DebugMatchOn::Int(*v),
            MatchOn::Bool(v) => DebugMatchOn::Bool(*v),
            MatchOn::Str(v) => DebugMatchOn::Str(v.clone()),
            MatchOn::Ident((ident, _)) => {
                DebugMatchOn::Ident(self.interner.read().resolve(*ident).to_string())
            }
            MatchOn::Struct {
                ident_id,
                symbol_id: _,
                args,
                disgard_rest,
            } => DebugMatchOn::Struct {
                ident: self.interner.read().resolve(*ident_id).to_string(),
                args: args
                    .iter()
                    .map(|(ident, match_on)| {
                        (
                            self.interner.read().resolve(*ident).to_string(),
                            self.match_on_to_debug(match_on),
                        )
                    })
                    .collect(),
                disgard_rest: *disgard_rest,
            },
            MatchOn::Enum {
                ident_id,
                symbol_id: _,
                variant_id,
                params,
            } => DebugMatchOn::Enum {
                ident: self.interner.read().resolve(*ident_id).to_string(),
                variant: self.interner.read().resolve(*variant_id).to_string(),
                params: Box::new(match &**params {
                    Some(match_on) => Some(self.match_on_to_debug(match_on)),
                    None => None,
                }),
            },
        }
    }
    pub fn lvalue_to_debug_expr(&self, lvalue: &Lvalue) -> DebugExprKind {
        match &lvalue.kind {
            LvalueKind::Ident { ident_id, .. } => DebugExprKind::Atom(DebugAtom::Ident(
                self.interner.read().resolve(*ident_id).to_string(),
            )),
            LvalueKind::ArrayAccess { base, index } => {
                DebugExprKind::Op(Box::new(DebugOp::ArrayAccess {
                    left: self.lvalue_to_debug_expr(base),
                    right: self.expr_to_debug(index),
                }))
            }
            LvalueKind::FieldAccess { base, field } => DebugExprKind::Op(Box::new(DebugOp::Dot {
                left: self.lvalue_to_debug_expr(base),
                right: DebugExprKind::Atom(DebugAtom::Ident(
                    self.interner.read().resolve(*field).to_string(),
                )),
            })),
        }
    }

    pub fn statement_to_debug(&self, stmt: &AstStatement) -> DebugStatement {
        match &stmt.kind {
            StatementKind::Decleration { ident_id, expr, .. } => DebugStatement::Declaration {
                ident: self.interner.read().resolve(*ident_id).to_string(),
                expr: self.expr_to_debug(expr),
            },
            StatementKind::Assignment { lhs, rhs } => DebugStatement::Assignment {
                lhs: self.lvalue_to_debug_expr(lhs),
                rhs: self.expr_to_debug(rhs),
            },
            StatementKind::Expr(expr) => DebugStatement::Expr(self.expr_to_debug(expr)),
            StatementKind::ExplicitReturn(expr) => {
                DebugStatement::ExplicitReturn(self.expr_to_debug(expr))
            }
            StatementKind::BlockReturn { expr, is_fn_return } => DebugStatement::BlockReturn {
                expr: self.expr_to_debug(expr),
                is_fn_return: *is_fn_return,
            },
            StatementKind::WhileLoop { condition, block } => DebugStatement::WhileLoop {
                condition: self.expr_to_debug(condition),
                block: block
                    .statements
                    .iter()
                    .map(|stmt| self.statement_to_debug(stmt))
                    .collect(),
            },
            StatementKind::Break { .. } => DebugStatement::Break,
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum DebugStatement {
    Declaration {
        ident: String,
        expr: DebugExprKind,
    },
    Assignment {
        lhs: DebugExprKind,
        rhs: DebugExprKind,
    },
    Expr(DebugExprKind),
    ExplicitReturn(DebugExprKind),
    BlockReturn {
        expr: DebugExprKind,
        is_fn_return: bool,
    },
    WhileLoop {
        condition: DebugExprKind,
        block: Vec<DebugStatement>,
    },
    Break,
}

#[derive(Debug, PartialEq)]
pub enum DebugAtom {
    Ident(String),
    Int(i128),
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
    DoubleColon {
        left: DebugExprKind,
        right: DebugExprKind,
    },
    Equivalent {
        left: DebugExprKind,
        right: DebugExprKind,
    },
    NotEquivalent {
        left: DebugExprKind,
        right: DebugExprKind,
    },
    BinInverse(DebugExprKind),
    ArrayAccess {
        left: DebugExprKind,
        right: DebugExprKind,
    },
    ArrayInit {
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
    Block {
        statements: Vec<DebugStatement>,
    },
    IfCond {
        condition: DebugExprKind,
        block: Vec<DebugStatement>,
        else_ifs: Vec<(DebugExprKind, Vec<DebugStatement>)>,
        unconditional_else: Option<Vec<DebugStatement>>,
    },
    Match {
        on: DebugExprKind,
        cases: Vec<DebugMatchBranch>,
    },
}

#[derive(Debug, PartialEq)]
pub enum DebugMatchOn {
    Int(i128),
    Bool(bool),
    Str(String),
    Ident(String),
    Struct {
        ident: String,
        args: Vec<(String, DebugMatchOn)>,
        disgard_rest: bool,
    },
    Enum {
        ident: String,
        variant: String,
        params: Box<Option<DebugMatchOn>>,
    },
}

#[derive(Debug, PartialEq)]
pub struct DebugMatchBranch {
    pub on: DebugMatchOn,
    pub expr: DebugExprKind,
}

pub fn parse_debug_setup(src: &str) -> (Ast, SymbolTable) {
    let interner = Interner::new();
    let shared_interner = SharedInterner::new(RwLock::new(interner));
    let symbols = SymbolTable::new(shared_interner.clone());
    let lexer = Lexer::from_src_str(src, &shared_interner).unwrap();
    let ast = Ast::new(lexer.tokens, shared_interner.clone());
    (ast, symbols)
}
pub fn parse_debug(src: &str) -> DebugExprKind {
    let (mut ast, mut symbols) = parse_debug_setup(src);
    ast.next_token();
    let expr = ast.parse_expr(0, &mut symbols, false).unwrap();
    ast.expr_to_debug(&expr)
}
