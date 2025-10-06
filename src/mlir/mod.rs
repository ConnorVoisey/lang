use rustc_hash::FxHashMap;

use crate::{
    ast::{
        Ast,
        ast_block::{AstStatement, StatementKind},
        ast_expr::{AstExpr, Atom, ExprKind, Op},
    },
    interner::{IdentId, SharedInterner},
    mlir::func::FunctionBuilder,
    symbols::SymbolId,
    types::{TypeArena, TypeId},
};
pub mod func;
pub mod module;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct ValueId(usize);

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct InstrId(usize);

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct BlockId(usize);

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct FuncId(usize);

// TODO: move this so it is generated whilst parsing the ast, or maybe even the lexer
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct SpanId(usize);

pub struct Module<'a> {
    pub types: &'a TypeArena,
    pub funcs: Vec<Function>,
    pub interner: SharedInterner,
}

// Per-function SSA container (function-local memory)
pub struct Function {
    name: SymbolId,
    params: Vec<(SymbolId, TypeId)>,
    blocks: Vec<Block>,
    instrs: Vec<Instr>,
    values: Vec<ValueInfo>,
    entry: BlockId,
    locals: Vec<LocalSlot>,
    metadata: FuncMetadata,
    symbols: FxHashMap<SymbolId, ValueId>,
}

// Basic block
pub struct Block {
    id: BlockId,
    params: Vec<ValueId>,
    instr_begin: usize,
    instr_end: usize,
    successors: Vec<BlockId>,
    predecessors: Vec<BlockId>,
    span: SpanId,
}

// Value info: every computed value has a type and a defining InstrId
pub struct ValueInfo {
    id: ValueId,
    ty: TypeId,
    def: InstrId,
    span: SpanId,
}

// Local slots for stackified allocs, etc.
pub struct LocalSlot {
    name: IdentId,
    ty: TypeId,
    slot_index: u32, // used at lowering for frame layout
}

pub enum Instr {
    Unary {
        op: UnaryOp,
        arg: ValueId,
    },
    Binary {
        op: BinaryOp,
        lhs: ValueId,
        rhs: ValueId,
    },

    // FieldAccess {
    //     base: ValueId,
    //     field_index: u32,
    // },
    Jump {
        target: BlockId,
    },
    Branch {
        cond: ValueId,
        if_true: BlockId,
        if_false: BlockId,
    },
    Return {
        values: Vec<ValueId>,
    },

    Call {
        callee: CalleeRef,
        args: Vec<ValueId>,
        ret_tys: Vec<TypeId>,
    },

    Load {
        addr: ValueId,
        ty: TypeId,
    },
    Store {
        addr: ValueId,
        val: ValueId,
    },
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnaryOp {
    Neg,
    Not,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Function reference — either static or dynamic
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum CalleeRef {
    Direct(FuncId),
    Indirect(ValueId),
}

/// Simple function-level metadata (debug, optimization flags, etc.)
#[derive(Clone, Debug)]
pub struct FuncMetadata {
    pub span: SpanId,
    pub is_inline_hint: bool,
    pub is_exported: bool,
}

impl<'a> Module<'a> {
    pub fn from_ast(self, ast: &Ast, types: &'a TypeArena) -> Self {
        let module = Self {
            types,
            funcs: Vec::with_capacity(ast.fns.len()),
            interner: ast.interner.clone(),
        };

        for func in ast.fns.iter() {
            let mut fb = FunctionBuilder::new(func.symbol_id, types, ast.interner.clone());
            for statement in &func.body.as_ref().unwrap().statements {
                module.parse_statement(&mut fb, &statement.kind);
            }
            fb.finish();
        }
        module
    }
    fn parse_statement(&self, fb: &mut FunctionBuilder<'_>, statement_kind: &StatementKind) {
        match statement_kind {
            StatementKind::Decleration {
                symbol_id,
                ident_id: _,
                ident_token_at: _,
                expr,
            } => {
                if let Some(value_id) = self.parse_expr(fb, expr) {
                    fb.assign_symbol(*symbol_id, value_id);
                }
            }
            StatementKind::Assignment {
                symbol_id,
                ident_id: _,
                ident_token_at: _,
                expr,
            } => {
                if let Some(value_id) = self.parse_expr(fb, expr) {
                    fb.assign_symbol(symbol_id.unwrap(), value_id);
                }
            }
            StatementKind::Expr(ast_expr) => {
                self.parse_expr(fb, ast_expr);
            }
            StatementKind::ExplicitReturn(ast_expr) => todo!(),
            StatementKind::BlockReturn { expr, is_fn_return } => todo!(),
            StatementKind::WhileLoop { condition, block } => todo!(),
        }
    }

    fn parse_expr(&self, fb: &mut FunctionBuilder<'_>, expr: &AstExpr) -> Option<ValueId> {
        match &expr.kind {
            ExprKind::Atom(atom) => match atom {
                Atom::Ident(_) => todo!(),
                Atom::Bool(_) => todo!(),
                Atom::Int(_) => todo!(),
                Atom::Str(_) => todo!(),
                Atom::CStr(_) => todo!(),
            },
            ExprKind::Op(op) => match &**op {
                Op::Add { left, right } => todo!(),
                Op::Divide { left, right } => todo!(),
                Op::Minus { left, right } => todo!(),
                Op::LessThan { left, right } => todo!(),
                Op::LessThanEq { left, right } => todo!(),
                Op::GreaterThan { left, right } => todo!(),
                Op::GreaterThanEq { left, right } => todo!(),
                Op::Neg(ast_expr) => todo!(),
                Op::Ref(ast_expr) => todo!(),
                Op::Multiply { left, right } => todo!(),
                Op::FnCall { ident, args } => todo!(),
                Op::Dot { left, right } => todo!(),
                Op::Block(ast_block) => todo!(),
                Op::Equivalent { left, right } => todo!(),
                Op::SquareOpen { left, args } => todo!(),
                Op::BracketOpen { left, right } => todo!(),
                Op::IfCond {
                    condition,
                    block,
                    else_ifs,
                    unconditional_else,
                } => todo!(),
            },
        }
    }
}
