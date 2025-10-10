use rustc_hash::FxHashMap;

use crate::{
    ast::{
        Ast,
        ast_block::StatementKind,
        ast_expr::{AstExpr, Atom, ExprKind, Op},
    },
    hlir::func::FunctionBuilder,
    interner::{IdentId, SharedInterner},
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
            StatementKind::ExplicitReturn(_) => todo!(),
            StatementKind::BlockReturn {
                expr: _,
                is_fn_return: _,
            } => todo!(),
            StatementKind::WhileLoop {
                condition: _,
                block: _,
            } => todo!(),
            StatementKind::Break { .. } => todo!(),
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
                Op::Add { left: _, right: _ } => todo!(),
                Op::Divide { left: _, right: _ } => todo!(),
                Op::Minus { left: _, right: _ } => todo!(),
                Op::LessThan { left: _, right: _ } => todo!(),
                Op::LessThanEq { left: _, right: _ } => todo!(),
                Op::GreaterThan { left: _, right: _ } => todo!(),
                Op::GreaterThanEq { left: _, right: _ } => todo!(),
                Op::Neg(_) => todo!(),
                Op::Ref(_) => todo!(),
                Op::Multiply { left: _, right: _ } => todo!(),
                Op::FnCall { ident: _, args: _ } => todo!(),
                Op::Dot { left: _, right: _ } => todo!(),
                Op::Block(_) => todo!(),
                Op::Equivalent { left: _, right: _ } => todo!(),
                Op::SquareOpen { left: _, args: _ } => todo!(),
                Op::BracketOpen { left: _, right: _ } => todo!(),
                Op::IfCond {
                    condition: _,
                    block: _,
                    else_ifs: _,
                    unconditional_else: _,
                } => todo!(),
                Op::StructCreate { ident: _, args: _ } => todo!(),
            },
        }
    }
}
