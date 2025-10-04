use crate::{
    ast::{
        Ast,
        ast_block::{AstStatement, StatementKind},
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
                ident_id,
                ident_token_at,
                expr,
            } => {}
            StatementKind::Assignment {
                symbol_id,
                ident_id,
                ident_token_at,
                expr,
            } => todo!(),
            StatementKind::Expr(ast_expr) => todo!(),
            StatementKind::ExplicitReturn(ast_expr) => todo!(),
            StatementKind::BlockReturn(ast_expr) => todo!(),
        }
    }
}
