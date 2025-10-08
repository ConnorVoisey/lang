use rustc_hash::FxHashMap;

use crate::{
    hlir::{
        BinaryOp, Block, BlockId, FuncMetadata, Function, Instr, InstrId, LocalSlot, SpanId,
        UnaryOp, ValueId, ValueInfo,
    },
    interner::SharedInterner,
    symbols::SymbolId,
    types::{TypeArena, TypeId},
};

pub struct FunctionBuilder<'a> {
    func: Function,
    current_block: Option<BlockId>,
    type_arena: &'a TypeArena,
    interner: SharedInterner,
}

impl<'a> FunctionBuilder<'a> {
    pub fn new(name: SymbolId, type_arena: &'a TypeArena, interner: SharedInterner) -> Self {
        let entry_block = Block {
            id: BlockId(0),
            params: Vec::new(),
            instr_begin: 0,
            instr_end: 0,
            successors: Vec::new(),
            predecessors: Vec::new(),
            span: SpanId(0),
        };
        Self {
            func: Function {
                name,
                params: Vec::new(),
                blocks: vec![entry_block],
                instrs: Vec::new(),
                values: Vec::new(),
                entry: BlockId(0),
                locals: Vec::new(),
                metadata: FuncMetadata {
                    span: SpanId(0),
                    is_inline_hint: false,
                    is_exported: false,
                },
                symbols: FxHashMap::default(),
            },
            current_block: Some(BlockId(0)),
            type_arena,
            interner,
        }
    }

    pub fn current_block(&self) -> BlockId {
        self.current_block.expect("No active block")
    }

    pub fn create_block(&mut self) -> BlockId {
        let id = BlockId(self.func.blocks.len());
        self.func.blocks.push(Block {
            id,
            params: Vec::new(),
            instr_begin: self.func.instrs.len(),
            instr_end: self.func.instrs.len(),
            successors: Vec::new(),
            predecessors: Vec::new(),
            span: SpanId(0),
        });
        id
    }

    pub fn switch_to_block(&mut self, id: BlockId) {
        self.current_block = Some(id);
    }

    pub fn append_instr(&mut self, instr: Instr, ty: Option<TypeId>) -> Option<ValueId> {
        let instr_id = InstrId(self.func.instrs.len());
        self.func.instrs.push(instr);
        if let Some(ty) = ty {
            let val_id = ValueId(self.func.values.len());
            self.func.values.push(ValueInfo {
                id: val_id,
                ty,
                def: instr_id,
                span: SpanId(0),
            });
            Some(val_id)
        } else {
            None
        }
    }

    pub fn emit_binary(&mut self, op: BinaryOp, lhs: ValueId, rhs: ValueId, ty: TypeId) -> ValueId {
        self.append_instr(Instr::Binary { op, lhs, rhs }, Some(ty))
            .unwrap()
    }

    pub fn emit_unary(&mut self, op: UnaryOp, arg: ValueId, ty: TypeId) -> ValueId {
        self.append_instr(Instr::Unary { op, arg }, Some(ty))
            .unwrap()
    }

    pub fn emit_jump(&mut self, target: BlockId) {
        self.append_instr(Instr::Jump { target }, None);
    }

    pub fn emit_branch(&mut self, cond: ValueId, t: BlockId, f: BlockId) {
        self.append_instr(
            Instr::Branch {
                cond,
                if_true: t,
                if_false: f,
            },
            None,
        );
    }

    pub fn emit_return(&mut self, values: Vec<ValueId>) {
        self.append_instr(Instr::Return { values }, None);
    }

    pub fn finish(self) -> Function {
        self.func
    }

    pub fn emit_local(&mut self) -> ValueId {
        let id = self.func.locals.len();
        self.func.locals.push(LocalSlot {
            name: todo!(),
            ty: todo!(),
            slot_index: todo!(),
        });
    }

    pub fn assign_symbol(&mut self, symbol_id: SymbolId, value_id: ValueId) {
        self.func.symbols.insert(symbol_id, value_id);
    }
    pub fn get_symbol(&self, symbol_id: SymbolId) -> ValueId {
        *self
            .func
            .symbols
            .get(&symbol_id)
            .expect("Called get_symbol on a symbol that has not been declared yet")
    }
}
