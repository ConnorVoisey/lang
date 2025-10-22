//! Lower RVSDG to Cranelift IR
//!
//! This module converts the high-level RVSDG representation into Cranelift IR.
//! The conversion is designed for minimal overhead and fast compilation.

use super::*;
use crate::{struct_layout::StructLayout, symbols::SymbolTable, types::TypeKind};
use cranelift::prelude::*;
use cranelift_codegen::{
    Context,
    ir::{Function as ClFunction, UserFuncName},
};
use cranelift_module::{FuncId as ClFuncId, Linkage, Module as ClModuleTrait};
use cranelift_object::ObjectModule;
use isa::CallConv;
use rustc_hash::FxHashMap;
use std::collections::HashMap;

pub struct RvsdgToCranelift<'a> {
    module: &'a self::Module<'a>,
    symbols: &'a SymbolTable,
    struct_layouts: &'a [StructLayout],

    // Map RVSDG function IDs to Cranelift function IDs
    func_map: FxHashMap<FunctionId, ClFuncId>,

    // Current function being compiled
    current_function: Option<FunctionId>,
}

pub struct FunctionCompiler<'a, 'b> {
    rvsdg_func: &'a Function,
    module: &'a self::Module<'a>,
    func_map: &'a FxHashMap<FunctionId, ClFuncId>,
    cl_module: &'b mut ObjectModule,

    // Map RVSDG values to Cranelift values
    value_map: HashMap<ValueId, Value>,

    // Cranelift builder
    builder: FunctionBuilder<'a>,

    // Counter for unique string global names
    string_counter: usize,
}

impl<'a> RvsdgToCranelift<'a> {
    pub fn new(
        module: &'a self::Module<'a>,
        symbols: &'a SymbolTable,
        struct_layouts: &'a [StructLayout],
    ) -> Self {
        Self {
            module,
            symbols,
            struct_layouts,
            func_map: FxHashMap::default(),
            current_function: None,
        }
    }

    pub fn compile(
        mut self,
        cl_module: &mut ObjectModule,
        call_conv: CallConv,
    ) -> color_eyre::Result<()> {
        // First pass: declare all functions
        for func in &self.module.functions {
            let cl_func_id = self.declare_function(func, cl_module, call_conv)?;
            self.func_map.insert(func.id, cl_func_id);
        }

        // Declare extern functions
        for extern_fn in &self.module.extern_functions {
            let cl_func_id = self.declare_extern_function(extern_fn, cl_module)?;
            self.func_map.insert(extern_fn.id, cl_func_id);
        }

        // Second pass: compile function bodies
        for func in &self.module.functions {
            self.compile_function(func, cl_module, call_conv)?;
        }

        Ok(())
    }

    fn declare_function(
        &self,
        func: &Function,
        cl_module: &mut ObjectModule,
        call_conv: CallConv,
    ) -> color_eyre::Result<ClFuncId> {
        let mut sig = Signature::new(call_conv);

        // Add parameters
        for param in &func.params {
            let cl_type = self.type_to_cl(param.ty);
            sig.params.push(AbiParam::new(cl_type));
        }

        // Add return type
        let ret_cl_type = self.type_to_cl(func.return_type);
        sig.returns.push(AbiParam::new(ret_cl_type));

        // Get function name
        let name = {
            let symbol = self.symbols.resolve(func.name);
            let reader = self.module.interner.read();
            reader.resolve(symbol.ident_id).to_string()
        };

        let linkage = if func.is_exported {
            Linkage::Export
        } else {
            Linkage::Local
        };

        cl_module
            .declare_function(&name, linkage, &sig)
            .map_err(|e| color_eyre::eyre::eyre!("Failed to declare function: {}", e))
    }

    fn declare_extern_function(
        &self,
        extern_fn: &ExternFunction,
        cl_module: &mut ObjectModule,
    ) -> color_eyre::Result<ClFuncId> {
        let mut sig = cl_module.make_signature();

        // Add parameters
        for &param_ty in &extern_fn.param_types {
            let cl_type = self.type_to_cl(param_ty);
            sig.params.push(AbiParam::new(cl_type));
        }

        // Add return type
        let ret_cl_type = self.type_to_cl(extern_fn.return_type);
        sig.returns.push(AbiParam::new(ret_cl_type));

        // Get function name
        let name = {
            let symbol = self.symbols.resolve(extern_fn.name);
            let reader = self.module.interner.read();
            reader.resolve(symbol.ident_id).to_string()
        };

        cl_module
            .declare_function(&name, Linkage::Import, &sig)
            .map_err(|e| color_eyre::eyre::eyre!("Failed to declare extern function: {}", e))
    }

    fn compile_function(
        &mut self,
        func: &Function,
        cl_module: &mut ObjectModule,
        call_conv: CallConv,
    ) -> color_eyre::Result<()> {
        let cl_func_id = self.func_map[&func.id];

        // Build Cranelift signature
        let mut sig = Signature::new(call_conv);
        for param in &func.params {
            sig.params.push(AbiParam::new(self.type_to_cl(param.ty)));
        }
        sig.returns
            .push(AbiParam::new(self.type_to_cl(func.return_type)));

        // Create Cranelift function
        let mut cl_func = ClFunction::with_name_signature(UserFuncName::user(0, 0), sig);
        let mut func_ctx = FunctionBuilderContext::new();
        let builder = FunctionBuilder::new(&mut cl_func, &mut func_ctx);

        // Compile the function body
        let mut compiler =
            FunctionCompiler::new(func, self.module, &self.func_map, cl_module, builder);
        compiler.compile()?;

        // Define the function
        let mut context = Context::for_function(cl_func);
        cl_module
            .define_function(cl_func_id, &mut context)
            .map_err(|e| color_eyre::eyre::eyre!("Failed to define function: {}", e))
    }

    fn type_to_cl(&self, type_id: TypeId) -> types::Type {
        match self.module.types.kind(type_id) {
            TypeKind::Int => types::I32,
            TypeKind::Uint => types::I32,
            TypeKind::Bool => types::I8,
            TypeKind::Ref(_) => types::I64,
            TypeKind::Struct(_) => types::I64, // Pointer to struct
            TypeKind::Void => types::I32,      // Placeholder
            _ => types::I32,                   // Default fallback
        }
    }
}

impl<'a, 'b> FunctionCompiler<'a, 'b> {
    fn new(
        rvsdg_func: &'a Function,
        module: &'a self::Module<'a>,
        func_map: &'a FxHashMap<FunctionId, ClFuncId>,
        cl_module: &'b mut ObjectModule,
        builder: FunctionBuilder<'a>,
    ) -> Self {
        Self {
            rvsdg_func,
            module,
            func_map,
            cl_module,
            value_map: HashMap::new(),
            builder,
            string_counter: 0,
        }
    }

    fn compile(mut self) -> color_eyre::Result<()> {
        // Create entry block
        let entry_block = self.builder.create_block();
        self.builder.switch_to_block(entry_block);
        self.builder
            .append_block_params_for_function_params(entry_block);

        // Map function parameters
        for (i, param) in self.rvsdg_func.params.iter().enumerate() {
            let cl_param = self.builder.block_params(entry_block)[i];
            // Create a ValueId for this parameter
            let param_node = NodeId(i); // Assuming parameters are the first nodes
            let param_value = ValueId {
                node: param_node,
                output_index: 0,
            };
            self.value_map.insert(param_value, cl_param);
        }

        // Compile the root lambda node
        let root_node = self.rvsdg_func.node(self.rvsdg_func.root);
        if let NodeKind::Lambda { region } = &root_node.kind {
            // For now, just return a dummy value
            // TODO: Properly compile the lambda region
            let dummy_ret = self.builder.ins().iconst(types::I32, 0);
            self.builder.ins().return_(&[dummy_ret]);
        }

        self.builder.seal_all_blocks();
        self.builder.finalize();

        Ok(())
    }

    fn compile_region(&mut self, region_id: RegionId) -> color_eyre::Result<Vec<Value>> {
        // TODO: Implement region compilation
        // This would iterate through nodes in the region and compile them
        Ok(vec![])
    }

    fn compile_node(&mut self, node: &Node) -> color_eyre::Result<Option<Value>> {
        match &node.kind {
            NodeKind::Const { value } => {
                let cl_val = match value {
                    ConstValue::I64(i) => self.builder.ins().iconst(types::I32, *i),
                    ConstValue::U64(u) => self.builder.ins().iconst(types::I32, *u as i64),
                    ConstValue::Bool(b) => self.builder.ins().iconst(types::I8, *b as i64),
                    ConstValue::String(bytes) => {
                        // Declare global data for the string
                        let global_name =
                            format!("str_{}_{}", self.rvsdg_func.id.0, self.string_counter);
                        self.string_counter += 1;

                        let data_id = self
                            .cl_module
                            .declare_data(&global_name, Linkage::Local, false, false)
                            .map_err(|e| {
                                color_eyre::eyre::eyre!("Failed to declare string data: {}", e)
                            })?;

                        // Define the global data with the string bytes
                        let mut data_desc = cranelift_module::DataDescription::new();
                        data_desc.define(bytes.clone().into_boxed_slice());
                        self.cl_module
                            .define_data(data_id, &data_desc)
                            .map_err(|e| {
                                color_eyre::eyre::eyre!("Failed to define string data: {}", e)
                            })?;

                        // Get a pointer to the global data
                        let global_value = self
                            .cl_module
                            .declare_data_in_func(data_id, self.builder.func);
                        self.builder.ins().global_value(types::I64, global_value)
                    }
                };
                Ok(Some(cl_val))
            }

            NodeKind::Binary { op, .. } => {
                // Get input values
                let lhs = self.get_value(node.inputs[0])?;
                let rhs = self.get_value(node.inputs[1])?;

                let result = match op {
                    BinaryOp::Add => self.builder.ins().iadd(lhs, rhs),
                    BinaryOp::Sub => self.builder.ins().isub(lhs, rhs),
                    BinaryOp::Mul => self.builder.ins().imul(lhs, rhs),
                    BinaryOp::Div => self.builder.ins().sdiv(lhs, rhs),
                    BinaryOp::Lt => self.builder.ins().icmp(IntCC::SignedLessThan, lhs, rhs),
                    BinaryOp::Le => self
                        .builder
                        .ins()
                        .icmp(IntCC::SignedLessThanOrEqual, lhs, rhs),
                    BinaryOp::Gt => self.builder.ins().icmp(IntCC::SignedGreaterThan, lhs, rhs),
                    BinaryOp::Ge => {
                        self.builder
                            .ins()
                            .icmp(IntCC::SignedGreaterThanOrEqual, lhs, rhs)
                    }
                    BinaryOp::Eq => self.builder.ins().icmp(IntCC::Equal, lhs, rhs),
                    BinaryOp::Ne => self.builder.ins().icmp(IntCC::NotEqual, lhs, rhs),
                    _ => return Err(color_eyre::eyre::eyre!("Unsupported binary op: {:?}", op)),
                };

                Ok(Some(result))
            }

            _ => {
                // TODO: Implement other node types
                Ok(None)
            }
        }
    }

    fn get_value(&self, value_id: ValueId) -> color_eyre::Result<Value> {
        self.value_map
            .get(&value_id)
            .copied()
            .ok_or_else(|| color_eyre::eyre::eyre!("Value not found in map"))
    }
}
