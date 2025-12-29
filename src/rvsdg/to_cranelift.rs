//! Lower RVSDG to Cranelift IR
//!
//! This module converts the high-level RVSDG representation into Cranelift IR.
//! The conversion is designed for minimal overhead and fast compilation.

use crate::{
    rvsdg::{
        BinaryOp, ConstValue, ExternFunction, Function, FunctionId, Module, Node, NodeId, NodeKind,
        RegionId, UnaryOp, ValueId,
    },
    struct_layout::StructLayoutInfo,
    symbols::SymbolTable,
    types::{StructId, TypeArena, TypeId, TypeKind},
};
use cranelift::prelude::*;
use cranelift_codegen::{
    Context,
    ir::{BlockArg, Function as ClFunction, UserFuncName},
};
use cranelift_module::{FuncId as ClFuncId, Linkage, Module as ClModuleTrait};
use cranelift_object::ObjectModule;
use isa::CallConv;
use rustc_hash::FxHashMap;

/// Convert an RVSDG type to a Cranelift type
fn type_to_cl(types: &TypeArena, type_id: TypeId) -> Option<types::Type> {
    match types.kind(type_id) {
        TypeKind::I32 => Some(types::I64),
        TypeKind::U64 => Some(types::I64),
        TypeKind::Bool => Some(types::I8),
        TypeKind::CStr => Some(types::I64),
        TypeKind::Array { .. } => todo!("This should probably be a pointer"),
        TypeKind::Enum(_) => todo!(),
        TypeKind::Ref(_) => Some(types::I64),
        TypeKind::Str => unreachable!(
            "Str should be lowered into the respected fields that are accessed before going to cranelift."
        ),
        TypeKind::Struct(_) => unreachable!(
            "struct should be lowered into the respected fields that are accessed before going to cranelift."
        ),
        TypeKind::Void => unreachable!(),
        TypeKind::Fn { .. } => unreachable!(),
        TypeKind::Unknown => unreachable!(),
        TypeKind::Become => unreachable!(),
        TypeKind::Var => unreachable!(),
        TypeKind::State => None,
    }
}

pub struct RvsdgToCranelift<'a> {
    module: &'a Module<'a>,
    symbols: &'a SymbolTable,
    struct_layout_info: &'a StructLayoutInfo<'a>,

    // Map RVSDG function IDs to Cranelift function IDs
    func_map: FxHashMap<FunctionId, ClFuncId>,

    // Current function being compiled
    current_function: Option<FunctionId>,
}

pub struct FunctionCompiler<'a, 'b> {
    rvsdg_func: &'a Function,
    module: &'a Module<'a>,
    func_map: &'a FxHashMap<FunctionId, ClFuncId>,
    cl_module: &'b mut ObjectModule,
    struct_layout_info: &'a StructLayoutInfo<'a>,

    // Map RVSDG values to Cranelift values
    value_map: FxHashMap<ValueId, Value>,

    // Map structural nodes to their Cranelift blocks
    block_map: FxHashMap<NodeId, Vec<Block>>,

    // Cranelift builder
    builder: FunctionBuilder<'a>,

    // Counter for unique string global names
    string_counter: usize,
}

impl<'a> RvsdgToCranelift<'a> {
    pub fn new(
        module: &'a self::Module<'a>,
        symbols: &'a SymbolTable,
        struct_layout_info: &'a StructLayoutInfo<'a>,
    ) -> Self {
        Self {
            module,
            symbols,
            struct_layout_info,
            func_map: FxHashMap::default(),
            current_function: None,
        }
    }

    #[tracing::instrument(skip(self, cl_module, call_conv))]
    pub fn compile(
        mut self,
        cl_module: &mut ObjectModule,
        call_conv: CallConv,
    ) -> color_eyre::Result<()> {
        // First pass: declare all functions
        let mut sigs = Vec::with_capacity(self.module.functions.len());
        for func in &self.module.functions {
            let (cl_func_id, sig) = self.declare_function(func, cl_module, call_conv)?;
            self.func_map.insert(func.id, cl_func_id);
            sigs.push(sig);
        }

        // Declare extern functions
        for extern_fn in &self.module.extern_functions {
            let cl_func_id = self.declare_extern_function(extern_fn, cl_module)?;
            self.func_map.insert(extern_fn.id, cl_func_id);
        }

        // Second pass: compile function bodies
        for (i, func) in self.module.functions.iter().enumerate() {
            self.compile_function(func, sigs[i].clone(), cl_module, call_conv)?;
        }

        Ok(())
    }

    fn declare_function(
        &self,
        func: &Function,
        cl_module: &mut ObjectModule,
        call_conv: CallConv,
    ) -> color_eyre::Result<(ClFuncId, Signature)> {
        let mut sig = Signature::new(call_conv);

        for param in &func.params {
            let cl_type = self.type_to_cl(param.ty);
            sig.params.push(AbiParam::new(
                cl_type.expect("to cl type should be a valid value got none"),
            ));
        }

        let ret_cl_type = self.type_to_cl(func.return_type);
        sig.returns.push(AbiParam::new(
            ret_cl_type.expect("to cl type should be a valid value got none"),
        ));

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

        match cl_module.declare_function(&name, linkage, &sig) {
            Ok(f) => Ok((f, sig)),
            Err(e) => Err(color_eyre::eyre::eyre!("Failed to declare function: {}", e)),
        }
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
            sig.params.push(AbiParam::new(
                cl_type.expect("to cl type should be a valid value, got none"),
            ));
        }

        // Add return type
        let ret_cl_type = self.type_to_cl(extern_fn.return_type);
        sig.returns.push(AbiParam::new(
            ret_cl_type.expect("to cl type should be a valid value, got none"),
        ));

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
        sig: Signature,
        cl_module: &mut ObjectModule,
        call_conv: CallConv,
    ) -> color_eyre::Result<()> {
        let cl_func_id = self.func_map[&func.id];

        let mut cl_func = ClFunction::with_name_signature(UserFuncName::user(0, 0), sig);
        let mut func_ctx = FunctionBuilderContext::new();
        let builder = FunctionBuilder::new(&mut cl_func, &mut func_ctx);

        let compiler = FunctionCompiler::new(
            func,
            self.module,
            &self.func_map,
            cl_module,
            self.struct_layout_info,
            builder,
        );
        compiler.compile()?;

        let mut context = Context::for_function(cl_func);

        cl_module
            .define_function(cl_func_id, &mut context)
            .map_err(|e| {
                color_eyre::eyre::eyre!(
                    "Failed to define function: {:?}\n\nGenerated Cranelift IR:\n{}",
                    e,
                    context.func
                )
            })
    }

    fn type_to_cl(&self, type_id: TypeId) -> Option<types::Type> {
        type_to_cl(self.module.types, type_id)
    }
}

impl<'a, 'b> FunctionCompiler<'a, 'b> {
    fn new(
        rvsdg_func: &'a Function,
        module: &'a self::Module<'a>,
        func_map: &'a FxHashMap<FunctionId, ClFuncId>,
        cl_module: &'b mut ObjectModule,
        struct_layout_info: &'a StructLayoutInfo<'a>,
        builder: FunctionBuilder<'a>,
    ) -> Self {
        Self {
            rvsdg_func,
            module,
            func_map,
            cl_module,
            struct_layout_info,
            value_map: FxHashMap::default(),
            block_map: FxHashMap::default(),
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

        // Get the lambda region and its parameter nodes
        let root_node = self.rvsdg_func.node(self.rvsdg_func.root);
        let lambda_region_id = match &root_node.kind {
            NodeKind::Lambda { region } => *region,
            _ => {
                return Err(color_eyre::eyre::eyre!(
                    "Root node is not a Lambda, found: {:?}",
                    root_node.kind
                ));
            }
        };

        // Get lambda region's parameter nodes
        let lambda_params = self.rvsdg_func.region(lambda_region_id).params.clone();

        // Map function parameters to their region param nodes
        for (i, &param_node_id) in lambda_params.iter().enumerate() {
            let cl_param = self.builder.block_params(entry_block)[i];
            let param_value = ValueId {
                node: param_node_id,
                output_index: 0,
            };
            self.value_map.insert(param_value, cl_param);
        }

        // Compile the lambda region
        let ret_val = self.compile_lambda(lambda_region_id)?;
        self.builder.ins().return_(&ret_val);

        self.builder.seal_all_blocks();
        self.builder.finalize();

        Ok(())
    }

    fn compile_lambda(&mut self, region_id: RegionId) -> color_eyre::Result<Vec<Value>> {
        self.compile_region_impl(region_id)
    }
    fn compile_region(
        &mut self,
        region_id: RegionId,
        inputs: &[Value],
    ) -> color_eyre::Result<Vec<Value>> {
        let region = self.rvsdg_func.region(region_id);

        // Map region parameters to the input values
        // Skip void type parameters (state tokens) - they don't have Cranelift representation
        let mut input_idx = 0;
        for &param_node_id in &region.params {
            let param_node = self.rvsdg_func.node(param_node_id);
            let param_ty = param_node.output_types[0];

            if !matches!(self.module.types.kind(param_ty), TypeKind::Void) {
                // Non-void parameter - map it to the corresponding input
                let value_id = ValueId {
                    node: param_node_id,
                    output_index: 0,
                };
                self.value_map.insert(value_id, inputs[input_idx]);
                input_idx += 1;
            }
            // Void parameters are not mapped - they have no Cranelift representation
        }

        self.compile_region_impl(region_id)
    }

    fn compile_region_impl(&mut self, region_id: RegionId) -> color_eyre::Result<Vec<Value>> {
        let region = self.rvsdg_func.region(region_id);

        // Region params are already mapped (they correspond to function params)
        // Or if they're separate, map them here

        // Compile all nodes in topological order
        for &node_id in &region.nodes {
            let node = self.rvsdg_func.node(node_id);
            self.compile_node(node)?;
        }

        let mut results = Vec::new();
        for &result_node_id in &region.results {
            let node = self.rvsdg_func.node(result_node_id);
            if let NodeKind::RegionResult { inputs } = node.kind {
                // Skip void-typed results (state tokens)
                let input_node = self.rvsdg_func.node(inputs.value.node);
                let input_ty = input_node.output_types[inputs.value.output_index as usize];

                if !matches!(self.module.types.kind(input_ty), TypeKind::Void) {
                    results.push(self.get_value(inputs.value)?);
                }
            }
        }

        Ok(results)
    }

    fn compile_node(&mut self, node: &Node) -> color_eyre::Result<Option<Value>> {
        match &node.kind {
            NodeKind::Const { value } => {
                let cl_val = match value {
                    ConstValue::I32(i) => self.builder.ins().iconst(types::I64, *i),
                    ConstValue::U32(u) => self.builder.ins().iconst(types::I64, *u as i64),
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
                self.value_map.insert(
                    ValueId {
                        node: node.id,
                        output_index: 0,
                    },
                    cl_val,
                );
                Ok(Some(cl_val))
            }
            NodeKind::Binary { op, inputs } => {
                let lhs = self.get_value(inputs.left)?;
                let rhs = self.get_value(inputs.right)?;

                let cl_val = match op {
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
                self.value_map.insert(
                    ValueId {
                        node: node.id,
                        output_index: 0,
                    },
                    cl_val,
                );

                Ok(Some(cl_val))
            }
            NodeKind::Unary { op, inputs } => {
                let operand = self.get_value(inputs.operand)?;

                let cl_val = match op {
                    UnaryOp::Neg => self.builder.ins().ineg(operand),
                    UnaryOp::Not => {
                        // For booleans: XOR with 1 to flip the bit
                        let one = self.builder.ins().iconst(types::I8, 1);
                        self.builder.ins().bxor(operand, one)
                    }
                };
                self.value_map.insert(
                    ValueId {
                        node: node.id,
                        output_index: 0,
                    },
                    cl_val,
                );

                Ok(Some(cl_val))
            }
            NodeKind::Call { function, inputs } => {
                // Get the Cranelift function ID
                let cl_func_id = *self.func_map.get(function).ok_or_else(|| {
                    color_eyre::eyre::eyre!("Function {:?} not found in func_map", function)
                })?;

                // Declare the function in the current function
                let func_ref = self
                    .cl_module
                    .declare_func_in_func(cl_func_id, self.builder.func);

                // First input is state token (skip it), rest are actual arguments
                let args: Vec<Value> = inputs
                    .args
                    .iter()
                    .map(|&value_id| self.get_value(value_id))
                    .collect::<color_eyre::Result<Vec<_>>>()?;

                // Make the call
                let inst = self.builder.ins().call(func_ref, &args);

                // Get return values from the call
                let results = self.builder.inst_results(inst);

                // Store the return value (output index 1, since 0 is the state token)
                // Note: We don't store the state token in value_map since it has no Cranelift representation
                if !results.is_empty() {
                    let return_value = results[0];
                    self.value_map.insert(
                        ValueId {
                            node: node.id,
                            output_index: 1,
                        },
                        return_value,
                    );
                }

                Ok(None)
            }
            NodeKind::Gamma { regions, inputs } => {
                // Gamma: conditional branch (if/else)
                // Inputs: [condition, ...captured_values]
                // Outputs: merged results from all branches

                // Get the condition value
                let condition = self.get_value(inputs.condition)?;

                // Create blocks for each region (typically 2: true and false)
                let mut region_blocks = Vec::new();
                for _ in regions {
                    let block = self.builder.create_block();
                    region_blocks.push(block);
                }

                // Create merge block for phi nodes
                let merge_block = self.builder.create_block();

                // Add block parameters to merge block (skip state tokens/void types)
                // State tokens don't have runtime representation, so we filter them out
                let non_void_output_indices: Vec<_> = node
                    .output_types
                    .iter()
                    .enumerate()
                    .filter(|(_, ty)| !matches!(self.module.types.kind(**ty), TypeKind::Void))
                    .collect();

                for (_, output_ty) in &non_void_output_indices {
                    let cl_type = type_to_cl(self.module.types, **output_ty);
                    self.builder.append_block_param(
                        merge_block,
                        cl_type.expect("to cl type should be a vaild value"),
                    );
                }

                // Branch on condition (true -> regions[0], false -> regions[1])
                // For now, assume binary if/else (2 regions)
                if regions.len() == 2 {
                    self.builder.ins().brif(
                        condition,
                        region_blocks[0],
                        &[],
                        region_blocks[1],
                        &[],
                    );
                } else {
                    return Err(color_eyre::eyre::eyre!(
                        "Gamma with {} regions not yet supported (expected 2)",
                        regions.len()
                    ));
                }

                // Compile each region in its block
                for (i, &region_id) in regions.iter().enumerate() {
                    self.builder.switch_to_block(region_blocks[i]);

                    // Get captured values (skip first input which is condition)
                    // Also skip void types (state tokens) since they don't have Cranelift representation
                    let captured_inputs: Vec<Value> = inputs
                        .captured
                        .iter()
                        .filter_map(|&vid| {
                            // Check if this is a void type
                            let input_node = self.rvsdg_func.node(vid.node);
                            let input_ty = input_node.output_types[vid.output_index as usize];
                            if matches!(self.module.types.kind(input_ty), TypeKind::Void) {
                                None // Skip void types
                            } else {
                                Some(self.get_value(vid))
                            }
                        })
                        .collect::<color_eyre::Result<Vec<_>>>()?;

                    // Compile the region with captured values
                    let region_results = self.compile_region(region_id, &captured_inputs)?;

                    // region_results already contains only non-void values
                    // (void results were filtered out in compile_region_impl)
                    let filtered_results: Vec<Value> = region_results;

                    // Jump to merge block with filtered results (convert Values to BlockArgs)
                    let block_args: Vec<_> = filtered_results
                        .iter()
                        .map(|&v| BlockArg::Value(v))
                        .collect();
                    self.builder.ins().jump(merge_block, &block_args);
                }

                // Seal all blocks we created
                for block in &region_blocks {
                    self.builder.seal_block(*block);
                }
                self.builder.seal_block(merge_block);

                // Continue in merge block
                self.builder.switch_to_block(merge_block);

                // Get the merged values from block parameters (phi nodes)
                let merge_params = self.builder.block_params(merge_block);

                // Store each non-void output in value_map
                for (param_idx, &(orig_idx, _)) in non_void_output_indices.iter().enumerate() {
                    self.value_map.insert(
                        ValueId {
                            node: node.id,
                            output_index: orig_idx as u32,
                        },
                        merge_params[param_idx],
                    );
                }

                Ok(None)
            }
            NodeKind::Theta { region, inputs } => {
                // Theta: loop construct
                // Inputs: [...initial_values]
                // Region outputs: [condition, ...updated_values]
                // Loop continues while condition is true

                // Create blocks: header (with phi nodes), body, exit
                let header_block = self.builder.create_block();
                let body_block = self.builder.create_block();
                let exit_block = self.builder.create_block();

                // Add block parameters to header for loop-carried values (skip void types)
                let non_void_output_indices: Vec<_> = node
                    .output_types
                    .iter()
                    .enumerate()
                    .filter(|(_, ty)| !matches!(self.module.types.kind(**ty), TypeKind::Void))
                    .collect();

                for (_, output_ty) in &non_void_output_indices {
                    let cl_type = type_to_cl(self.module.types, **output_ty);
                    self.builder.append_block_param(
                        header_block,
                        cl_type.expect("to cl type should be a valid value, got none"),
                    );
                }

                // Get initial values (only non-void ones, matching non_void_output_indices)
                // State tokens (void type) don't have Cranelift representations, so skip them
                let initial_values: Vec<Value> = inputs
                    .all_values()
                    .filter_map(|value_id| {
                        let value_node = self.rvsdg_func.node(value_id.node);
                        let value_ty = value_node.output_types[value_id.output_index as usize];
                        if matches!(self.module.types.kind(value_ty), TypeKind::Void) {
                            None // Skip void types (state tokens)
                        } else {
                            Some(self.get_value(value_id))
                        }
                    })
                    .collect::<color_eyre::Result<Vec<_>>>()?;

                // Jump to header with initial values
                let initial_args: Vec<_> =
                    initial_values.iter().map(|&v| BlockArg::Value(v)).collect();
                self.builder.ins().jump(header_block, &initial_args);

                // Seal the current block (before header)
                // Note: We can't seal header yet because body will jump back to it

                // Switch to header block
                self.builder.switch_to_block(header_block);

                // Jump to body to start loop
                self.builder.ins().jump(body_block, &[]);

                // Switch to body block
                self.builder.switch_to_block(body_block);

                // Get header parameters (loop-carried values)
                let header_params: Vec<Value> = self.builder.block_params(header_block).to_vec();

                // Compile the loop region with loop-carried values as inputs
                let region_results = self.compile_region(*region, &header_params)?;

                // First result is the continuation condition, rest are updated values
                if region_results.is_empty() {
                    return Err(color_eyre::eyre::eyre!(
                        "Theta region must produce at least a condition"
                    ));
                }

                let condition = region_results[0];

                // Updated values are all region results except the first (condition)
                // They're already filtered to exclude void types in compile_region
                let updated_values: Vec<Value> = region_results[1..].to_vec();

                // Branch: if condition is true, jump back to header, else exit
                let updated_args: Vec<_> =
                    updated_values.iter().map(|&v| BlockArg::Value(v)).collect();
                self.builder
                    .ins()
                    .brif(condition, header_block, &updated_args, exit_block, &[]);

                // Now we can seal header (all predecessors known: initial jump + body)
                self.builder.seal_block(header_block);
                self.builder.seal_block(body_block);

                // Continue in exit block
                self.builder.switch_to_block(exit_block);
                self.builder.seal_block(exit_block);

                // Store the final values (from header phi nodes) in value_map (skip void)
                for (param_idx, &(orig_idx, _)) in non_void_output_indices.iter().enumerate() {
                    self.value_map.insert(
                        ValueId {
                            node: node.id,
                            output_index: orig_idx as u32,
                        },
                        header_params[param_idx],
                    );
                }

                Ok(None)
            }
            NodeKind::Parameter { .. }
            | NodeKind::RegionParam { .. }
            | NodeKind::StateToken
            | NodeKind::RegionResult { .. } => {
                // These are either already mapped or don't need Cranelift values
                Ok(None)
            }
            NodeKind::Lambda { region: _ } => {
                // Lambda nodes are structural and handled separately
                Ok(None)
            }
            NodeKind::Alloc { ty, inputs: _ } => {
                // Allocate memory (stack allocation for now)
                // Inputs: [state]
                // Outputs: [new_state, pointer]

                let (size, alignment) = self.get_size_and_align(*ty)?;

                let stack_slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    size as u32,
                    alignment as u8,
                ));

                let ptr = self.builder.ins().stack_addr(types::I64, stack_slot, 0);

                self.value_map.insert(
                    ValueId {
                        node: node.id,
                        output_index: 1,
                    },
                    ptr,
                );

                Ok(Some(ptr))
            }
            NodeKind::Load { ty, inputs } => {
                let ptr = self.get_value(inputs.address)?;

                let cl_type = type_to_cl(self.module.types, *ty).ok_or_else(|| {
                    color_eyre::eyre::eyre!(
                        "Cannot convert field type to Cranelift type: {:?}",
                        self.module.types.kind(*ty)
                    )
                })?;

                let value = self.builder.ins().load(cl_type, MemFlags::new(), ptr, 0);
                self.value_map.insert(
                    ValueId {
                        node: node.id,
                        output_index: 1,
                    },
                    value,
                );

                Ok(Some(value))
            }
            NodeKind::Store { ty, inputs } => {
                let ptr = self.get_value(inputs.address)?;

                let value_to_store = self.get_value(inputs.value)?;

                self.builder
                    .ins()
                    .store(MemFlags::new(), value_to_store, ptr, 0);

                // No value to store in value_map - only output is state token
                // State tokens have no Cranelift representation
                Ok(None)
            }
        }
    }

    fn get_value(&self, value_id: ValueId) -> color_eyre::Result<Value> {
        self.value_map.get(&value_id).copied().ok_or_else(|| {
            let node = self.rvsdg_func.node(value_id.node);
            color_eyre::eyre::eyre!(
                "Value not found in map: {:?} (node kind: {:?})",
                value_id,
                node.kind
            )
        })
    }

    /// Get the StructId from a pointer value by dereferencing its type
    fn get_struct_id_from_ptr(&self, ptr_value_id: ValueId) -> color_eyre::Result<StructId> {
        let ptr_node = self.rvsdg_func.node(ptr_value_id.node);
        let ptr_type = ptr_node.output_types[ptr_value_id.output_index as usize];

        // Handle both Ref(Struct) and Struct directly
        // (Alloc currently returns Struct instead of Ref(Struct))
        let struct_type = match self.module.types.kind(ptr_type) {
            TypeKind::Ref(inner_type) => *inner_type,
            TypeKind::Struct(_) => ptr_type, // Already a struct type (from Alloc)
            _ => {
                return Err(color_eyre::eyre::eyre!(
                    "Expected pointer or struct type for struct field access, got {:?}",
                    self.module.types.kind(ptr_type)
                ));
            }
        };

        // Extract the StructId from the type
        match self.module.types.kind(struct_type) {
            TypeKind::Struct(struct_id) => Ok(*struct_id),
            _ => Err(color_eyre::eyre::eyre!(
                "Expected struct type, got {:?}",
                self.module.types.kind(struct_type)
            )),
        }
    }

    /// Get the size and alignment for a type
    fn get_size_and_align(&self, type_id: TypeId) -> color_eyre::Result<(usize, usize)> {
        match self.module.types.kind(type_id) {
            TypeKind::Struct(struct_id) => {
                let layout = &self.struct_layout_info.layouts[struct_id.0]
                    .as_ref()
                    .unwrap();
                Ok((layout.size, layout.alignment))
            }
            TypeKind::Array {
                size,
                inner_type: _,
            } => {
                // TODO: not sure what the alignment of an array will be, but it probably is not the
                // size
                Ok((*size, *size))
            }
            _ => Err(color_eyre::eyre::eyre!(
                "Alloc is currently only supported for struct types, got: {:?}",
                self.module.types.kind(type_id)
            )),
        }
    }
}
