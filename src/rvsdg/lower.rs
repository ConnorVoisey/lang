//! Lower AST to RVSDG

use super::builder::FunctionBuilder;
use super::*;
use crate::{
    ast::{
        Ast,
        ast_block::{AstBlock, AstStatement, StatementKind},
        ast_expr::{AstExpr, Atom, ExprKind, Op},
        ast_fn::AstFunc,
    },
    interner::{IdentId, SharedInterner},
    lexer::{Span, TokenKind},
    rvsdg::optimize::dead_code_elimination,
    symbols::{SymbolKind, SymbolTable},
    types::{TypeArena, TypeKind},
};

pub struct AstLowering<'a> {
    ast: &'a Ast,
    types: &'a TypeArena,
    symbols: &'a SymbolTable,
    interner: SharedInterner,

    // Function ID counter
    next_func_id: usize,

    // Map from AST symbol IDs to RVSDG function IDs
    func_map: FxHashMap<SymbolId, FunctionId>,

    // Current state token for effect threading
    current_state: Option<ValueId>,

    // Track variables modified in current scope (for gamma/theta nodes)
    modified_vars: Vec<SymbolId>,
}

impl<'a> AstLowering<'a> {
    pub fn new(
        ast: &'a Ast,
        types: &'a TypeArena,
        symbols: &'a SymbolTable,
        interner: SharedInterner,
    ) -> Self {
        Self {
            ast,
            types,
            symbols,
            interner,
            next_func_id: 0,
            func_map: FxHashMap::default(),
            current_state: None,
            modified_vars: Vec::new(),
        }
    }

    pub fn lower_module(mut self) -> Module<'a> {
        let mut module = Module::new(self.types, self.interner.clone());
        // First register all functions

        // Register internal functions
        for func in &self.ast.fns {
            let func_id = FunctionId(self.next_func_id);
            self.next_func_id += 1;
            self.func_map.insert(func.symbol_id, func_id);
        }

        // Register extern functions
        for extern_fn in &self.ast.extern_fns {
            let func_id = FunctionId(self.next_func_id);
            self.next_func_id += 1;
            self.func_map.insert(extern_fn.symbol_id, func_id);

            module
                .extern_functions
                .push(self.lower_extern_function(extern_fn, func_id));
        }

        // Second pass: lower function bodies
        for func in &self.ast.fns {
            let func_id = self.func_map[&func.symbol_id];
            let mut rvsdg_func = self.lower_function(func, func_id);

            dead_code_elimination(&mut rvsdg_func);

            module.functions.push(rvsdg_func);
        }

        module
    }

    fn lower_extern_function(&self, ast_fn: &AstFunc, func_id: FunctionId) -> ExternFunction {
        let symbol = self.symbols.resolve(ast_fn.symbol_id);
        let (param_types, return_type) = match &symbol.kind {
            SymbolKind::Fn(data) => {
                let fn_type_id = data.fn_type_id.expect("Extern function missing type");
                match self.types.kind(fn_type_id) {
                    TypeKind::Fn { params, ret, .. } => (params.clone(), *ret),
                    _ => panic!("Extern function has non-function type"),
                }
            }
            _ => panic!("Extern function symbol is not a function"),
        };

        // Create a dummy span - AST functions don't track their full span
        let span = Span {
            start: ast_fn.fn_token_at,
            end: ast_fn.fn_token_at + 2,
        };

        ExternFunction {
            id: func_id,
            name: ast_fn.symbol_id,
            param_types,
            return_type,
            span,
        }
    }

    fn lower_function(&mut self, ast_fn: &AstFunc, func_id: FunctionId) -> Function {
        let symbol = self.symbols.resolve(ast_fn.symbol_id);
        let return_type = match &symbol.kind {
            SymbolKind::Fn(data) => {
                let fn_type_id = data.fn_type_id.expect("Function missing type");
                match self.types.kind(fn_type_id) {
                    TypeKind::Fn { ret, .. } => *ret,
                    _ => panic!("Function has non-function type"),
                }
            }
            _ => panic!("Function symbol is not a function"),
        };

        // Build parameters
        let params: Vec<Parameter> = ast_fn
            .args
            .iter()
            .map(|arg| {
                let arg_symbol = self.symbols.resolve(arg.symbol_id);
                let ty = match &arg_symbol.kind {
                    SymbolKind::FnArg(data) => data.type_id.expect("Parameter missing type"),
                    _ => panic!("Parameter symbol is not a function argument"),
                };

                // TODO: review if spans are even needed for RVSDG, currently there isn't enough
                // info to generate them accurately
                let span = Span { start: 0, end: 0 };

                Parameter {
                    name: arg.symbol_id,
                    ty,
                    span,
                }
            })
            .collect();

        // Create a dummy span for the function
        let fn_span = Span {
            start: ast_fn.fn_token_at,
            end: ast_fn.fn_token_at + 2,
        };

        let mut builder = FunctionBuilder::new(
            func_id,
            ast_fn.symbol_id,
            params.clone(),
            return_type,
            fn_span.clone(),
        );

        let lambda_region = builder.create_lambda(return_type, fn_span.clone());

        // Get parameter nodes that were created in create_lambda()
        // We need to do this before start_region() to avoid borrow issues
        let param_nodes: Vec<NodeId> = builder.get_region(lambda_region).params.clone();

        builder.start_region(lambda_region);

        // Map region parameters to symbols
        for (i, param) in params.iter().enumerate() {
            let param_value = ValueId {
                node: param_nodes[i],
                output_index: 0,
            };
            builder.define_symbol(param.name, param_value);
        }

        // Create initial state token for effect threading
        let initial_state = builder.state_token(self.types.void_type, fn_span.clone());
        self.current_state = Some(initial_state);

        // Lower function body
        let body = ast_fn.body.as_ref().expect("Function body is None");
        let result = self.lower_block(&mut builder, body);

        // Create region result with return value
        if let Some(return_value) = result {
            let result_span = Span {
                start: ast_fn.fn_token_at,
                end: ast_fn.fn_token_at + 1,
            };
            builder.region_result(return_value, result_span);
        }

        builder.end_region();

        let mut func = builder.finish();

        // Mark the main function as exported so it's visible to the linker
        let function_name = {
            let interner = self.interner.read();
            let symbol = self.symbols.resolve(func.name);
            interner.resolve(symbol.ident_id).to_string()
        };
        if function_name == "main" {
            func.is_exported = true;
        }

        func
    }

    fn lower_block(&mut self, builder: &mut FunctionBuilder, block: &AstBlock) -> Option<ValueId> {
        let mut last_value = None;

        for statement in &block.statements {
            last_value = self.lower_statement(builder, statement);
        }

        last_value
    }

    fn lower_statement(
        &mut self,
        builder: &mut FunctionBuilder,
        statement: &AstStatement,
    ) -> Option<ValueId> {
        match &statement.kind {
            StatementKind::Expr(expr) => self.lower_expr(builder, expr),

            StatementKind::Decleration {
                symbol_id, expr, ..
            } => {
                if let Some(value) = self.lower_expr(builder, expr) {
                    builder.define_symbol(*symbol_id, value);
                    Some(value)
                } else {
                    None
                }
            }

            StatementKind::Assignment {
                symbol_id, expr, ..
            } => {
                if let Some(value) = self.lower_expr(builder, expr) {
                    if let Some(sym_id) = symbol_id {
                        builder.define_symbol(*sym_id, value);
                        // Track that this variable was modified
                        if !self.modified_vars.contains(sym_id) {
                            self.modified_vars.push(*sym_id);
                        }
                    }
                    Some(value)
                } else {
                    None
                }
            }

            StatementKind::ExplicitReturn(expr) => {
                // TODO: set the has_early_return bool, not sure how this will function
                self.lower_expr(builder, expr)
            }

            StatementKind::BlockReturn { expr, .. } => self.lower_expr(builder, expr),

            StatementKind::WhileLoop { condition, block } => {
                let span = Span {
                    start: statement.start_token_at,
                    end: statement.start_token_at + 5,
                };
                self.lower_while_loop(builder, condition, block, span)
            }

            StatementKind::Break { .. } => {
                // TODO: set the break bool, not sure how this will function
                None
            }
        }
    }

    fn lower_expr(&mut self, builder: &mut FunctionBuilder, expr: &AstExpr) -> Option<ValueId> {
        // Use Void type if expression doesn't have a type (e.g., if-statement used as statement)
        let ty = expr.type_id.unwrap_or({
            // Get void type from type arena
            self.types.void_type
        });

        match &expr.kind {
            ExprKind::Atom(atom) => self.lower_atom(builder, atom, ty, expr.span.clone()),

            ExprKind::Op(op) => self.lower_op(builder, op, ty, expr.span.clone()),
        }
    }

    fn lower_atom(
        &mut self,
        builder: &mut FunctionBuilder,
        atom: &Atom,
        ty: TypeId,
        span: Span,
    ) -> Option<ValueId> {
        match atom {
            Atom::Int(val) => Some(builder.const_i64(*val as i64, ty, span)),

            Atom::Bool(val) => Some(builder.const_bool(*val, ty, span)),

            Atom::Ident((_, Some(symbol_id))) => builder.lookup_symbol(*symbol_id),

            Atom::Ident((_, None)) => {
                // Unresolved symbol - should have been caught in type checking
                None
            }

            Atom::Str(token_idx) | Atom::CStr(token_idx) => {
                // Extract string from token
                // TODO: strings should probably be stored in a vec of strings with a string id so
                // that passing them around is much cheaper
                let string_data = match &self.ast.tokens[*token_idx].kind {
                    TokenKind::Str(s) | TokenKind::CStr(s) => s,
                    _ => unreachable!("String atom with non-string token"),
                };

                // Convert to bytes and add null terminator (for C interop)
                let mut bytes = string_data.as_bytes().to_vec();
                bytes.push(0); // Null terminator for both Str and CStr

                // Create string constant (will be deduplicated via hash-consing)
                Some(builder.const_string(bytes, ty, span))
            }
        }
    }

    fn lower_op(
        &mut self,
        builder: &mut FunctionBuilder,
        op: &Op,
        ty: TypeId,
        span: Span,
    ) -> Option<ValueId> {
        match op {
            Op::Add { left, right } => {
                let lhs = self.lower_expr(builder, left)?;
                let rhs = self.lower_expr(builder, right)?;
                Some(builder.binary(BinaryOp::Add, lhs, rhs, ty, span))
            }

            Op::Minus { left, right } => {
                let lhs = self.lower_expr(builder, left)?;
                let rhs = self.lower_expr(builder, right)?;
                Some(builder.binary(BinaryOp::Sub, lhs, rhs, ty, span))
            }

            Op::Multiply { left, right } => {
                let lhs = self.lower_expr(builder, left)?;
                let rhs = self.lower_expr(builder, right)?;
                Some(builder.binary(BinaryOp::Mul, lhs, rhs, ty, span))
            }

            Op::Divide { left, right } => {
                let lhs = self.lower_expr(builder, left)?;
                let rhs = self.lower_expr(builder, right)?;
                Some(builder.binary(BinaryOp::Div, lhs, rhs, ty, span))
            }

            Op::LessThan { left, right } => {
                let lhs = self.lower_expr(builder, left)?;
                let rhs = self.lower_expr(builder, right)?;
                Some(builder.binary(BinaryOp::Lt, lhs, rhs, ty, span))
            }

            Op::LessThanEq { left, right } => {
                let lhs = self.lower_expr(builder, left)?;
                let rhs = self.lower_expr(builder, right)?;
                Some(builder.binary(BinaryOp::Le, lhs, rhs, ty, span))
            }

            Op::GreaterThan { left, right } => {
                let lhs = self.lower_expr(builder, left)?;
                let rhs = self.lower_expr(builder, right)?;
                Some(builder.binary(BinaryOp::Gt, lhs, rhs, ty, span))
            }

            Op::GreaterThanEq { left, right } => {
                let lhs = self.lower_expr(builder, left)?;
                let rhs = self.lower_expr(builder, right)?;
                Some(builder.binary(BinaryOp::Ge, lhs, rhs, ty, span))
            }

            Op::Equivalent { left, right } => {
                let lhs = self.lower_expr(builder, left)?;
                let rhs = self.lower_expr(builder, right)?;
                Some(builder.binary(BinaryOp::Eq, lhs, rhs, ty, span))
            }

            Op::Neg(operand) => {
                let val = self.lower_expr(builder, operand)?;
                Some(builder.unary(UnaryOp::Neg, val, ty, span))
            }

            Op::FnCall { ident, args } => self.lower_call(builder, ident, args, ty, span),

            Op::IfCond {
                condition,
                block,
                else_ifs: _,
                unconditional_else,
            } => self.lower_if(
                builder,
                condition,
                block,
                unconditional_else.as_ref(),
                ty,
                span,
            ),

            Op::Block(block) => self.lower_block(builder, block),

            Op::Dot { left, right } => {
                // Struct field access
                self.lower_struct_field_access(builder, left, right, ty, span)
            }

            Op::StructCreate {
                ident,
                symbol_id,
                args,
            } => {
                // Struct instantiation
                self.lower_struct_create(builder, ident, symbol_id, args, ty, span)
            }

            Op::Ref(operand) => {
                // For now, just lower the operand (pointer is implicit in RVSDG)
                // TODO: Proper reference handling
                self.lower_expr(builder, operand)
            }

            Op::ArrayAccess { .. } | Op::ArrayInit { .. } | Op::BracketOpen { .. } => {
                // TODO: Handle these operations
                None
            }
        }
    }

    fn lower_call(
        &mut self,
        builder: &mut FunctionBuilder,
        ident: &AstExpr,
        args: &[AstExpr],
        return_ty: TypeId,
        span: Span,
    ) -> Option<ValueId> {
        let func_symbol_id = match &ident.kind {
            ExprKind::Atom(Atom::Ident((_, Some(symbol_id)))) => *symbol_id,
            _ => return None,
        };

        let func_id = *self.func_map.get(&func_symbol_id)?;

        // Lower arguments
        let arg_values: Vec<ValueId> = args
            .iter()
            .filter_map(|arg| self.lower_expr(builder, arg))
            .collect();

        if arg_values.len() != args.len() {
            return None; // Some argument failed to lower
        }

        // Thread state through the function call
        let state = self.current_state.expect("State not initialized");
        let (new_state, result) = builder.call(
            state,
            func_id,
            arg_values,
            self.types.void_type,
            return_ty,
            span,
        );

        self.current_state = Some(new_state);

        Some(result)
    }

    fn lower_if(
        &mut self,
        builder: &mut FunctionBuilder,
        condition: &AstExpr,
        then_block: &AstBlock,
        else_block: Option<&AstBlock>,
        result_ty: TypeId,
        span: Span,
    ) -> Option<ValueId> {
        let cond = self.lower_expr(builder, condition)?;

        // Check for constant condition and optimize
        if let Some(const_val) = self.get_const_bool(builder, cond) {
            if const_val {
                // Constant true: just lower then-block
                return self.lower_block(builder, then_block);
            } else {
                // Constant false: just lower else-block (if present)
                if let Some(else_blk) = else_block {
                    return self.lower_block(builder, else_blk);
                } else {
                    // No else block, if-statement produces no value
                    return None;
                }
            }
        }

        // Non-constant condition: create gamma node
        // Scan AST to find which variables are assigned in either branch
        let mut all_modified = Vec::new();
        self.scan_block_for_assignments(then_block, &mut all_modified);
        if let Some(else_blk) = else_block {
            self.scan_block_for_assignments(else_blk, &mut all_modified);
        }

        // Save incoming state - it needs to be captured by gamma
        let incoming_state = self.current_state.expect("State not initialized");

        // Get current values of variables that will be modified
        // Track which symbols were actually captured (some might not be in scope yet)
        let mut captured_symbols: Vec<SymbolId> = Vec::new();
        let mut captured_values: Vec<ValueId> = vec![incoming_state]; // State is always first

        for sym in &all_modified {
            if let Some(val) = builder.lookup_symbol(*sym) {
                captured_symbols.push(*sym);
                captured_values.push(val);
            }
        }

        // Determine output types: result_ty + state + types of modified variables
        let mut output_types = vec![result_ty, self.types.void_type]; // result + state
        for val in &captured_values[1..] {
            // Skip state (already added)
            // Get the output type of this value
            if let Some(ty) = builder.get_value_type(*val) {
                output_types.push(ty);
            }
        }

        // Create gamma node with captured values (including state)
        let (gamma_node, regions) =
            builder.create_gamma(cond, captured_values, output_types, span.clone());

        // Save current modified vars state
        let saved_modified = self.modified_vars.clone();

        // Lower then branch
        self.modified_vars.clear();
        builder.start_region(regions[0]);

        // Map region parameters to captured values
        // Index 0 is state, indices 1+ are modified variables
        let region_params = builder.get_region(regions[0]).params.clone();

        // Map state parameter
        let then_state_param = ValueId {
            node: region_params[0],
            output_index: 0,
        };
        self.current_state = Some(then_state_param);

        // Map captured variables to their region parameters
        for (i, sym) in captured_symbols.iter().enumerate() {
            let param_value = ValueId {
                node: region_params[i + 1], // +1 to skip state parameter
                output_index: 0,
            };
            builder.define_symbol(*sym, param_value);
        }

        let then_value = self.lower_block(builder, then_block);

        // Return block result - must match result_ty
        // If result_ty is Void, ignore the block's value and create a default
        let result_val = if matches!(self.types.kind(result_ty), crate::types::TypeKind::Void) {
            // For void result type, always create default (ignore block value)
            builder.const_i64(0, result_ty, span.clone())
        } else {
            then_value.unwrap_or_else(|| {
                // No result value - create default value of the correct type
                match self.types.kind(result_ty) {
                    crate::types::TypeKind::Int | crate::types::TypeKind::Uint => {
                        builder.const_i64(0, result_ty, span.clone())
                    }
                    crate::types::TypeKind::Bool => {
                        builder.const_bool(false, result_ty, span.clone())
                    }
                    _ => builder.const_i64(0, result_ty, span.clone()),
                }
            })
        };
        builder.region_result(result_val, span.clone());

        // Return final state
        let final_state = self.current_state.expect("State should be set");
        builder.region_result(final_state, span.clone());

        // Return modified variable values (in same order as captured)
        for sym in &captured_symbols {
            if let Some(val) = builder.lookup_symbol(*sym) {
                builder.region_result(val, span.clone());
            }
        }
        builder.end_region();

        // Lower else branch
        self.modified_vars.clear();
        builder.start_region(regions[1]);

        // Map region parameters to captured values
        // Index 0 is state, indices 1+ are modified variables
        let region_params = builder.get_region(regions[1]).params.clone();

        // Map state parameter
        let else_state_param = ValueId {
            node: region_params[0],
            output_index: 0,
        };
        self.current_state = Some(else_state_param);

        // Map captured variables to their region parameters
        for (i, sym) in captured_symbols.iter().enumerate() {
            let param_value = ValueId {
                node: region_params[i + 1], // +1 to skip state parameter
                output_index: 0,
            };
            builder.define_symbol(*sym, param_value);
        }

        let else_value = if let Some(else_blk) = else_block {
            self.lower_block(builder, else_blk)
        } else {
            None
        };

        // Return block result - must match result_ty (same as then branch)
        // If result_ty is Void, ignore the block's value and create a default
        let result_val = if matches!(self.types.kind(result_ty), crate::types::TypeKind::Void) {
            // For void result type, always create default (ignore block value)
            builder.const_i64(0, result_ty, span.clone())
        } else {
            else_value.unwrap_or_else(|| {
                // No result value - create default value of the correct type
                match self.types.kind(result_ty) {
                    crate::types::TypeKind::Int | crate::types::TypeKind::Uint => {
                        builder.const_i64(0, result_ty, span.clone())
                    }
                    crate::types::TypeKind::Bool => {
                        builder.const_bool(false, result_ty, span.clone())
                    }
                    _ => builder.const_i64(0, result_ty, span.clone()),
                }
            })
        };
        builder.region_result(result_val, span.clone());

        // Return final state
        let final_state = self.current_state.expect("State should be set");
        builder.region_result(final_state, span.clone());

        // Return modified variable values (in same order as captured)
        for sym in &captured_symbols {
            if let Some(val) = builder.lookup_symbol(*sym) {
                builder.region_result(val, span.clone());
            }
        }
        builder.end_region();

        // Restore modified vars state
        self.modified_vars = saved_modified;

        // Update outer scope with merged state from gamma (output index 1)
        self.current_state = Some(ValueId {
            node: gamma_node,
            output_index: 1,
        });

        // Update outer scope with gamma outputs for captured variables
        // Offset by +2 because output 0 is block result, output 1 is state
        for (i, sym) in captured_symbols.iter().enumerate() {
            let gamma_output = ValueId {
                node: gamma_node,
                output_index: (i + 2) as u32,
            };
            builder.define_symbol(*sym, gamma_output);
        }

        Some(ValueId {
            node: gamma_node,
            output_index: 0,
        })
    }

    /// Check if a value is a constant boolean and return its value
    fn get_const_bool(&self, builder: &FunctionBuilder, value: ValueId) -> Option<bool> {
        // Constants only have one output
        if value.output_index != 0 {
            return None;
        }

        let node = builder.get_node(value.node);
        match &node.kind {
            NodeKind::Const {
                value: ConstValue::Bool(b),
            } => Some(*b),
            _ => None,
        }
    }

    /// Scan a block to find all variable assignments (for gamma/theta node handling)
    fn scan_block_for_assignments(&self, block: &AstBlock, modified: &mut Vec<SymbolId>) {
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Assignment { symbol_id, .. } => {
                    if let Some(sym) = symbol_id
                        && !modified.contains(sym)
                    {
                        modified.push(*sym);
                    }
                }
                StatementKind::WhileLoop { block, .. } => {
                    self.scan_block_for_assignments(block, modified);
                }
                StatementKind::Expr(expr) | StatementKind::BlockReturn { expr, .. } => {
                    self.scan_expr_for_assignments(expr, modified);
                }
                _ => {}
            }
        }
    }

    /// Scan an expression to find assignments (for nested if-statements, etc.)
    fn scan_expr_for_assignments(&self, expr: &AstExpr, modified: &mut Vec<SymbolId>) {
        if let ExprKind::Op(op) = &expr.kind {
            match &**op {
                Op::IfCond {
                    block,
                    unconditional_else,
                    ..
                } => {
                    self.scan_block_for_assignments(block, modified);
                    if let Some(else_blk) = unconditional_else {
                        self.scan_block_for_assignments(else_blk, modified);
                    }
                }
                Op::Block(block) => {
                    self.scan_block_for_assignments(block, modified);
                }
                _ => {}
            }
        }
    }

    fn lower_while_loop(
        &mut self,
        builder: &mut FunctionBuilder,
        condition: &AstExpr,
        body: &AstBlock,
        span: Span,
    ) -> Option<ValueId> {
        // For while loops with theta nodes, the pattern is:
        // theta [initial_state, initial_vars...] {
        //   region params: [state, vars...]
        //   ... loop body ...
        //   cond = evaluate condition
        //   results: [cond, new_state, updated_vars...]
        // }

        // Start with just state as the loop-carried value
        // TODO: Track all variables modified in the loop body
        let initial_state = self.current_state.expect("State not initialized");
        let initial_values = vec![initial_state];

        // Get output types (state type + any other loop vars)
        let state_ty = self.types.void_type;
        let output_types = vec![state_ty];

        // Create theta node
        let (theta_node, theta_region) =
            builder.create_theta(initial_values, output_types, span.clone());

        // Get the region parameter nodes (created by create_theta)
        let theta_param_nodes: Vec<NodeId> = builder.get_region(theta_region).params.clone();

        // Save the current state before entering the loop
        let outer_state = self.current_state;

        // Start building in the theta region
        builder.start_region(theta_region);

        // Map the state parameter
        let loop_state = ValueId {
            node: theta_param_nodes[0],
            output_index: 0,
        };
        self.current_state = Some(loop_state);

        // Lower the loop body
        let _body_result = self.lower_block(builder, body);

        // Evaluate the condition
        let cond_value = self.lower_expr(builder, condition)?;

        // Create region results: [condition, final_state]
        let final_state = self.current_state.expect("State should still be set");

        // First result is the continuation condition
        builder.region_result(cond_value, span.clone());

        // Remaining results are the updated loop-carried values (state)
        builder.region_result(final_state, span.clone());

        builder.end_region();

        // Restore outer state - after loop, we have the final state from theta
        // The theta node's first output (index 0) is the final state value
        self.current_state = Some(ValueId {
            node: theta_node,
            output_index: 0,
        });

        // Restore outer scope's state context
        // Actually, we should use the state from after the loop
        // theta outputs: [final_state]
        // We already set current_state above

        // While loops don't produce a value in our language (they're statements)
        // But we return the theta node reference for consistency
        Some(ValueId {
            node: theta_node,
            output_index: 0,
        })
    }

    fn lower_struct_field_access(
        &mut self,
        builder: &mut FunctionBuilder,
        struct_expr: &AstExpr,
        field_expr: &AstExpr,
        result_ty: TypeId,
        span: Span,
    ) -> Option<ValueId> {
        // Lower the struct expression (should produce a pointer to the struct)
        let struct_val = self.lower_expr(builder, struct_expr)?;

        // Get the field name from the right expression (should be an Ident)
        let field_ident_id = match &field_expr.kind {
            ExprKind::Atom(Atom::Ident((_, Some(symbol_id)))) => {
                // Get the ident_id from the symbol
                let symbol = self.symbols.resolve(*symbol_id);
                symbol.ident_id
            }
            ExprKind::Atom(Atom::Ident((ident_id, None))) => *ident_id,
            _ => return None, // Field name must be an identifier
        };

        // Get the struct type from the left expression
        let struct_type_id = struct_expr.type_id?;
        // Note: find() is only needed during type checking for union-find
        // After type checking, types are already unified
        // let struct_type_id = self.types.find(struct_type_id);

        // Get the struct ID from the type
        let struct_id = match self.types.kind(struct_type_id) {
            crate::types::TypeKind::Struct(sid) => *sid,
            crate::types::TypeKind::Ref(inner_ty) => {
                // If it's a reference, dereference it
                match self.types.kind(*inner_ty) {
                    crate::types::TypeKind::Struct(sid) => *sid,
                    _ => return None,
                }
            }
            _ => return None, // Not a struct type
        };

        // Look up the struct definition in the AST
        let struct_def = self.ast.structs.iter().find(|s| s.struct_id == struct_id)?;

        // Find the field index by name
        let field_index = struct_def
            .fields
            .iter()
            .position(|(fid, _, _)| *fid == field_ident_id)?;

        // Use StructFieldLoad with state threading
        let state = self.current_state.expect("State not initialized");
        let field_id = FieldId(field_index);

        let (new_state, field_value) =
            builder.struct_field_load(state, struct_val, field_id, result_ty, span);

        // Update current state
        self.current_state = Some(new_state);

        Some(field_value)
    }

    fn lower_struct_create(
        &mut self,
        builder: &mut FunctionBuilder,
        ident_expr: &AstExpr,
        symbol_id: &Option<SymbolId>,
        field_values: &[(IdentId, AstExpr)],
        result_ty: TypeId,
        span: Span,
    ) -> Option<ValueId> {
        // Get the struct symbol
        let struct_symbol_id = symbol_id.or_else(|| {
            // Try to get symbol from ident expression
            match &ident_expr.kind {
                ExprKind::Atom(Atom::Ident((_, Some(sid)))) => Some(*sid),
                _ => None,
            }
        })?;

        // Get struct ID from symbol
        let struct_id = match &self.symbols.resolve(struct_symbol_id).kind {
            SymbolKind::Struct(data) => data.struct_id,
            _ => return None,
        };

        // Look up the struct definition
        let struct_def = self.ast.structs.iter().find(|s| s.struct_id == struct_id)?;

        // Allocate memory for the struct
        let state = self.current_state.expect("State not initialized");
        let (new_state, struct_ptr) = builder.alloc(state, result_ty, span.clone());
        self.current_state = Some(new_state);

        // Store each field value
        for (field_ident_id, field_expr) in field_values {
            let field_index = struct_def
                .fields
                .iter()
                .position(|(fid, _, _)| *fid == *field_ident_id)?;

            // Lower the field value expression
            let field_value = self.lower_expr(builder, field_expr)?;

            // Store the field
            let field_id = FieldId(field_index);
            let state = self.current_state.expect("State should still be set");
            let field_ty = struct_def.field_type_ids[field_index].unwrap_or(self.types.void_type);

            let new_state = builder.struct_field_store(
                state,
                struct_ptr,
                field_id,
                field_value,
                field_ty,
                span.clone(),
            );

            self.current_state = Some(new_state);
        }

        // Return the pointer to the struct
        Some(struct_ptr)
    }
}
