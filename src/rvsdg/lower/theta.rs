use crate::{
    ast::{ast_block::AstBlock, ast_expr::AstExpr},
    lexer::Span,
    rvsdg::{NodeId, ValueId, builder::FunctionBuilder, lower::AstLowering},
    symbols::SymbolId,
};

impl<'a> AstLowering<'a> {
    pub fn lower_while_loop(
        &mut self,
        builder: &mut FunctionBuilder,
        condition: &AstExpr,
        body: &AstBlock,
        span: Span,
    ) -> Option<ValueId> {
        let initial_state = self.current_state.expect("State not initialized");

        // Track all variables that need to be loop-carried
        // For now, we need to find all variables used in the condition or body
        // and add them to the loop. This is a simplified version - a full implementation
        // would analyze the AST to find exactly which variables are modified.

        // Collect all current variables from the symbol map as loop-carried values
        let loop_carried_vars: Vec<(SymbolId, ValueId)> = builder.current_scope_symbols();

        // Build initial values: state + all loop vars
        let mut initial_values = vec![initial_state];
        let mut var_value_ids: Vec<ValueId> = loop_carried_vars.iter().map(|(_, v)| *v).collect();
        initial_values.append(&mut var_value_ids);

        // Get output types (state type + loop var types)
        let state_ty = self.types.void_type;
        let mut output_types = vec![state_ty];
        for &(_sym, value_id) in &loop_carried_vars {
            let value_node = &builder.get_func().nodes[value_id.node.0];
            let var_ty = value_node.output_types[value_id.output_index as usize];
            output_types.push(var_ty);
        }

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

        // Map loop-carried variables to their region parameters
        // Parameters are: [state, var1, var2, ...]
        for (i, (symbol_id, _)) in loop_carried_vars.iter().enumerate() {
            let param_value = ValueId {
                node: theta_param_nodes[i + 1], // +1 to skip state parameter
                output_index: 0,
            };
            builder.define_symbol(*symbol_id, param_value);
        }

        // Lower the loop body
        let _body_result = self.lower_block(builder, body);

        // NOW evaluate the condition inside the theta region with the updated state
        // This ensures the condition is re-evaluated each loop iteration
        let loop_cond = self
            .lower_expr(builder, condition)
            .expect("Failed to evaluate loop condition");

        // Create region results: [condition, final_state, updated_vars...]
        let final_state = self.current_state.expect("State should still be set");

        // First result is the continuation condition (freshly evaluated!)
        builder.region_result(loop_cond, span.clone());

        // Second result is the updated state
        builder.region_result(final_state, span.clone());

        // Remaining results are the updated loop-carried variable values
        for (symbol_id, _) in &loop_carried_vars {
            let updated_value = builder
                .lookup_symbol(*symbol_id)
                .expect("Loop variable should still be in symbol map");
            builder.region_result(updated_value, span.clone());
        }

        builder.end_region();

        // Restore state and variables after the loop
        // Theta outputs: [final_state, updated_var1, updated_var2, ...]

        // First output is the final state
        self.current_state = Some(ValueId {
            node: theta_node,
            output_index: 0,
        });

        // Remaining outputs are the final values of loop-carried variables
        for (i, (symbol_id, _)) in loop_carried_vars.iter().enumerate() {
            let final_value = ValueId {
                node: theta_node,
                output_index: (i + 1) as u32, // +1 to skip state output
            };
            builder.define_symbol(*symbol_id, final_value);
        }

        // While loops don't produce a value in our language (they're statements)
        // But we return the theta node reference for consistency
        Some(ValueId {
            node: theta_node,
            output_index: 0,
        })
    }
}
