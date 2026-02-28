use crate::{
    ast::ast_block::{AstStatement, StatementKind},
    symbols::{SymbolId, SymbolKind},
    type_checker::{TypeChecker, error::TypeCheckingError},
    types::TypeId,
};

impl<'a> TypeChecker<'a> {
    pub fn check_statement(
        &mut self,
        statement: &mut AstStatement,
        return_type_id: Option<TypeId>,
        fn_symbol_id: SymbolId,
        inside_loop: bool,
    ) -> Option<TypeId> {
        match &mut statement.kind {
            StatementKind::Decleration {
                ident_token_at: _,
                ident_id: _,
                symbol_id,
                expr,
            } => {
                let new_type_id = self.check_expr(expr, return_type_id, fn_symbol_id, inside_loop);
                let sym = self.symbols.resolve_mut(*symbol_id);
                match &mut sym.kind {
                    SymbolKind::Var(data) => {
                        data.type_id = new_type_id;
                    }
                    _ => unreachable!(
                        "Just checked that the statement was a var so the symbol for it should be a var as well"
                    ),
                }
                None
            }
            StatementKind::Assignment { lhs, rhs } => {
                let lhs_type = self.check_lvalue(lhs, return_type_id, fn_symbol_id, inside_loop);
                let rhs_type = self.check_expr(rhs, return_type_id, fn_symbol_id, inside_loop);
                if let (Some(lhs_t), Some(rhs_t)) = (lhs_type, rhs_type) {
                    if self.arena.unify(lhs_t, rhs_t).is_err() {
                        self.errors.push(TypeCheckingError::AssignmentMismatch {
                            assigned_type_str: self.arena.id_to_string(rhs_t),
                            assigned_type_span: rhs.span.clone(),
                            var_type_str: self.arena.id_to_string(lhs_t),
                            var_decl_span: lhs.span.clone(),
                        });
                    }
                }
                None
            }
            StatementKind::Expr(ast_expr) => {
                ast_expr.type_id =
                    self.check_expr(ast_expr, return_type_id, fn_symbol_id, inside_loop);
                ast_expr.type_id
            }
            StatementKind::ExplicitReturn(expr) => {
                let explicit_return_type = self
                    .check_expr(expr, return_type_id, fn_symbol_id, inside_loop)
                    .unwrap();
                if self
                    .arena
                    .unify(explicit_return_type, return_type_id.unwrap())
                    .is_err()
                {
                    let fn_sym = self.symbols.resolve(fn_symbol_id);
                    let fn_return_span = match &fn_sym.kind {
                        SymbolKind::Fn(data) => data.return_type_span.clone(),
                        _ => unreachable!("fn_symbol_id should always point to a function symbol"),
                    };

                    self.errors.push(TypeCheckingError::FnInvalidReturnType {
                        got_type_str: self.arena.id_to_string(explicit_return_type),
                        call_type_span: expr.span.clone(),
                        expected_type_str: self.arena.id_to_string(return_type_id.unwrap()),
                        fn_return_span,
                    });
                    return None;
                }
                Some(explicit_return_type)
            }
            StatementKind::BlockReturn { expr, is_fn_return } => {
                let block_return_id =
                    match self.check_expr(expr, return_type_id, fn_symbol_id, inside_loop) {
                        Some(type_id) => type_id,
                        None => return None,
                    };
                if *is_fn_return
                    && self
                        .arena
                        .unify(block_return_id, return_type_id.unwrap())
                        .is_err()
                {
                    let fn_sym = self.symbols.resolve(fn_symbol_id);
                    let fn_return_span = match &fn_sym.kind {
                        SymbolKind::Fn(data) => data.return_type_span.clone(),
                        _ => unreachable!("fn_symbol_id should always point to a function symbol"),
                    };

                    self.errors.push(TypeCheckingError::FnInvalidReturnType {
                        got_type_str: self.arena.id_to_string(block_return_id),
                        call_type_span: expr.span.clone(),
                        expected_type_str: self.arena.id_to_string(return_type_id.unwrap()),
                        fn_return_span,
                    });
                    return None;
                }
                Some(block_return_id)
            }
            StatementKind::WhileLoop { condition, block } => {
                let bool_type = self.arena.bool_type;
                let condition_return = self
                    .check_expr(condition, return_type_id, fn_symbol_id, inside_loop)
                    .unwrap();
                if self.arena.unify(bool_type, condition_return).is_err() {
                    self.errors.push(TypeCheckingError::WhileConditionNotBool {
                        got_type_str: self.arena.id_to_string(condition_return),
                        condition_span: condition.span.clone(),
                    });
                }
                // Check the block with inside_loop = true
                self.check_block(block, return_type_id, fn_symbol_id, true);
                None
            }
            StatementKind::Break { span } => {
                if !inside_loop {
                    self.errors.push(TypeCheckingError::BreakOutsideLoop {
                        break_span: span.clone(),
                    });
                }
                None
            }
        }
    }
}
