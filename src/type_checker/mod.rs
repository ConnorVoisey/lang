use crate::{
    ast::{
        Ast,
        ast_block::{AstBlock, AstStatement, StatementKind},
        ast_expr::{AstExpr, Atom, ExprKind, Op},
        ast_fn::AstFunc,
    },
    symbols::{SymbolId, SymbolKind, SymbolTable},
    type_checker::error::TypeCheckingError,
    types::{TypeArena, TypeId, TypeKind},
};

pub mod error;

#[derive(Debug)]
pub struct TypeChecker<'a> {
    pub arena: &'a mut TypeArena,
    pub errors: Vec<TypeCheckingError>,
    pub symbols: &'a mut SymbolTable,
}

impl<'a> TypeChecker<'a> {
    pub fn new(arena: &'a mut TypeArena, symbols: &'a mut SymbolTable) -> Self {
        Self {
            arena,
            errors: vec![],
            symbols,
        }
    }

    pub fn check_ast(&mut self, ast: &mut Ast) {
        for f in &mut ast.extern_fns {
            self.check_func(f);
        }
        for f in &mut ast.fns {
            self.check_func(f);
        }
        // later: check structs, globals, etc.
    }

    fn check_func(&mut self, f: &mut AstFunc) {
        let return_type_id = self.arena.var_type_to_typeid(&f.return_type);

        // allocate TypeIds for args
        let mut param_type_ids = vec![];
        let mut param_symbols = vec![];
        for arg in &mut f.args {
            let arg_symb = self.symbols.resolve_mut(arg.symbol_id);
            param_symbols.push(arg.symbol_id);
            if let SymbolKind::FnArg(data) = &mut arg_symb.kind {
                data.type_id = Some(self.arena.var_type_to_typeid(&arg.var_type));
                param_type_ids.push(data.type_id.unwrap());
            } else {
                unreachable!()
            }
        }
        let fn_type = self.arena.alloc(TypeKind::Fn {
            params: param_type_ids,
            ret: return_type_id,
            param_symbols,
        });

        if let Some(body) = &mut f.body {
            self.check_block(body, Some(return_type_id), f.symbol_id);
        }
        let fn_symb = self.symbols.resolve_mut(f.symbol_id);
        match &mut fn_symb.kind {
            SymbolKind::Fn(data) => {
                data.fn_type_id = Some(fn_type);
                data.return_type_id = Some(return_type_id);
            }
            _ => unreachable!(),
        }
    }

    fn check_statement(
        &mut self,
        statement: &mut AstStatement,
        return_type_id: Option<TypeId>,
        fn_symbol_id: SymbolId,
    ) -> Option<TypeId> {
        match &mut statement.kind {
            StatementKind::Decleration {
                ident_token_at: _,
                ident_id: _,
                symbol_id,
                expr,
            } => {
                let new_type_id = self.check_expr(expr, return_type_id, fn_symbol_id);
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
            StatementKind::Assignment {
                ident_token_at: _,
                ident_id: _,
                symbol_id,
                expr,
            } => {
                let new_type_id = self.check_expr(expr, return_type_id, fn_symbol_id).unwrap();
                let sym = self.symbols.resolve(symbol_id.unwrap());
                match &sym.kind {
                    SymbolKind::Var(data) => {
                        if self
                            .arena
                            .unify(data.type_id.unwrap(), new_type_id)
                            .is_err()
                        {
                            self.errors.push(TypeCheckingError::AssignmentMismatch {
                                assigned_type_str: self.arena.id_to_string(new_type_id),
                                assigned_type_span: expr.span.clone(),
                                var_type_str: self.arena.id_to_string(data.type_id.unwrap()),
                                var_decl_span: sym.ident_span.clone(),
                            });
                        }
                    }
                    _ => unreachable!(
                        "Just checked that the statement was a var so the symbol for it should be a var as well"
                    ),
                }
                None
            }
            StatementKind::Expr(ast_expr) => {
                ast_expr.type_id = self.check_expr(ast_expr, return_type_id, fn_symbol_id);
                ast_expr.type_id
            }
            StatementKind::ExplicitReturn(expr) => {
                let explicit_return_type =
                    self.check_expr(expr, return_type_id, fn_symbol_id).unwrap();
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
                let block_return_id = self.check_expr(expr, return_type_id, fn_symbol_id).unwrap();
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
                    .check_expr(condition, return_type_id, fn_symbol_id)
                    .unwrap();
                if self.arena.unify(bool_type, condition_return).is_err() {
                    self.errors.push(TypeCheckingError::WhileConditionNotBool {
                        got_type_str: self.arena.id_to_string(condition_return),
                        condition_span: condition.span.clone(),
                    });
                }
                self.check_block(block, return_type_id, fn_symbol_id);
                None
            }
        }
    }
    fn check_block(
        &mut self,
        block: &mut AstBlock,
        return_type_id: Option<TypeId>,
        fn_symbol_id: SymbolId,
    ) -> Option<TypeId> {
        let mut block_return_id = None;
        for statement in block.statements.iter_mut() {
            if let Some(type_id) = self.check_statement(statement, return_type_id, fn_symbol_id) {
                block_return_id = Some(type_id);
            }
        }
        block.type_id = block_return_id;
        block_return_id
    }
    fn check_expr(
        &mut self,
        expr: &mut AstExpr,
        return_type_id: Option<TypeId>,
        fn_symbol_id: SymbolId,
    ) -> Option<TypeId> {
        match &mut expr.kind {
            ExprKind::Atom(atom) => {
                expr.type_id = Some(match atom {
                    Atom::Int(_) => self.arena.int_type,
                    Atom::Bool(_) => self.arena.bool_type,
                    Atom::Str(_) => self.arena.str_type,
                    Atom::CStr(_) => self.arena.cstr_type,
                    Atom::Ident((_, symbol_id)) => {
                        let sym = self.symbols.resolve(symbol_id.unwrap());
                        match &sym.kind {
                            SymbolKind::Fn(data) => data.fn_type_id.unwrap(),
                            SymbolKind::Var(data) => data.type_id.unwrap(),
                            SymbolKind::Struct(_) => todo!(),
                            SymbolKind::FnArg(data) => data.type_id.unwrap(),
                        }
                    }
                });
                expr.type_id
            }
            ExprKind::Op(op) => {
                match &mut **op {
                    Op::Add { left, right }
                    | Op::Minus { left, right }
                    | Op::Multiply { left, right }
                    | Op::Divide { left, right } => {
                        let lt = self.check_expr(left, return_type_id, fn_symbol_id).unwrap();
                        let rt = self
                            .check_expr(right, return_type_id, fn_symbol_id)
                            .unwrap();
                        let int_t = self.arena.int_type;
                        if self.arena.unify(lt, int_t).is_err() {
                            self.errors.push(TypeCheckingError::Mismatch {
                                type_a_str: self.arena.id_to_string(lt),
                                type_a_span: left.span.clone(),
                                type_b_str: self.arena.id_to_string(rt),
                                type_b_span: right.span.clone(),
                            });
                        }
                        if self.arena.unify(rt, int_t).is_err() {
                            self.errors.push(TypeCheckingError::Mismatch {
                                type_a_str: self.arena.id_to_string(lt),
                                type_a_span: left.span.clone(),
                                type_b_str: self.arena.id_to_string(rt),
                                type_b_span: right.span.clone(),
                            });
                        }
                        expr.type_id = Some(int_t);
                        expr.type_id
                    }
                    Op::Neg(inner) => {
                        let t = self
                            .check_expr(inner, return_type_id, fn_symbol_id)
                            .unwrap();
                        let int_t = self.arena.int_type;
                        if self.arena.unify(t, int_t).is_err() {
                            self.errors.push(TypeCheckingError::Mismatch {
                                type_a_str: self.arena.id_to_string(t),
                                type_a_span: inner.span.clone(),
                                type_b_str: self.arena.id_to_string(int_t),
                                type_b_span: inner.span.clone(),
                            });
                        }
                        expr.type_id = Some(int_t);
                        expr.type_id
                    }
                    Op::Ref(inner) => {
                        let inner_t = self
                            .check_expr(inner, return_type_id, fn_symbol_id)
                            .unwrap();
                        let ref_t = self.arena.alloc(TypeKind::Ref(inner_t));
                        expr.type_id = Some(ref_t);
                        expr.type_id
                    }
                    Op::FnCall { ident, args } => {
                        let _ = self.check_expr(ident, return_type_id, fn_symbol_id);
                        let (params_t, param_symbols, ret_t) = match self
                            .arena
                            .kind(ident.type_id.unwrap())
                        {
                            TypeKind::Fn {
                                params,
                                ret,
                                param_symbols,
                            } => (params.clone(), param_symbols.clone(), *ret),
                            _ => {
                                self.errors.push(TypeCheckingError::CallNonFunction {
                                    got_type_str: self.arena.id_to_string(ident.type_id.unwrap()),
                                    call_span: ident.span.clone(),
                                });
                                return None;
                            }
                        };
                        let arg_types: Vec<_> = args
                            .iter_mut()
                            .map(|a| (self.check_expr(a, return_type_id, fn_symbol_id).unwrap(), a))
                            .collect();
                        if params_t.len() != arg_types.len() {
                            // Get function name and span for better error message
                            let fn_sym = if let ExprKind::Atom(Atom::Ident((_, Some(sym_id)))) =
                                &ident.kind
                            {
                                Some(self.symbols.resolve(*sym_id))
                            } else {
                                None
                            };

                            let (fn_def_str, fn_def_span) = if let Some(sym) = fn_sym {
                                (
                                    self.symbols
                                        .interner
                                        .read()
                                        .resolve(sym.ident_id)
                                        .to_string(),
                                    match &sym.kind {
                                        SymbolKind::Fn(data) => data.full_signature_span.clone(),
                                        _ => sym.ident_span.clone(),
                                    },
                                )
                            } else {
                                ("unknown function".to_string(), ident.span.clone())
                            };

                            self.errors.push(TypeCheckingError::MissingFnArgCall {
                                expected_arg_count: params_t.len(),
                                got_arg_count: arg_types.len(),
                                calling_span: expr.span.clone(),
                                fn_def_str,
                                fn_def_span,
                            });
                            return None;
                        }
                        for (i, param_t) in params_t.iter().enumerate() {
                            if let Some((arg_t, expr)) = arg_types.get(i)
                                && self.arena.unify(*param_t, *arg_t).is_err()
                            {
                                let param_symbol = self.symbols.resolve(param_symbols[i]);
                                self.errors.push(TypeCheckingError::FnInvalidArg {
                                    call_type_str: self.arena.id_to_string(*arg_t),
                                    call_type_span: expr.span.clone(),
                                    fn_arg_def_str: self.arena.id_to_string(*param_t),
                                    fn_arg_def_span: param_symbol.ident_span.clone(),
                                });
                            }
                        }
                        // Expect fn_t to be a function type
                        expr.type_id = Some(ret_t);
                        expr.type_id
                    }
                    Op::IfCond {
                        condition,
                        block,
                        else_ifs,
                        unconditional_else,
                    } => {
                        let cond_type = self
                            .check_expr(condition, return_type_id, fn_symbol_id)
                            .expect("if condition did not have a type");

                        // Ensure condition is Bool
                        let bool_type = self.arena.bool_type;
                        if self.arena.unify(cond_type, bool_type).is_err() {
                            self.errors.push(TypeCheckingError::IfConditionNotBool {
                                got_type_str: self.arena.id_to_string(cond_type),
                                condition_span: condition.span.clone(),
                            });
                        }

                        // all blocks must return the same value
                        let if_block_return_id =
                            self.check_block(block, return_type_id, fn_symbol_id);
                        match if_block_return_id {
                            None => {
                                // If block returns unit/nothing, all else blocks must also return nothing
                                for (_, else_block) in else_ifs.iter_mut() {
                                    self.check_block(else_block, return_type_id, fn_symbol_id);
                                    // Note: we don't error here for simplicity - empty blocks are compatible
                                }
                                if let Some(v) = unconditional_else {
                                    self.check_block(v, return_type_id, fn_symbol_id);
                                }
                            }
                            Some(t) => {
                                // If block returns a value, all else blocks must return compatible type
                                for (else_cond, else_block) in else_ifs.iter_mut() {
                                    if let Some(else_t) =
                                        self.check_block(else_block, return_type_id, fn_symbol_id)
                                        && self.arena.unify(t, else_t).is_err()
                                    {
                                        // Use the whole if expression span for the error
                                        self.errors.push(TypeCheckingError::IfElseBranchMismatch {
                                            if_type_str: self.arena.id_to_string(t),
                                            if_span: condition.span.clone(),
                                            else_type_str: self.arena.id_to_string(else_t),
                                            else_span: else_cond.span.clone(),
                                        });
                                    }
                                }
                                if let Some(v) = unconditional_else
                                    && let Some(else_t) =
                                        self.check_block(v, return_type_id, fn_symbol_id)
                                    && self.arena.unify(t, else_t).is_err()
                                {
                                    self.errors.push(TypeCheckingError::IfElseBranchMismatch {
                                        if_type_str: self.arena.id_to_string(t),
                                        if_span: condition.span.clone(),
                                        else_type_str: self.arena.id_to_string(else_t),
                                        else_span: expr.span.clone(), // Use full expression span as fallback
                                    });
                                }
                            }
                        }
                        expr.type_id = if_block_return_id;
                        if_block_return_id
                    }
                    Op::LessThan { left, right }
                    | Op::LessThanEq { left, right }
                    | Op::GreaterThan { left, right }
                    | Op::GreaterThanEq { left, right } => {
                        let int_type = self.arena.int_type;
                        let left_type_id = self
                            .check_expr(left, return_type_id, fn_symbol_id)
                            .expect("left hand side of comparison expression did not have a type");
                        let right_type_id = self
                            .check_expr(right, return_type_id, fn_symbol_id)
                            .expect("right hand side of comparison expression did not have a type");

                        if self.arena.unify(left_type_id, int_type).is_err()
                            || self.arena.unify(right_type_id, int_type).is_err()
                        {
                            self.errors.push(TypeCheckingError::ComparisonTypeMismatch {
                                left_type_str: self.arena.id_to_string(left_type_id),
                                left_span: left.span.clone(),
                                right_type_str: self.arena.id_to_string(right_type_id),
                                right_span: right.span.clone(),
                            });
                        }
                        Some(self.arena.bool_type)
                    }
                    Op::Dot { left: _, right: _ } => todo!(),
                    Op::Block(ast_block) => {
                        let type_id = self.check_block(ast_block, return_type_id, fn_symbol_id);
                        expr.type_id = type_id;
                        type_id
                    }

                    Op::Equivalent { left: _, right: _ } => todo!(),
                    Op::SquareOpen { left: _, args: _ } => todo!(),
                    Op::BracketOpen { left: _, right: _ } => todo!(),
                }
            }
        }
    }
}
