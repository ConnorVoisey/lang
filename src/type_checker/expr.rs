use crate::{
    ast::ast_expr::{AstExpr, Atom, ExprKind, Op},
    interner::IdentId,
    lexer::Span,
    symbols::{SymbolId, SymbolKind},
    type_checker::{TypeChecker, error::TypeCheckingError},
    types::{TypeId, TypeKind},
};
use rustc_hash::FxHashMap;
use std::iter::once;

impl<'a> TypeChecker<'a> {
    pub fn check_expr(
        &mut self,
        expr: &mut AstExpr,
        return_type_id: Option<TypeId>,
        fn_symbol_id: SymbolId,
        inside_loop: bool,
    ) -> Option<TypeId> {
        match &mut expr.kind {
            ExprKind::Atom(atom) => {
                expr.type_id = self.check_atom(atom, &expr.span);
                expr.type_id
            }
            ExprKind::Op(op) => {
                match &mut **op {
                    Op::Add { left, right }
                    | Op::Minus { left, right }
                    | Op::Multiply { left, right }
                    | Op::Divide { left, right } => {
                        let lt = self
                            .check_expr(left, return_type_id, fn_symbol_id, inside_loop)
                            .unwrap();
                        let rt = self
                            .check_expr(right, return_type_id, fn_symbol_id, inside_loop)
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
                            .check_expr(inner, return_type_id, fn_symbol_id, inside_loop)
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
                            .check_expr(inner, return_type_id, fn_symbol_id, inside_loop)
                            .unwrap();
                        let ref_t = self.arena.make(TypeKind::Ref(inner_t));
                        expr.type_id = Some(ref_t);
                        expr.type_id
                    }
                    Op::FnCall { ident, args } => {
                        let _ = self.check_expr(ident, return_type_id, fn_symbol_id, inside_loop);
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
                            .map(|a| {
                                (
                                    self.check_expr(a, return_type_id, fn_symbol_id, inside_loop)
                                        .unwrap(),
                                    a,
                                )
                            })
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
                        // Ensure condition, and else if conditions is Bool
                        let bool_type = self.arena.bool_type;
                        for cond in once(&mut *condition)
                            .chain(else_ifs.iter_mut().map(|else_if| &mut else_if.0))
                        {
                            let cond_type = self
                                .check_expr(cond, return_type_id, fn_symbol_id, inside_loop)
                                .expect("if condition did not have a type");

                            if self.arena.unify(cond_type, bool_type).is_err() {
                                self.errors.push(TypeCheckingError::IfConditionNotBool {
                                    got_type_str: self.arena.id_to_string(cond_type),
                                    condition_span: cond.span.clone(),
                                });
                            }
                        }

                        // all blocks must return the same value
                        let if_block_return_id =
                            self.check_block(block, return_type_id, fn_symbol_id, inside_loop);
                        match if_block_return_id {
                            None => {
                                // If block returns unit/nothing, all else blocks must also return nothing
                                for (_, else_block) in else_ifs.iter_mut() {
                                    self.check_block(
                                        else_block,
                                        return_type_id,
                                        fn_symbol_id,
                                        inside_loop,
                                    );
                                    // Note: we don't error here for simplicity - empty blocks are compatible
                                }
                                if let Some(v) = unconditional_else {
                                    self.check_block(v, return_type_id, fn_symbol_id, inside_loop);
                                }
                            }
                            Some(t) => {
                                // If block returns a value, all else blocks must return compatible type
                                for (else_cond, else_block) in else_ifs.iter_mut() {
                                    if let Some(else_t) = self.check_block(
                                        else_block,
                                        return_type_id,
                                        fn_symbol_id,
                                        inside_loop,
                                    ) && self.arena.unify(t, else_t).is_err()
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
                                    && let Some(else_t) = self.check_block(
                                        v,
                                        return_type_id,
                                        fn_symbol_id,
                                        inside_loop,
                                    )
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
                    Op::Equivalent { left, right } | Op::NotEquivalent { left, right } => {
                        let left_type_id = self
                            .check_expr(left, return_type_id, fn_symbol_id, inside_loop)
                            .expect("left hand side of comparison expression did not have a type");
                        let right_type_id = self
                            .check_expr(right, return_type_id, fn_symbol_id, inside_loop)
                            .expect("right hand side of comparison expression did not have a type");

                        if self.arena.unify(left_type_id, right_type_id).is_err() {
                            self.errors.push(TypeCheckingError::ComparisonTypeMismatch {
                                left_type_str: self.arena.id_to_string(left_type_id),
                                left_span: left.span.clone(),
                                right_type_str: self.arena.id_to_string(right_type_id),
                                right_span: right.span.clone(),
                            });
                        }
                        Some(self.arena.bool_type)
                    }
                    Op::BinInverse(cond) => {
                        let left_type_id = self
                            .check_expr(cond, return_type_id, fn_symbol_id, inside_loop)
                            .expect("condition of `!` expression did not have a type");

                        if self
                            .arena
                            .unify(left_type_id, self.arena.bool_type)
                            .is_err()
                        {
                            // TODO: this probably needs to be a separate case, or the right hand
                            // side needs to be made optional
                            self.errors.push(TypeCheckingError::ComparisonTypeMismatch {
                                left_type_str: self.arena.id_to_string(left_type_id),
                                left_span: cond.span.clone(),
                                right_type_str: self.arena.id_to_string(self.arena.bool_type),
                                right_span: cond.span.clone(),
                            });
                        }
                        Some(self.arena.bool_type)
                    }
                    Op::LessThan { left, right }
                    | Op::LessThanEq { left, right }
                    | Op::GreaterThan { left, right }
                    | Op::GreaterThanEq { left, right } => {
                        let expected_type = self.arena.int_type;
                        let left_type_id = self
                            .check_expr(left, return_type_id, fn_symbol_id, inside_loop)
                            .expect("left hand side of comparison expression did not have a type");
                        let right_type_id = self
                            .check_expr(right, return_type_id, fn_symbol_id, inside_loop)
                            .expect("right hand side of comparison expression did not have a type");

                        if self.arena.unify(left_type_id, expected_type).is_err()
                            || self.arena.unify(right_type_id, expected_type).is_err()
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
                    Op::Dot { left, right } => {
                        let struct_type_id = self
                            .check_expr(left, return_type_id, fn_symbol_id, inside_loop)
                            .unwrap();
                        let expected_fields = match self.arena.kind(struct_type_id) {
                            TypeKind::Struct(struct_id) => self.arena.get_struct_fields(*struct_id),
                            _ => {
                                self.errors.push(TypeCheckingError::Mismatch {
                                    type_a_str: "struct".to_string(),
                                    type_a_span: left.span.clone(),
                                    type_b_str: self.arena.id_to_string(struct_type_id),
                                    type_b_span: left.span.clone(),
                                });
                                return None;
                            }
                        };
                        let type_id = match right.kind {
                            ExprKind::Atom(Atom::Ident((ident_id, _))) => {
                                let found_field = expected_fields.iter().find(|f| f.0 == ident_id);
                                found_field.map(|f| f.1)
                            }
                            _ => {
                                self.errors.push(TypeCheckingError::DotAccessExpectedIdent {
                                    expr_span: right.span.clone(),
                                });
                                return None;
                            }
                        };
                        expr.type_id = type_id;
                        type_id
                    }
                    Op::DoubleColon { left, right } => {
                        // currently `::` is only for enum variants
                        let type_id = self
                            .check_expr(left, return_type_id, fn_symbol_id, inside_loop)
                            .unwrap();
                        let expected_fields = match self.arena.kind(type_id) {
                            TypeKind::Enum(enum_id) => self.arena.get_enum_variants(*enum_id),
                            _ => {
                                self.errors.push(TypeCheckingError::Mismatch {
                                    type_a_str: "enum".to_string(),
                                    type_a_span: left.span.clone(),
                                    type_b_str: self.arena.id_to_string(type_id),
                                    type_b_span: left.span.clone(),
                                });
                                return None;
                            }
                        };
                        let type_id = match right.kind {
                            ExprKind::Atom(Atom::Ident((ident_id, _))) => {
                                let found_field = expected_fields.iter().find(|f| f.0 == ident_id);
                                found_field.map(|f| f.1)
                            }
                            _ => {
                                self.errors
                                    .push(TypeCheckingError::DoubleColonExpectedIdent {
                                        expr_span: right.span.clone(),
                                    });
                                return None;
                            }
                        };
                        expr.type_id = type_id;
                        type_id
                    }
                    Op::Block(ast_block) => {
                        let type_id =
                            self.check_block(ast_block, return_type_id, fn_symbol_id, inside_loop);
                        expr.type_id = type_id;
                        type_id
                    }

                    Op::ArrayAccess { left, right } => {
                        // left must be an array or array indexable thing (string),
                        // For now only allow arrays, string array access is ambiguous, is bytes or
                        // char array
                        let left_ty_id =
                            self.check_expr(left, return_type_id, fn_symbol_id, inside_loop)?;
                        let left_kind = self.arena.kind(left_ty_id);
                        let inner_type = match left_kind {
                            TypeKind::Array {
                                size: _,
                                inner_type,
                            } => Some(*inner_type),
                            _ => {
                                self.errors.push(TypeCheckingError::IndexNonArray {
                                    got_type_str: self.arena.id_to_string(left_ty_id),
                                    lhs_span: left.span.clone(),
                                });
                                return None;
                            }
                        };

                        // right must be an integer
                        let right_ty_id =
                            self.check_expr(right, return_type_id, fn_symbol_id, inside_loop)?;
                        let right_kind = self.arena.kind(right_ty_id);
                        match right_kind {
                            TypeKind::IntLiteral(_)
                            | TypeKind::I32
                            | TypeKind::U8
                            | TypeKind::U32
                            | TypeKind::U64 => (),
                            _ => {
                                self.errors
                                    .push(TypeCheckingError::ArrayAccessIndexNotInteger {
                                        got_type_str: self.arena.id_to_string(right_ty_id),
                                        index_span: right.span.clone(),
                                    });
                                return None;
                            }
                        }

                        expr.type_id = inner_type;
                        inner_type
                    }
                    Op::ArrayInit { args } => {
                        // all elements within the array init must have the same type
                        let mut type_id = None;
                        for arg in args.iter_mut() {
                            let arg_type_id =
                                self.check_expr(arg, return_type_id, fn_symbol_id, inside_loop);
                            if let Some(new_type_id) = arg_type_id {
                                match type_id {
                                    Some(type_id) => {
                                        if self.arena.unify(new_type_id, type_id).is_err() {
                                            self.errors.push(TypeCheckingError::Mismatch {
                                                type_a_str: self.arena.id_to_string(new_type_id),
                                                type_a_span: arg.span.clone(),
                                                type_b_str: self.arena.id_to_string(type_id),
                                                type_b_span: arg.span.clone(),
                                            });
                                        }
                                    }
                                    None => type_id = arg_type_id,
                                }
                            }
                        }
                        if type_id.is_none() {
                            self.errors.push(TypeCheckingError::ArrayNoInnerType {
                                creation_span: expr.span.clone(),
                            });
                            Some(self.arena.become_type)
                        } else {
                            let size = args.len();
                            expr.type_id = Some(self.arena.make(TypeKind::Array {
                                size,
                                inner_type: type_id.unwrap(),
                            }));
                            expr.type_id
                        }
                    }
                    Op::BracketOpen { .. } => {
                        self.errors.push(TypeCheckingError::InternalError {
                            message: "Op::BracketOpen should not reach type checking".to_string(),
                            span: expr.span.clone(),
                        });
                        return None;
                    }
                    Op::StructCreate {
                        ident,
                        args,
                        symbol_id: _,
                    } => {
                        // Type check the struct identifier expression
                        let struct_type_id = self
                            .check_expr(ident, return_type_id, fn_symbol_id, inside_loop)
                            .unwrap();
                        let struct_type_id = self.arena.find(struct_type_id);

                        // Extract struct_id and field definitions
                        let expected_fields = match self.arena.kind(struct_type_id) {
                            TypeKind::Struct(struct_id) =>
                            // TODO: remove this clone
                            {
                                self.arena.get_struct_fields(*struct_id).clone()
                            }
                            _ => {
                                self.errors.push(TypeCheckingError::Mismatch {
                                    type_a_str: "struct".to_string(),
                                    type_a_span: ident.span.clone(),
                                    type_b_str: self.arena.id_to_string(struct_type_id),
                                    type_b_span: ident.span.clone(),
                                });
                                return None;
                            }
                        };

                        // Build FxHashMap of provided fields: IdentId -> (TypeId, Span)
                        let mut provided: FxHashMap<IdentId, (TypeId, usize)> =
                            FxHashMap::default();
                        for (i, (field_ident, field_expr)) in args.iter_mut().enumerate() {
                            let field_type = self
                                .check_expr(field_expr, return_type_id, fn_symbol_id, inside_loop)
                                .unwrap();
                            if provided.insert(*field_ident, (field_type, i)).is_some() {
                                // Duplicate field name
                                self.errors.push(TypeCheckingError::Mismatch {
                                    type_a_str: format!(
                                        "duplicate field '{}'",
                                        self.symbols.interner.read().resolve(*field_ident)
                                    ),
                                    type_a_span: field_expr.span.clone(),
                                    type_b_str: "unique field".to_string(),
                                    type_b_span: field_expr.span.clone(),
                                });
                            }
                        }

                        // Validate each expected field
                        for (expected_ident, expected_type) in expected_fields.iter() {
                            match provided.remove(expected_ident) {
                                Some((provided_type, arg_index)) => {
                                    if self.arena.unify(*expected_type, provided_type).is_err() {
                                        let field_name = self
                                            .symbols
                                            .interner
                                            .read()
                                            .resolve(*expected_ident)
                                            .to_string();
                                        self.errors.push(TypeCheckingError::Mismatch {
                                            type_a_str: format!(
                                                "field '{}' has type {}",
                                                field_name,
                                                self.arena.id_to_string(provided_type)
                                            ),
                                            type_a_span: args[arg_index].1.span.clone(),
                                            type_b_str: format!(
                                                "expected type {}",
                                                self.arena.id_to_string(*expected_type)
                                            ),
                                            type_b_span: args[arg_index].1.span.clone(),
                                        });
                                    }
                                }
                                None => {
                                    let field_name = self
                                        .symbols
                                        .interner
                                        .read()
                                        .resolve(*expected_ident)
                                        .to_string();
                                    self.errors.push(TypeCheckingError::Mismatch {
                                        type_a_str: format!("missing field '{}'", field_name),
                                        type_a_span: expr.span.clone(),
                                        type_b_str: format!("field '{}' is required", field_name),
                                        type_b_span: ident.span.clone(),
                                    });
                                }
                            }
                        }

                        // Check for extra fields
                        if !provided.is_empty() {
                            for (extra_ident, (_, arg_index)) in provided.iter() {
                                let field_name = self
                                    .symbols
                                    .interner
                                    .read()
                                    .resolve(*extra_ident)
                                    .to_string();
                                self.errors.push(TypeCheckingError::Mismatch {
                                    type_a_str: format!("unexpected field '{}'", field_name),
                                    type_a_span: args[*arg_index].1.span.clone(),
                                    type_b_str: "no such field in struct".to_string(),
                                    type_b_span: ident.span.clone(),
                                });
                            }
                        }

                        expr.type_id = Some(struct_type_id);
                        Some(struct_type_id)
                    }
                }
            }
        }
    }

    fn check_atom(&mut self, atom: &Atom, span: &Span) -> Option<TypeId> {
        match atom {
            Atom::Int(val) => Some(self.arena.make(TypeKind::IntLiteral(*val))),
            Atom::Bool(_) => Some(self.arena.bool_type),
            Atom::Str(_) => Some(self.arena.str_type),
            Atom::CStr(_) => Some(self.arena.cstr_type),
            Atom::Ident((_, symbol_id)) => {
                let symbol_id = match symbol_id {
                    Some(id) => *id,
                    None => {
                        self.errors.push(TypeCheckingError::InternalError {
                            message: "symbol was not resolved during symbol registration"
                                .to_string(),
                            span: span.clone(),
                        });
                        return None;
                    }
                };
                let sym = self.symbols.resolve(symbol_id);
                match &sym.kind {
                    SymbolKind::Fn(data) => data.fn_type_id,
                    SymbolKind::Var(data) => data.type_id,
                    SymbolKind::Struct(data) => {
                        Some(self.arena.intern_struct_symbol(data.struct_id))
                    }
                    SymbolKind::Enum(data) => Some(self.arena.intern_enum_symbol(data.enum_id)),
                    SymbolKind::FnArg(data) => data.type_id,
                }
            }
        }
    }
}
