use std::iter::once;

use crate::{
    ast::{
        Ast,
        ast_block::{AstBlock, AstStatement, Lvalue, LvalueKind, StatementKind},
        ast_expr::{AstExpr, Atom, ExprKind, Op},
        ast_fn::AstFunc,
        ast_struct::AstStruct,
    },
    interner::IdentId,
    symbols::{SymbolId, SymbolKind, SymbolTable},
    type_checker::error::TypeCheckingError,
    types::{TypeArena, TypeId, TypeKind},
};
use rustc_hash::FxHashMap;

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
        for s in &mut ast.structs {
            self.check_struct_name(s);
        }
        for s in &mut ast.structs {
            self.check_struct_fields(s);
        }
        for f in &mut ast.extern_fns {
            self.check_func(f);
        }
        for f in &mut ast.fns {
            self.check_func(f);
        }
        // later: check structs, globals, etc.
    }

    fn check_struct_name(&mut self, s: &mut AstStruct) {
        // Ensure the struct has a TypeId (may already be set from symbol registration)
        if s.type_id.is_none() {
            let type_id = self.arena.intern_struct_symbol(s.struct_id);
            s.type_id = Some(type_id);
        };
    }
    fn check_struct_fields(&mut self, s: &mut AstStruct) {
        let struct_type_id = if let Some(type_id) = s.type_id {
            type_id
        } else {
            unreachable!(
                "Should have called check_struct_name which should have resolved this structs type id"
            )
        };

        let new_fields: Vec<_> = s
            .fields
            .iter()
            .map(|f| {
                (
                    f.ident,
                    self.arena.var_type_to_typeid(&f.var_type, self.symbols),
                )
            })
            .collect();

        let struct_type = self.arena.kind_mut(struct_type_id);
        if let TypeKind::Struct(struct_id) = struct_type {
            let struct_id = *struct_id;
            self.arena.set_struct_fields(struct_id, new_fields);
        }
    }
    fn check_func(&mut self, f: &mut AstFunc) {
        let return_type_id = self.arena.var_type_to_typeid(&f.return_type, self.symbols);

        // allocate TypeIds for args
        let mut param_type_ids = vec![];
        let mut param_symbols = vec![];
        for arg in &mut f.args {
            let type_id = self.arena.var_type_to_typeid(&arg.var_type, self.symbols);
            let arg_symb = self.symbols.resolve_mut(arg.symbol_id);
            param_symbols.push(arg.symbol_id);
            if let SymbolKind::FnArg(data) = &mut arg_symb.kind {
                data.type_id = Some(type_id);
                param_type_ids.push(data.type_id.unwrap());
            } else {
                unreachable!()
            }
        }
        let fn_type = self.arena.make(TypeKind::Fn {
            params: param_type_ids,
            ret: return_type_id,
            param_symbols,
        });

        if let Some(body) = &mut f.body {
            self.check_block(body, Some(return_type_id), f.symbol_id, false);
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
    fn check_lvalue(
        &mut self,
        lvalue: &mut Lvalue,
        return_type_id: Option<TypeId>,
        fn_symbol_id: SymbolId,
        inside_loop: bool,
    ) -> Option<TypeId> {
        match &mut lvalue.kind {
            LvalueKind::Ident { symbol_id, .. } => {
                let sym = self.symbols.resolve((*symbol_id)?);
                match &sym.kind {
                    SymbolKind::Var(data) => data.type_id,
                    SymbolKind::FnArg(data) => data.type_id,
                    _ => None,
                }
            }
            LvalueKind::ArrayAccess { base, index } => {
                let base_span = base.span.clone();
                let base_type_id =
                    self.check_lvalue(base, return_type_id, fn_symbol_id, inside_loop)?;

                // Separate the borrow of arena.kind from any later self.* calls.
                let inner_type: Option<TypeId> = match self.arena.kind(base_type_id) {
                    TypeKind::Array { inner_type, .. } => Some(*inner_type),
                    _ => None,
                };
                if inner_type.is_none() {
                    self.errors.push(TypeCheckingError::AssignIndexNonArray {
                        got_type_str: self.arena.id_to_string(base_type_id),
                        lhs_span: base_span,
                    });
                }

                let index_span = index.span.clone();
                let index_type_id =
                    self.check_expr(index, return_type_id, fn_symbol_id, inside_loop)?;
                let index_is_valid = matches!(
                    self.arena.kind(index_type_id),
                    TypeKind::IntLiteral(_)
                        | TypeKind::I32
                        | TypeKind::U8
                        | TypeKind::U32
                        | TypeKind::U64
                );
                if !index_is_valid {
                    self.errors.push(TypeCheckingError::AssignIndexNotInteger {
                        got_type_str: self.arena.id_to_string(index_type_id),
                        index_span,
                    });
                }

                inner_type
            }
            LvalueKind::FieldAccess { base, .. } => {
                // TODO: implement when struct field assignment is added
                self.check_lvalue(base, return_type_id, fn_symbol_id, inside_loop);
                None
            }
        }
    }

    fn check_block(
        &mut self,
        block: &mut AstBlock,
        return_type_id: Option<TypeId>,
        fn_symbol_id: SymbolId,
        inside_loop: bool,
    ) -> Option<TypeId> {
        let mut block_return_id = None;
        for statement in block.statements.iter_mut() {
            if let Some(type_id) =
                self.check_statement(statement, return_type_id, fn_symbol_id, inside_loop)
            {
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
        inside_loop: bool,
    ) -> Option<TypeId> {
        match &mut expr.kind {
            ExprKind::Atom(atom) => {
                expr.type_id = Some(match atom {
                    Atom::Int(val) => self.arena.make(TypeKind::IntLiteral(*val)),
                    Atom::Bool(_) => self.arena.bool_type,
                    Atom::Str(_) => self.arena.str_type,
                    Atom::CStr(_) => self.arena.cstr_type,
                    Atom::Ident((_, symbol_id)) => {
                        let sym = self.symbols.resolve(symbol_id.unwrap_or_else(|| {
                            panic!("symbol should have been resolved for expr: {:?}", expr)
                        }));
                        match &sym.kind {
                            SymbolKind::Fn(data) => data.fn_type_id.unwrap(),
                            SymbolKind::Var(data) => data.type_id.unwrap(),
                            SymbolKind::Struct(data) => {
                                // Return the struct type for struct identifiers
                                self.arena.intern_struct_symbol(data.struct_id)
                            }
                            SymbolKind::Enum(data) => {
                                // Return the struct type for struct identifiers
                                self.arena.intern_enum_symbol(data.enum_id)
                            }
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
                                todo!(
                                    "could not find field in this struct with this ident, add error handling herre"
                                )
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
                                todo!(
                                    "could not find field in this struct with this ident, add error handling herre"
                                )
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
                            // TODO: add error here
                            _ => None,
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
                            t => todo!("{:?} is not valid for array access", t),
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
                    Op::BracketOpen { left: _, right: _ } => todo!(),
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
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        interner::{Interner, SharedInterner},
        lexer::Lexer,
    };
    use parking_lot::RwLock;

    struct TypeCheckTestCase {
        arena: TypeArena,
        symbols: SymbolTable,
        ast: Ast,
    }

    impl TypeCheckTestCase {
        fn from_source(src: &str) -> Self {
            let interner = SharedInterner::new(RwLock::new(Interner::new()));
            let mut symbols = SymbolTable::new(interner.clone());

            let lexer = Lexer::from_src_str(src, &interner).unwrap();
            let mut ast = Ast::from_tokens(lexer.tokens, interner.clone(), &mut symbols).unwrap();

            let mut arena = TypeArena::new();
            symbols.register_ast(&mut ast, &mut arena);

            Self {
                arena,
                symbols,
                ast,
            }
        }

        fn check(mut self) -> TypeCheckResult {
            let mut checker = TypeChecker::new(&mut self.arena, &mut self.symbols);
            checker.check_ast(&mut self.ast);

            TypeCheckResult {
                errors: checker.errors,
                ast: self.ast,
                arena: self.arena,
            }
        }
    }

    #[derive(Debug)]
    struct TypeCheckResult {
        errors: Vec<TypeCheckingError>,
        ast: Ast,
        arena: TypeArena,
    }

    impl TypeCheckResult {
        fn assert_no_errors(&self) {
            assert!(
                self.errors.is_empty(),
                "Expected no errors, got: {:?}",
                self.errors
            );
        }

        fn assert_error_count(&self, count: usize) {
            assert_eq!(self.errors.len(), count);
        }

        fn assert_has_error<F>(&self, predicate: F)
        where
            F: Fn(&TypeCheckingError) -> bool,
        {
            assert!(
                self.errors.iter().any(predicate),
                "No matching error found in: {:?}",
                self.errors
            );
        }
    }

    #[test]
    fn test_simple_addition() {
        let result = TypeCheckTestCase::from_source("fn main() I32 { 1 + 2 }").check();
        result.assert_no_errors();
    }
    #[test]
    fn test_mixed_type_arithmetic() {
        let result = TypeCheckTestCase::from_source(r#"fn main() I32 { 1 + true }"#).check();
        result.assert_error_count(1);
        result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
    }

    // ===== Function Call Tests =====

    #[test]
    fn test_function_wrong_arg_count() {
        let result = TypeCheckTestCase::from_source(
            r#"
              fn add(a I32, b I32) I32 { a + b }
              fn main() I32 { add(1) }
          "#,
        )
        .check();

        result.assert_error_count(1);
        result.assert_has_error(|e| {
            matches!(
                e,
                TypeCheckingError::MissingFnArgCall {
                    expected_arg_count: 2,
                    got_arg_count: 1,
                    ..
                }
            )
        });
    }

    // ===== If Expression Tests =====

    #[test]
    fn test_if_non_bool_condition() {
        let result = TypeCheckTestCase::from_source(
            r#"
              fn main() I32 {
                  if 5 { 1 } else { 2 }
              }
          "#,
        )
        .check();

        result.assert_has_error(|e| matches!(e, TypeCheckingError::IfConditionNotBool { .. }));
    }

    #[test]
    fn test_if_else_branch_mismatch() {
        let result = TypeCheckTestCase::from_source(
            r#"
              fn main() I32 {
                  if true { 1 } else { false }
              }
          "#,
        )
        .check();

        result.assert_has_error(|e| matches!(e, TypeCheckingError::IfElseBranchMismatch { .. }));
    }

    // ===== Arithmetic Operations - Extended =====

    #[test]
    fn test_subtraction_valid() {
        let result = TypeCheckTestCase::from_source("fn main() I32 { 10 - 5 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_multiplication_valid() {
        let result = TypeCheckTestCase::from_source("fn main() I32 { 3 * 7 }").check();
        dbg!(&result);
        result.assert_no_errors();
    }

    #[test]
    fn test_division_valid() {
        let result = TypeCheckTestCase::from_source("fn main() I32 { 20 / 4 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_subtraction_left_bool() {
        let result = TypeCheckTestCase::from_source("fn main() I32 { true - 5 }").check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
    }

    #[test]
    fn test_multiplication_right_bool() {
        let result = TypeCheckTestCase::from_source("fn main() I32 { 5 * false }").check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
    }

    #[test]
    fn test_division_left_string() {
        let result = TypeCheckTestCase::from_source(r#"fn main() I32 { "hello" / 2 }"#).check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
    }

    #[test]
    fn test_nested_arithmetic() {
        let result =
            TypeCheckTestCase::from_source("fn main() I32 { (1 + 2) * (3 - 4) / 5 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_arithmetic_with_variables() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 10;
                let y = 20;
                x + y * 2
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_arithmetic_with_function_result() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn get_num() I32 { 42 }
            fn main() I32 { get_num() + 10 }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_subtraction_both_sides_wrong() {
        let result = TypeCheckTestCase::from_source("fn main() I32 { true - false }").check();
        result.assert_error_count(2);
    }

    #[test]
    fn test_complex_arithmetic_chain() {
        let result =
            TypeCheckTestCase::from_source("fn main() I32 { 1 + 2 - 3 * 4 / 5 + 6 }").check();
        result.assert_no_errors();
    }

    // ===== Negation Operator =====

    #[test]
    fn test_negation_on_int() {
        let result = TypeCheckTestCase::from_source("fn main() I32 { -42 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_negation_on_bool() {
        let result = TypeCheckTestCase::from_source("fn main() I32 { -true }").check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
    }

    #[test]
    fn test_negation_on_string() {
        let result = TypeCheckTestCase::from_source(r#"fn main() I32 { -"hello" }"#).check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
    }

    #[test]
    fn test_double_negation() {
        let result = TypeCheckTestCase::from_source("fn main() I32 { --5 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_triple_negation() {
        let result = TypeCheckTestCase::from_source("fn main() I32 { ---10 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_negation_on_expression() {
        let result = TypeCheckTestCase::from_source("fn main() I32 { -(5 + 3) }").check();
        result.assert_no_errors();
    }

    // ===== Reference Operator =====

    #[test]
    fn test_reference_on_int() {
        let result = TypeCheckTestCase::from_source("fn main() &I32 { &42 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_reference_on_bool() {
        let result = TypeCheckTestCase::from_source("fn main() &Bool { &true }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_nested_reference() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 5;
                let y = &x;
                10
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_reference_in_arithmetic() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 5;
                let y = &x;
                10
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    // ===== Comparison Operators =====

    #[test]
    fn test_less_than_valid() {
        let result = TypeCheckTestCase::from_source("fn main() Bool { 5 < 10 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_greater_than_valid() {
        let result = TypeCheckTestCase::from_source("fn main() Bool { 10 > 5 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_less_than_eq_valid() {
        let result = TypeCheckTestCase::from_source("fn main() Bool { 5 <= 10 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_greater_than_eq_valid() {
        let result = TypeCheckTestCase::from_source("fn main() Bool { 10 >= 5 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_less_than_left_bool() {
        let result = TypeCheckTestCase::from_source("fn main() Bool { true < 5 }").check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::ComparisonTypeMismatch { .. }));
    }

    #[test]
    fn test_less_than_right_bool() {
        let result = TypeCheckTestCase::from_source("fn main() Bool { 5 < true }").check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::ComparisonTypeMismatch { .. }));
    }

    #[test]
    fn test_greater_than_both_bool() {
        let result = TypeCheckTestCase::from_source("fn main() Bool { true > false }").check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::ComparisonTypeMismatch { .. }));
    }

    #[test]
    fn test_less_than_eq_mixed() {
        let result = TypeCheckTestCase::from_source("fn main() Bool { 5 <= false }").check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::ComparisonTypeMismatch { .. }));
    }

    #[test]
    fn test_greater_than_eq_mixed() {
        let result = TypeCheckTestCase::from_source("fn main() Bool { true >= 10 }").check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::ComparisonTypeMismatch { .. }));
    }

    #[test]
    fn test_comparison_with_expressions() {
        let result = TypeCheckTestCase::from_source("fn main() Bool { (1 + 2) < (3 * 4) }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_comparison_with_variables() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() Bool {
                let x = 10;
                let y = 20;
                x < y
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_chained_comparisons() {
        let result = TypeCheckTestCase::from_source("fn main() Bool { 1 < 2 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_comparison_complex_left() {
        let result = TypeCheckTestCase::from_source("fn main() Bool { (10 - 5) * 2 > 8 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_comparison_complex_right() {
        let result = TypeCheckTestCase::from_source("fn main() Bool { 15 <= (3 + 4) * 2 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_comparison_with_function_call() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn get_num() I32 { 42 }
            fn main() Bool { get_num() > 10 }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_comparison_both_function_calls() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn get_a() I32 { 10 }
            fn get_b() I32 { 20 }
            fn main() Bool { get_a() < get_b() }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    // ===== Function Calls - Extended =====

    #[test]
    fn test_function_no_args() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn get_value() I32 { 42 }
            fn main() I32 { get_value() }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_function_three_args() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn add_three(a I32, b I32, c I32) I32 { a + b + c }
            fn main() I32 { add_three(1, 2, 3) }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_function_too_many_args() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn add(a I32, b I32) I32 { a + b }
            fn main() I32 { add(1, 2, 3) }
        "#,
        )
        .check();
        result.assert_has_error(|e| {
            matches!(
                e,
                TypeCheckingError::MissingFnArgCall {
                    expected_arg_count: 2,
                    got_arg_count: 3,
                    ..
                }
            )
        });
    }

    #[test]
    fn test_function_wrong_first_arg() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn add(a I32, b I32) I32 { a + b }
            fn main() I32 { add(true, 2) }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::FnInvalidArg { .. }));
    }

    #[test]
    fn test_function_wrong_second_arg() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn add(a I32, b I32) I32 { a + b }
            fn main() I32 { add(1, false) }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::FnInvalidArg { .. }));
    }

    #[test]
    fn test_function_wrong_middle_arg() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn add_three(a I32, b I32, c I32) I32 { a + b + c }
            fn main() I32 { add_three(1, true, 3) }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::FnInvalidArg { .. }));
    }

    #[test]
    fn test_function_multiple_wrong_args() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn add(a I32, b I32) I32 { a + b }
            fn main() I32 { add(true, false) }
        "#,
        )
        .check();
        result.assert_error_count(2);
    }

    #[test]
    fn test_nested_function_calls() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn inner(x I32) I32 { x * 2 }
            fn outer(y I32) I32 { inner(y + 1) }
            fn main() I32 { outer(5) }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_function_call_result_in_expr() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn get_val() I32 { 10 }
            fn main() I32 { get_val() + 5 }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_call_variable_not_function() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 5;
                x()
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::CallNonFunction { .. }));
    }

    #[test]
    fn test_multiple_function_calls_in_expr() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn a() I32 { 1 }
            fn b() I32 { 2 }
            fn c() I32 { 3 }
            fn main() I32 { a() + b() * c() }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    // ===== If Expressions - Extended =====

    #[test]
    fn test_if_bool_literal() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                if true { 42 } else { 0 }
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_if_comparison_condition() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                if 5 < 10 { 1 } else { 2 }
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_if_without_else() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                if true { 42 };
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_if_else_matching_types() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                if true { 10 } else { 20 }
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_multiple_else_if_matching() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                if false { 1 } else if true { 2 } else if false { 3 } else { 4 }
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_multiple_else_if_mismatched() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                if false { 1 } else if true { false } else { 3 }
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::IfElseBranchMismatch { .. }));
    }

    #[test]
    fn test_nested_if_expressions() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                if true {
                    if false { 1 } else { 2 }
                } else {
                    3
                }
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_if_in_arithmetic() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                (if true { 10 } else { 20 }) + 5
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_if_as_function_arg() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn use_val(x I32) I32 { x }
            fn main() I32 {
                use_val(if true { 5 } else { 10 })
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_if_else_if_non_bool_condition() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                if true {
                    1 
                } else if 5 {
                    2
                } else { 
                    3
                }
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::IfConditionNotBool { .. }));
    }

    #[test]
    fn test_if_with_block_body() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                if true {
                    let x = 5;
                    x + 10
                } else {
                    20
                }
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_if_else_type_mismatch_bool_int() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                if true { true } else { 10 }
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::IfElseBranchMismatch { .. }));
    }

    #[test]
    fn test_if_only_else_if_no_final_else() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                if false { 1 } else if true { 2 };
                42
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_if_string_condition() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                if "hello" { 1 } else { 2 }
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::IfConditionNotBool { .. }));
    }

    // ===== While Loops =====

    #[test]
    fn test_while_bool_condition() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                while true { break; };
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_while_int_condition() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                while 5 { break; };
                0
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::WhileConditionNotBool { .. }));
    }

    #[test]
    fn test_while_comparison_condition() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 0;
                while x < 10 { break; };
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_while_with_body() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 0;
                while x < 10 {
                    let y = x + 1;
                    break;
                };
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_break_inside_while() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                while true { break; };
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_break_outside_while() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                break;
                0
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::BreakOutsideLoop { .. }));
    }

    #[test]
    fn test_break_inside_nested_while() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                while true {
                    while false {
                        break;
                    };
                    break;
                };
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_while_empty_body() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                while false { };
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    // ===== Variable Declarations =====

    #[test]
    fn test_var_decl_int() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 42;
                x
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_var_decl_bool() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() Bool {
                let x = true;
                x
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_var_decl_with_arithmetic() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 10 + 20;
                x
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_var_decl_with_function_call() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn get_val() I32 { 42 }
            fn main() I32 {
                let x = get_val();
                x
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_multiple_var_decls() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 10;
                let y = 20;
                let z = 30;
                x + y + z
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_var_decl_complex_expr() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = (10 + 20) * 3 - 5;
                x
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    // ===== Assignments =====

    #[test]
    fn test_assignment_compatible_type() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 10;
                x = 20;
                x
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_assignment_incompatible_int_to_bool() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = true;
                x = 10;
                0
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::AssignmentMismatch { .. }));
    }

    #[test]
    fn test_assignment_incompatible_bool_to_int() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 10;
                x = true;
                x
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::AssignmentMismatch { .. }));
    }

    #[test]
    fn test_assignment_function_result() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn get_val() I32 { 42 }
            fn main() I32 {
                let x = 0;
                x = get_val();
                x
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_assignment_arithmetic_result() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 10;
                x = x + 5;
                x
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_multiple_assignments() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 10;
                let y = 20;
                x = 30;
                y = 40;
                x + y
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_reassignment_same_type() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 10;
                x = 20;
                x = 30;
                x
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_assignment_to_if_result() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 0;
                x = if true { 10 } else { 20 };
                x
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    // ===== Return Statements =====

    #[test]
    fn test_explicit_return_matching() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn foo() I32 {
                return 42;
            }
            fn main() I32 { foo() }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_explicit_return_mismatched() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn foo() I32 {
                return true;
            }
            fn main() I32 { 0 }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::FnInvalidReturnType { .. }));
    }

    #[test]
    fn test_block_return_matching() {
        let result = TypeCheckTestCase::from_source("fn main() I32 { 42 }").check();
        result.assert_no_errors();
    }

    #[test]
    fn test_block_return_mismatched() {
        let result = TypeCheckTestCase::from_source("fn main() I32 { true }").check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::FnInvalidReturnType { .. }));
    }

    #[test]
    fn test_return_in_nested_block() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn foo() I32 {
                {
                    return 42;
                }
            }
            fn main() I32 { foo() }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_return_in_if_branch() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn foo() I32 {
                if true {
                    return 42;
                } else {
                    return 0;
                }
            }
            fn main() I32 { foo() }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_return_in_else_branch() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn foo() I32 {
                if false {
                    0
                } else {
                    return 42;
                }
            }
            fn main() I32 { foo() }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_early_return_wrong_type() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn foo() I32 {
                if true {
                    return false;
                };
                42
            }
            fn main() I32 { foo() }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::FnInvalidReturnType { .. }));
    }

    #[test]
    fn test_multiple_returns_all_matching() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn foo(x I32) I32 {
                if x < 0 {
                    return 0;
                };
                if x > 100 {
                    return 100;
                };
                x
            }
            fn main() I32 { foo(50) }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_return_with_expression() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn foo() I32 {
                return 10 + 20 * 3;
            }
            fn main() I32 { foo() }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    // ===== Struct Operations =====

    #[test]
    fn test_struct_field_access() {
        let result = TypeCheckTestCase::from_source(
            r#"
            struct Point { x I32, y I32 }
            fn main() I32 {
                let p = Point { x: 10, y: 20 };
                p.x
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_struct_creation_all_fields() {
        let result = TypeCheckTestCase::from_source(
            r#"
            struct Point { x I32, y I32 }
            fn main() I32 {
                let p = Point { x: 10, y: 20 };
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_struct_creation_missing_field() {
        let result = TypeCheckTestCase::from_source(
            r#"
            struct Point { x I32, y I32 }
            fn main() I32 {
                let p = Point { x: 10 };
                0
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
    }

    #[test]
    fn test_struct_creation_extra_field() {
        let result = TypeCheckTestCase::from_source(
            r#"
            struct Point { x I32, y I32 }
            fn main() I32 {
                let p = Point { x: 10, y: 20, z: 30 };
                0
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
    }

    #[test]
    fn test_struct_creation_wrong_field_type() {
        let result = TypeCheckTestCase::from_source(
            r#"
            struct Point { x I32, y I32 }
            fn main() I32 {
                let p = Point { x: true, y: 20 };
                0
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
    }

    #[test]
    fn test_struct_creation_duplicate_field() {
        let result = TypeCheckTestCase::from_source(
            r#"
            struct Point { x I32, y I32 }
            fn main() I32 {
                let p = Point { x: 10, x: 20 };
                0
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
    }

    #[test]
    fn test_empty_struct() {
        let result = TypeCheckTestCase::from_source(
            r#"
            struct Empty { }
            fn main() I32 {
                let e = Empty { };
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_struct_as_function_param() {
        let result = TypeCheckTestCase::from_source(
            r#"
            struct Point { x I32, y I32 }
            fn use_point(p Point) I32 { 0 }
            fn main() I32 {
                let p = Point { x: 10, y: 20 };
                use_point(p)
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_struct_field_in_arithmetic() {
        let result = TypeCheckTestCase::from_source(
            r#"
            struct Point { x I32, y I32 }
            fn main() I32 {
                let p = Point { x: 10, y: 20 };
                p.x + p.y
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_nested_struct_field_access() {
        let result = TypeCheckTestCase::from_source(
            r#"
            struct Inner { val I32 }
            struct Outer { inner Inner }
            fn main() I32 {
                let inner = Inner { val: 42 };
                let outer = Outer { inner: inner };
                outer.inner.val
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_field_access_on_non_struct() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = 42;
                x.field
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
    }

    // ===== Array Operations =====

    #[test]
    fn test_array_init_homogeneous_ints() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let arr = [1, 2, 3];
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_array_init_homogeneous_bools() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let arr = [true, false, true];
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_array_init_heterogeneous() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let arr = [1, true, 3];
                0
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
    }

    #[test]
    fn test_array_init_empty() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let arr = [];
                0
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::ArrayNoInnerType { .. }));
    }

    #[test]
    fn test_array_with_expressions() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let arr = [1 + 2, 3 * 4, 5 - 1];
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_array_with_function_results() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn get_val() I32 { 42 }
            fn main() I32 {
                let arr = [get_val(), get_val()];
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_nested_arrays() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let arr = [[1, 2], [3, 4]];
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_array_mixed_expr_types() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let arr = [10, true];
                0
            }
        "#,
        )
        .check();
        result.assert_has_error(|e| matches!(e, TypeCheckingError::Mismatch { .. }));
    }

    // ===== Block Expressions =====

    #[test]
    fn test_empty_block() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                { };
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_block_single_statement() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                { let x = 5; };
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_block_multiple_statements() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                {
                    let x = 5;
                    let y = 10;
                    let z = x + y;
                };
                0
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_block_with_return_value() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let x = { 42 };
                x
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_nested_blocks() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                {
                    {
                        {
                            42
                        }
                    }
                }
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_block_in_arithmetic() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                { 10 } + { 20 }
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    // ===== Complex/Integration Tests =====

    #[test]
    fn test_multiple_errors_in_function() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn foo() I32 {
                let x = true + false;
                let y = 10 < "hello";
                if 5 { 1 } else { 2 }
            }
            fn main() I32 { 0 }
        "#,
        )
        .check();
        assert!(result.errors.len() >= 3);
    }

    #[test]
    fn test_complex_nested_expression() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                ((1 + 2) * (3 - 4)) / ((5 + 6) - (7 * 8))
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_function_calling_function() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn helper(x I32) I32 { x * 2 }
            fn caller(y I32) I32 { helper(y + 1) }
            fn main() I32 { caller(10) }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_mixed_control_flow() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                let result = 0;
                while result < 10 {
                    if result < 5 {
                        result = result + 1;
                    } else {
                        break;
                    };
                };
                result
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_deep_nesting() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                if true {
                    let x = {
                        if false {
                            while false {
                                break;
                            };
                            10
                        } else {
                            20
                        }
                    };
                    x + 5
                } else {
                    0
                }
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_program_with_multiple_functions() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn add(a I32, b I32) I32 { a + b }
            fn sub(a I32, b I32) I32 { a - b }
            fn mul(a I32, b I32) I32 { a * b }
            fn div(a I32, b I32) I32 { a / b }
            fn main() I32 {
                add(10, sub(20, mul(3, div(12, 4))))
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_function_with_struct_param() {
        let result = TypeCheckTestCase::from_source(
            r#"
            struct Point { x I32, y I32 }
            fn use_point(p Point) I32 { p.x + p.y }
            fn main() I32 {
                let pt = Point { x: 5, y: 10 };
                use_point(pt)
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_function_returning_struct() {
        let result = TypeCheckTestCase::from_source(
            r#"
            struct Point { x I32, y I32 }
            fn make_point(x I32, y I32) Point {
                Point { x: x, y: y }
            }
            fn main() I32 {
                let p = make_point(10, 20);
                p.x
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_deeply_nested_arithmetic() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() I32 {
                1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_complex_boolean_expression() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() Bool {
                (1 < 2) == (4 > 3)
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }

    #[test]
    fn test_boolean_expression() {
        let result = TypeCheckTestCase::from_source(
            r#"
            fn main() Bool {
                true == false
            }
        "#,
        )
        .check();
        result.assert_no_errors();
    }
}
