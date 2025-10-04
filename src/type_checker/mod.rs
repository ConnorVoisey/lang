use crate::{
    ast::{
        Ast,
        ast_block::{AstBlock, AstStatement, StatementKind},
        ast_expr::{AstExpr, Atom, ExprKind, Op},
        ast_fn::AstFunc,
    },
    symbols::{SymbolKind, SymbolTable},
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
            if let SymbolKind::FnArg { type_id, .. } = &mut arg_symb.kind {
                *type_id = Some(self.arena.var_type_to_typeid(&arg.var_type));
                param_type_ids.push(type_id.unwrap());
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
            self.check_block(body, Some(return_type_id));
        }
        let fn_symb = self.symbols.resolve_mut(f.symbol_id);
        match &mut fn_symb.kind {
            SymbolKind::Fn {
                fn_type_id: fn_type_slot,
                return_type_id: ret_slot,
            } => {
                *fn_type_slot = Some(fn_type);
                *ret_slot = Some(return_type_id);
            }
            _ => unreachable!(),
        }
    }

    fn check_statement(
        &mut self,
        statement: &mut AstStatement,
        return_type_id: Option<TypeId>,
    ) -> Option<TypeId> {
        match &mut statement.kind {
            StatementKind::Decleration {
                ident_token_at: _,
                ident_id: _,
                symbol_id,
                expr,
            } => {
                let new_type_id = self.check_expr(expr, return_type_id);
                let sym = self.symbols.resolve_mut(*symbol_id);
                match &mut sym.kind {
                    SymbolKind::Var {
                        type_id,
                        is_used: _,
                        is_mutable: _,
                    } => {
                        *type_id = new_type_id;
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
                let new_type_id = self.check_expr(expr, return_type_id).unwrap();
                let sym = self.symbols.resolve(symbol_id.unwrap());
                match &sym.kind {
                    SymbolKind::Var {
                        type_id,
                        is_used: _,
                        is_mutable: _,
                    } => {
                        if let Err(e) = self.arena.unify(type_id.unwrap(), new_type_id) {
                            dbg!(e);
                            panic!();
                        }
                    }
                    _ => unreachable!(
                        "Just checked that the statement was a var so the symbol for it should be a var as well"
                    ),
                }
                None
            }
            StatementKind::Expr(ast_expr) => {
                ast_expr.type_id = self.check_expr(ast_expr, return_type_id);
                ast_expr.type_id
            }
            StatementKind::ExplicitReturn(ast_expr) => {
                let return_type_id = self.check_expr(ast_expr, return_type_id).unwrap();
                if let Err(e) = self.arena.unify(return_type_id, return_type_id) {
                    dbg!(e);
                    panic!();
                }
                Some(return_type_id)
            }
            StatementKind::BlockReturn(ast_expr) => {
                let return_type_id = self.check_expr(ast_expr, return_type_id).unwrap();
                if let Err(e) = self.arena.unify(return_type_id, return_type_id) {
                    dbg!(e);
                    panic!();
                }
                Some(return_type_id)
            }
        }
    }
    fn check_block(
        &mut self,
        block: &mut AstBlock,
        return_type_id: Option<TypeId>,
    ) -> Option<TypeId> {
        let mut block_return_id = None;
        for statement in block.statements.iter_mut() {
            if let Some(type_id) = self.check_statement(statement, return_type_id) {
                block_return_id = Some(type_id);
            }
        }
        block.type_id = block_return_id;
        dbg!(block_return_id);
        block_return_id
    }
    fn check_expr(&mut self, expr: &mut AstExpr, return_type_id: Option<TypeId>) -> Option<TypeId> {
        match &mut expr.kind {
            ExprKind::Atom(atom) => {
                expr.type_id = Some(match atom {
                    Atom::Int(_) => self.arena.alloc(TypeKind::Int),
                    Atom::Bool(_) => self.arena.alloc(TypeKind::Bool),
                    Atom::Str(_) => self.arena.alloc(TypeKind::Str),
                    Atom::CStr(_) => self.arena.alloc(TypeKind::CStr),
                    Atom::Ident((_, symbol_id)) => {
                        let sym = self.symbols.resolve(symbol_id.unwrap());
                        match &sym.kind {
                            SymbolKind::Fn {
                                fn_type_id,
                                return_type_id: _,
                            } => fn_type_id.unwrap(),
                            SymbolKind::Var {
                                type_id,
                                is_used: _,
                                is_mutable: _,
                            } => type_id.unwrap(),
                            SymbolKind::Struct { struct_id: _ } => todo!(),
                            SymbolKind::FnArg {
                                type_id,
                                is_used: _,
                                is_mutable: _,
                            } => type_id.unwrap(),
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
                        let lt = self.check_expr(left, return_type_id).unwrap();
                        let rt = self.check_expr(right, return_type_id).unwrap();
                        let int_t = self.arena.alloc(TypeKind::Int);
                        if let Err(_) = self.arena.unify(lt, int_t) {
                            self.errors.push(TypeCheckingError::Mismatch {
                                type_a_str: format!("{}", lt.0),
                                type_a_span: left.span.clone(),
                                type_b_str: format!("{}", rt.0),
                                type_b_span: right.span.clone(),
                            });
                        }
                        if let Err(_) = self.arena.unify(rt, int_t) {
                            self.errors.push(TypeCheckingError::Mismatch {
                                type_a_str: format!("{}", lt.0),
                                type_a_span: left.span.clone(),
                                type_b_str: format!("{}", rt.0),
                                type_b_span: right.span.clone(),
                            });
                        }
                        expr.type_id = Some(int_t);
                        expr.type_id
                    }
                    Op::Neg(inner) => {
                        let t = self.check_expr(inner, return_type_id).unwrap();
                        let int_t = self.arena.alloc(TypeKind::Int);
                        if let Err(_) = self.arena.unify(t, int_t) {
                            self.errors.push(TypeCheckingError::Mismatch {
                                type_a_str: format!("{}", t.0),
                                type_a_span: inner.span.clone(),
                                type_b_str: format!("{}", int_t.0),
                                type_b_span: inner.span.clone(),
                            });
                        }
                        expr.type_id = Some(int_t);
                        expr.type_id
                    }
                    Op::Ref(inner) => {
                        let inner_t = self.check_expr(inner, return_type_id).unwrap();
                        let ref_t = self.arena.alloc(TypeKind::Ref(inner_t));
                        expr.type_id = Some(ref_t);
                        expr.type_id
                    }
                    Op::FnCall { ident, args } => {
                        let _ = self.check_expr(ident, return_type_id);
                        // TODO: this is a funtion type, not sure how or even if it should be checked,
                        // guess just check that it is a function type
                        let (params_t, param_symbols, ret_t) =
                            match self.arena.kind(ident.type_id.unwrap()) {
                                // Don't like this clone, it is only a vec of usize, but I don't think it
                                // should be required
                                TypeKind::Fn {
                                    params,
                                    ret,
                                    param_symbols,
                                } => (params.clone(), param_symbols.clone(), *ret),
                                t => {
                                    dbg!(t);
                                    todo!("handle error, tried calling a non function e.g. 5()");
                                }
                            };
                        let arg_types: Vec<_> = args
                            .iter_mut()
                            .map(|a| (self.check_expr(a, return_type_id).unwrap(), a))
                            .collect();
                        if params_t.len() != arg_types.len() {
                            dbg!(&params_t, &arg_types, ident.type_id, &self.arena);
                            todo!("handle error, invalid arg count to call fn");
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
                                    fn_arg_def_span: param_symbol.span.clone(),
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
                        // all blocks must return the same value
                        let if_block_return_id = self.check_block(block, return_type_id);
                        match if_block_return_id {
                            None => {
                                for else_id in else_ifs.iter_mut().map(|(_, else_block)| {
                                    self.check_block(else_block, return_type_id)
                                }) {
                                    if else_id.is_some() {
                                        panic!("if block was none but else case had a value")
                                    }
                                }
                                if let Some(v) = unconditional_else
                                    && self.check_block(v, return_type_id).is_some()
                                {
                                    panic!("if block was none but else case had a value")
                                };
                            }
                            Some(t) => {
                                for else_id in else_ifs.iter_mut() {
                                    if let Some(else_t) =
                                        self.check_block(&mut else_id.1, return_type_id)
                                    {
                                        if self.arena.unify(t, else_t).is_err() {
                                            panic!();
                                        }
                                    }
                                }
                                let else_return_id = match unconditional_else {
                                    Some(v) => self.check_block(v, return_type_id),
                                    None => None,
                                };
                                // TODO: unify and check all block types are equal
                            }
                        }
                        if_block_return_id
                    }
                    Op::LessThan { left, right } => todo!(),
                    Op::LessThanEq { left, right } => todo!(),
                    Op::GreaterThan { left, right } => todo!(),
                    Op::GreaterThanEq { left, right } => todo!(),
                    Op::Dot { left, right } => todo!(),
                    Op::Block(ast_block) => {
                        let type_id = self.check_block(ast_block, return_type_id);
                        expr.type_id = type_id;
                        type_id
                    }
                    Op::Equivalent { left, right } => todo!(),
                    Op::SquareOpen { left, args } => todo!(),
                    Op::BracketOpen { left, right } => todo!(),
                }
            }
        }
    }
}
