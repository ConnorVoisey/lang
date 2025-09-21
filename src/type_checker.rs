use crate::{
    ast::{
        Ast, VarType,
        ast_block::{AstBlock, AstStatement, StatementKind},
        ast_expr::{AstExpr, Atom, ExprKind, Op},
        ast_fn::AstFunc,
    },
    lexer::Span,
    symbols::{SymbolKind, SymbolTable},
    types::{TypeArena, TypeId, TypeKind, error::UnifyError},
};

#[derive(Debug)]
pub struct TypeChecker<'a> {
    pub arena: &'a mut TypeArena,
    pub errors: Vec<UnifyError>,
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
        // allocate TypeIds for args
        for arg in &mut f.args {
            arg.type_id = Some(self.arena.var_type_to_typeid(&arg.var_type));
        }

        f.return_type_id = Some(self.arena.var_type_to_typeid(&f.return_type));

        // declare function symbol type
        let fn_type = self.arena.alloc(TypeKind::Fn {
            params: f.args.iter().map(|a| a.type_id.unwrap()).collect(),
            ret: f.return_type_id.unwrap(),
        });
        f.type_id = Some(fn_type);

        if let Some(body) = &mut f.body {
            self.check_block(body, f.return_type_id.unwrap());
        }

        // unify with symbol table entry (if it already has a type)
        // e.g., let sym = ast.symbols.resolve(f.symbol_id); unify here
    }

    fn check_statement(
        &mut self,
        statement: &mut AstStatement,
        return_type_id: TypeId,
    ) -> Option<TypeId> {
        dbg!(&statement);
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
                None
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
    fn check_block(&mut self, block: &mut AstBlock, return_type_id: TypeId) -> Option<TypeId> {
        let mut block_return_id = None;
        for statement in block.statements.iter_mut() {
            if let Some(type_id) = self.check_statement(statement, return_type_id) {
                block_return_id = Some(type_id);
            }
        }
        block_return_id
    }
    fn check_expr(&mut self, expr: &mut AstExpr, return_type_id: TypeId) -> Option<TypeId> {
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
                                param_type_ids: _,
                                return_type_id: _,
                            } => fn_type_id.unwrap(),
                            SymbolKind::Var {
                                type_id,
                                is_used: _,
                                is_mutable: _,
                            } => type_id.unwrap(),
                            SymbolKind::Struct {
                                param_type_ids: _,
                                struct_id: _,
                            } => todo!(),
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
                            self.errors.push(UnifyError::Mismatch {
                                type_a_str: format!("{}", lt.0),
                                type_a_span: Span {
                                    start: left.start_token_at,
                                    end: left.end_token_at,
                                },
                                type_b_str: format!("{}", rt.0),
                                type_b_span: Span {
                                    start: right.start_token_at,
                                    end: right.end_token_at,
                                },
                            });
                        }
                        if let Err(_) = self.arena.unify(rt, int_t) {
                            self.errors.push(UnifyError::Mismatch {
                                type_a_str: format!("{}", lt.0),
                                type_a_span: Span {
                                    start: left.start_token_at,
                                    end: left.end_token_at,
                                },
                                type_b_str: format!("{}", rt.0),
                                type_b_span: Span {
                                    start: right.start_token_at,
                                    end: right.end_token_at,
                                },
                            });
                        }
                        expr.type_id = Some(int_t);
                        expr.type_id
                    }
                    Op::Neg(inner) => {
                        let t = self.check_expr(inner, return_type_id).unwrap();
                        let int_t = self.arena.alloc(TypeKind::Int);
                        if let Err(_) = self.arena.unify(t, int_t) {
                            self.errors.push(UnifyError::Mismatch {
                                type_a_str: format!("{}", t.0),
                                type_a_span: Span {
                                    start: inner.start_token_at,
                                    end: inner.end_token_at,
                                },
                                type_b_str: format!("{}", int_t.0),
                                type_b_span: Span {
                                    start: inner.start_token_at,
                                    end: inner.end_token_at,
                                },
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

                        let (params_t, ret_t) = match self.arena.kind(ident.type_id.unwrap()) {
                            // Don't like this clone, it is only a vec of usize, but I don't think it
                            // should be required
                            TypeKind::Fn { params, ret } => (params.clone(), *ret),
                            t => {
                                dbg!(t);
                                todo!("handle error, tried calling a non function e.g. 5()");
                            }
                        };
                        let arg_types: Vec<_> = args
                            .iter_mut()
                            .map(|a| self.check_expr(a, return_type_id).unwrap())
                            .collect();
                        if params_t.len() != arg_types.len() {
                            dbg!(&params_t, &arg_types, ident.type_id, &self.arena);
                            todo!("handle error, invalid arg count to call fn");
                        }
                        for (i, param_t) in params_t.iter().enumerate() {
                            let arg_t = arg_types[i];
                            if let Err(e) = self.arena.unify(*param_t, arg_t) {
                                dbg!(e);
                                panic!();
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
                                if let Some(v) = unconditional_else {
                                    if self.check_block(v, return_type_id).is_some() {
                                        panic!("if block was none but else case had a value")
                                    }
                                };
                            }
                            Some(if_id) => {
                                todo!()
                                // for else_id in else_ifs.iter_mut().map(|(_, else_block)| {
                                //     self.check_block(else_block, return_type_id)
                                // }) {
                                //     self.arena.unify(if_block_return_id, else_id);
                                // }
                                // let else_return_id = match unconditional_else {
                                //     Some(v) => self.check_block(v, return_type_id),
                                //     None => None,
                                // };
                            }
                        }
                        if_block_return_id
                    }
                    // other ops...
                    _ => {
                        let fresh = self.arena.alloc_var();
                        expr.type_id = Some(fresh);
                        expr.type_id
                    }
                }
            }
        }
    }
}
