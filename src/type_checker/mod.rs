use crate::{
    ast::{
        Ast,
        ast_block::{AstBlock, Lvalue, LvalueKind},
        ast_fn::AstFunc,
        ast_struct::AstStruct,
    },
    symbols::{SymbolId, SymbolKind, SymbolTable},
    type_checker::error::TypeCheckingError,
    types::{TypeArena, TypeId, TypeKind},
};

pub mod error;
pub mod expr;
pub mod statement;

#[cfg(test)]
mod tests;

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
}
