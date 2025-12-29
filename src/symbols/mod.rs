use crate::{
    ast::{
        Ast, VarType,
        ast_block::{AstBlock, AstStatement, StatementKind},
        ast_expr::{AstExpr, Atom, ExprKind, Op},
        ast_fn::AstFunc,
        ast_struct::{AstStruct, AstStructField},
    },
    interner::{IdentId, SharedInterner},
    lexer::Span,
    symbols::error::SymbolError,
    types::{EnumId, StructId, TypeArena, TypeId, TypeKind},
};
use rustc_hash::FxHashMap;

pub mod error;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymbolId(pub usize);

#[derive(Debug)]
pub struct FnSymbolData {
    pub fn_type_id: Option<TypeId>,
    pub return_type_id: Option<TypeId>,
    pub return_type_span: Span,
    pub full_signature_span: Span,
}

#[derive(Debug)]
pub struct FnArgSymbolData {
    pub type_id: Option<TypeId>,
    pub is_used: bool,
    pub is_mutable: bool,
    pub type_span: Span,
}

#[derive(Debug)]
pub struct VarSymbolData {
    pub type_id: Option<TypeId>,
    pub is_used: bool,
    pub is_mutable: bool,
}

#[derive(Debug)]
pub struct StructSymbolData {
    pub struct_id: StructId,
    pub full_def_span: Span,
}

#[derive(Debug)]
pub struct EnumSymbolData {
    pub enum_id: EnumId,
    pub full_def_span: Span,
}

#[derive(Debug)]
pub enum SymbolKind {
    Fn(FnSymbolData),
    FnArg(FnArgSymbolData),
    Var(VarSymbolData),
    Struct(StructSymbolData),
    Enum(EnumSymbolData),
}

#[derive(Debug)]
pub struct Symbol {
    pub ident_id: IdentId,
    pub scope_depth: usize,
    pub kind: SymbolKind,
    pub ident_span: Span,
}

#[derive(Debug)]
pub struct SymbolTable {
    pub scopes: Vec<FxHashMap<IdentId, SymbolId>>,
    pub symbols: Vec<Symbol>,
    pub interner: SharedInterner,
}

impl SymbolTable {
    pub fn new(interner: SharedInterner) -> Self {
        Self {
            scopes: vec![FxHashMap::default()],
            symbols: vec![],
            interner,
        }
    }
    pub fn push_scope(&mut self) {
        self.scopes.push(FxHashMap::default());
    }

    pub fn pop_scope(&mut self) {
        self.scopes.pop().expect("No scopes to remove");
    }

    pub fn lookup(&self, ident_id: IdentId) -> Option<SymbolId> {
        for scope in self.scopes.iter().rev() {
            if let Some(symbol_id) = scope.get(&ident_id) {
                return Some(*symbol_id);
            }
        }
        None
    }

    pub fn declare(&mut self, ident_id: IdentId, symbol_kind: SymbolKind, span: Span) -> SymbolId {
        let id = SymbolId(self.symbols.len());
        let scope_depth = self.scopes.len() - 1;
        self.symbols.push(Symbol {
            ident_id,
            kind: symbol_kind,
            scope_depth,
            ident_span: span,
        });
        let last_scope = self
            .scopes
            .last_mut()
            .expect("Tried to declare symbol but there are no stacks left");
        last_scope.insert(ident_id, id);
        id
    }

    pub fn resolve(&self, symbol_id: SymbolId) -> &Symbol {
        &self.symbols[symbol_id.0]
    }
    pub fn resolve_mut(&mut self, symbol_id: SymbolId) -> &mut Symbol {
        &mut self.symbols[symbol_id.0]
    }

    pub fn register_ast(&mut self, ast: &mut Ast, types: &mut TypeArena) -> Vec<SymbolError> {
        let mut errs = vec![];

        for struct_decl in ast.structs.iter_mut() {
            self.register_struct(types, struct_decl, &mut errs);
        }

        for func in ast.extern_fns.iter_mut() {
            self.register_fn(types, func, &mut errs);
        }

        for func in ast.fns.iter_mut() {
            self.register_fn(types, func, &mut errs);
        }
        errs
    }

    /// Recursively resolves symbol IDs in a VarType
    /// This is needed before converting VarType to TypeKind
    fn resolve_var_type_symbols(&mut self, var_type: &mut VarType) {
        match var_type {
            VarType::Custom((ident_id, symbol_id_opt)) => {
                *symbol_id_opt = self.lookup(*ident_id);
            }
            VarType::Array { var_type, .. } => {
                self.resolve_var_type_symbols(&mut *var_type);
            }
            VarType::Ref(inner) => {
                self.resolve_var_type_symbols(inner);
            }
            // Primitive types don't need resolution
            VarType::Void
            | VarType::Int
            | VarType::Bool
            | VarType::Uint
            | VarType::Str
            | VarType::CStr
            | VarType::CChar => {}
        }
    }

    pub fn register_struct(
        &mut self,
        types: &mut TypeArena,
        struct_decl: &mut AstStruct,
        _errors: &mut Vec<SymbolError>,
    ) {
        let sym_id = struct_decl.symbol_id;
        let struct_id = match &self.resolve(sym_id).kind {
            SymbolKind::Struct(data) => data.struct_id,
            t => unreachable!("struct_symbol should always have SymbolKind::Struct, got: {t:?}"),
        };

        let mut field_type_ids = Vec::with_capacity(struct_decl.fields.len());
        let mut fields_for_typekind = Vec::with_capacity(struct_decl.fields.len());

        for AstStructField {
            ident,
            ident_token_at: _,
            var_type,
        } in &mut struct_decl.fields
        {
            let field_type_id = match var_type {
                VarType::Custom((ident_id, symbol_id_opt)) => {
                    *symbol_id_opt = self.lookup(*ident_id);
                    match symbol_id_opt {
                        Some(symbol_id) => {
                            let symbol = self.resolve(*symbol_id);
                            match &symbol.kind {
                                SymbolKind::Struct(data) => {
                                    types.intern_struct_symbol(data.struct_id)
                                }
                                _ => types.var_type_to_typeid(var_type, self),
                            }
                        }
                        None => types.var_type_to_typeid(var_type, self),
                    }
                }
                _ => types.var_type_to_typeid(var_type, self),
            };
            field_type_ids.push(Some(field_type_id));
            fields_for_typekind.push((*ident, field_type_id));
        }

        // Intern the struct type (creates or returns existing TypeId)
        let struct_type_id = types.intern_struct_symbol(struct_id);

        // Update the struct's TypeKind with the computed field types
        let struct_type = types.kind(struct_type_id);
        if let TypeKind::Struct(struct_id) = struct_type {
            types.set_struct_fields(*struct_id, fields_for_typekind);
        }

        struct_decl.type_id = Some(struct_type_id);
        struct_decl.field_type_ids = field_type_ids;
        struct_decl.struct_id = struct_id;
    }

    pub fn register_fn(
        &mut self,
        types: &mut TypeArena,
        func: &mut AstFunc,
        _errors: &mut Vec<SymbolError>,
    ) {
        // We will not hold a long-lived mutable borrow to `self` while we call lookup/resolve.
        // First, ensure the symbol exists and is a function (immutable borrow).
        let sym_id = func.symbol_id;
        match &self.resolve(sym_id).kind {
            SymbolKind::Fn(_) => (),
            t => unreachable!("fn_symbol should always have SymbolKind::Fn, got: {t:?}"),
        }

        // Compute the TypeKind for the function return type.
        // This may call self.lookup(...) which requires &mut self, but that's okay because we don't
        // hold any mutable borrows to a particular symbol right now.
        let return_t = match &mut func.return_type {
            VarType::Custom((ident_id, symbol_id_opt)) => {
                // fill symbol_id_opt by looking it up in the current scopes
                *symbol_id_opt = self.lookup(*ident_id);
                let kind = match symbol_id_opt {
                    Some(symbol_id) => {
                        let symbol = self.resolve(*symbol_id);
                        match &symbol.kind {
                            SymbolKind::Fn(_) => todo!(),
                            SymbolKind::FnArg(_) => todo!(),
                            SymbolKind::Var(_) => todo!(),
                            SymbolKind::Struct(struct_symbol) => {
                                TypeKind::Struct(struct_symbol.struct_id)
                            }
                            SymbolKind::Enum(_) => todo!(),
                        }
                    }
                    None => match self.interner.read().resolve(*ident_id) {
                        "Int" => TypeKind::I32,
                        "Uint" => TypeKind::U64,
                        "Str" => TypeKind::Str,
                        "CStr" => TypeKind::CStr,
                        "Bool" => TypeKind::Bool,
                        // "CChar" => TypeKind::CChar,
                        _ => TypeKind::Unknown,
                    },
                };
                types.make(kind)
            }
            _ => types.var_type_to_typeid(&func.return_type, self),
        };

        // allocte fn params
        let mut params = vec![];
        let mut param_symbols = vec![];
        for arg in &mut func.args {
            // Resolve symbol IDs in the VarType before converting to TypeKind
            self.resolve_var_type_symbols(&mut arg.var_type);
            let kind = arg.var_type.to_type_kind(types, &self);
            let symb = self.resolve_mut(arg.symbol_id);
            let new_type_id = types.make(kind);
            match &mut symb.kind {
                SymbolKind::FnArg(data) => {
                    data.type_id = Some(new_type_id);
                }
                _ => unreachable!("fn arg symbol should have tag for fn arg"),
            }
            params.push(new_type_id);
            param_symbols.push(arg.symbol_id);
        }

        let fn_t = types.make(TypeKind::Fn {
            params,
            param_symbols,
            ret: return_t,
        });

        {
            let fn_symbol = self.resolve_mut(sym_id);
            match &mut fn_symbol.kind {
                SymbolKind::Fn(data) => {
                    data.return_type_id = Some(return_t);
                    data.fn_type_id = Some(fn_t);
                }
                t => unreachable!("fn_symbol should always have SymbolKind::Fn, got: {t:?}"),
            }
        }

        // register function bodies (locals and expressions)
        if let Some(block) = &mut func.body {
            self.register_block(block);
        }
    }

    pub fn register_block(&mut self, block: &mut AstBlock) {
        for statement in &mut block.statements {
            self.register_statement(statement);
        }
    }

    pub fn register_statement(&mut self, statement: &mut AstStatement) {
        match &mut statement.kind {
            StatementKind::Decleration { expr, .. }
            | StatementKind::Assignment { expr, .. }
            | StatementKind::BlockReturn { expr, .. } => {
                self.register_expr(expr);
            }
            StatementKind::Expr(ast_expr) | StatementKind::ExplicitReturn(ast_expr) => {
                self.register_expr(ast_expr);
            }
            StatementKind::WhileLoop { condition, block } => {
                self.register_expr(condition);
                self.register_block(block);
            }
            StatementKind::Break { .. } => (),
        };
    }
    pub fn register_expr(&mut self, expr: &mut AstExpr) {
        match &mut expr.kind {
            ExprKind::Atom(atom) => {
                if let Atom::Ident((ident_id, symbol_id)) = atom {
                    *symbol_id = self.lookup(*ident_id);
                }
            }
            ExprKind::Op(op) => match &mut **op {
                Op::Add { left, right }
                | Op::Minus { left, right }
                | Op::Multiply { left, right }
                | Op::Divide { left, right }
                | Op::LessThan { left, right }
                | Op::LessThanEq { left, right }
                | Op::GreaterThan { left, right }
                | Op::GreaterThanEq { left, right }
                | Op::Dot { left, right }
                | Op::DoubleColon { left, right }
                | Op::Equivalent { left, right }
                | Op::BracketOpen { left, right } => {
                    self.register_expr(left);
                    self.register_expr(right);
                }
                Op::Neg(ast_expr) => {
                    self.register_expr(ast_expr);
                }
                Op::Ref(ast_expr) => {
                    self.register_expr(ast_expr);
                }
                Op::FnCall { ident, args } => {
                    self.register_expr(ident);
                    args.iter_mut().for_each(|expr| self.register_expr(expr));
                }
                Op::Block(block) => {
                    self.register_block(block);
                }
                Op::ArrayAccess { left, right } => {
                    self.register_expr(left);
                    self.register_expr(right);
                }
                Op::ArrayInit { args } => {
                    args.iter_mut().for_each(|expr| self.register_expr(expr));
                }
                Op::IfCond {
                    condition,
                    block,
                    else_ifs,
                    unconditional_else,
                } => {
                    self.register_expr(condition);
                    for statement in block.statements.iter_mut() {
                        self.register_statement(statement);
                    }
                    for else_if in else_ifs.iter_mut() {
                        self.register_expr(&mut else_if.0);
                        for statement in &mut else_if.1.statements.iter_mut() {
                            self.register_statement(statement);
                        }
                    }
                    if let Some(else_block) = unconditional_else {
                        for statement in else_block.statements.iter_mut() {
                            self.register_statement(statement);
                        }
                    }
                }
                Op::StructCreate {
                    ident,
                    args,
                    symbol_id: _,
                } => {
                    self.register_expr(ident);
                    // TODO: might need to set the symbol_id here
                    for (_, expr) in args.iter_mut() {
                        self.register_expr(expr);
                    }
                }
            },
        }
    }
}

trait ToTypeKind {
    fn to_type_kind(&self, types: &mut TypeArena, symbols: &SymbolTable) -> TypeKind;
}
impl ToTypeKind for VarType {
    fn to_type_kind(&self, types: &mut TypeArena, symbols: &SymbolTable) -> TypeKind {
        match &self {
            VarType::Void => todo!(),
            VarType::Int => TypeKind::I32,
            VarType::Bool => TypeKind::Bool,
            VarType::Uint => TypeKind::U64,
            VarType::Str => TypeKind::Str,
            VarType::CStr => TypeKind::CStr,
            VarType::CChar => todo!(),
            VarType::Custom((_, symbol_id_opt)) => {
                let symbol_id = match symbol_id_opt {
                    Some(symbol_id) => symbol_id,
                    None => todo!(),
                };
                match &symbols.resolve(*symbol_id).kind {
                    SymbolKind::Fn(fn_symbol_data) => todo!(),
                    SymbolKind::FnArg(fn_arg_symbol_data) => todo!(),
                    SymbolKind::Var(var_symbol_data) => todo!(),
                    SymbolKind::Struct(struct_symbol_data) => {
                        TypeKind::Struct(struct_symbol_data.struct_id)
                    }
                    SymbolKind::Enum(enum_symbol_data) => todo!(),
                }
            }
            VarType::Ref(var_type) => TypeKind::Ref(types.var_type_to_typeid(var_type, symbols)),
            VarType::Array { var_type, count } => TypeKind::Array {
                size: *count,
                inner_type: types.var_type_to_typeid(&var_type, symbols),
            },
        }
    }
}
