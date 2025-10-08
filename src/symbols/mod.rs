use crate::{
    ast::{
        Ast, VarType,
        ast_block::{AstBlock, AstStatement, StatementKind},
        ast_expr::{AstExpr, Atom, ExprKind, Op},
        ast_fn::AstFunc,
    },
    cl_export::cl_vals::CraneliftId,
    interner::{IdentId, SharedInterner},
    lexer::Span,
    symbols::error::SymbolError,
    types::{TypeArena, TypeId, TypeKind},
};
use rustc_hash::FxHashMap;

pub mod error;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymbolId(usize);

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
    pub struct_id: usize,
    pub full_def_span: Span,
}

#[derive(Debug)]
pub enum SymbolKind {
    Fn(FnSymbolData),
    FnArg(FnArgSymbolData),
    Var(VarSymbolData),
    Struct(StructSymbolData),
}

#[derive(Debug)]
pub struct Symbol {
    pub ident_id: IdentId,
    pub scope_depth: usize,
    pub kind: SymbolKind,
    pub cranelift_id: Option<CraneliftId>,
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

    pub fn lookup(&mut self, ident_id: IdentId) -> Option<SymbolId> {
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
            cranelift_id: None,
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

        for func in ast.extern_fns.iter_mut() {
            self.register_fn(types, func, &mut errs);
        }

        for func in ast.fns.iter_mut() {
            self.register_fn(types, func, &mut errs);
        }
        errs
    }

    pub fn register_fn(
        &mut self,
        types: &mut TypeArena,
        func: &mut AstFunc,
        errors: &mut Vec<SymbolError>,
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
        let type_kind = match &mut func.return_type {
            VarType::Void => todo!(),
            VarType::Int => TypeKind::Int,
            VarType::Bool => TypeKind::Bool,
            VarType::Uint => TypeKind::Uint,
            VarType::Str => TypeKind::Str,
            VarType::CStr => TypeKind::CStr,
            VarType::CChar => todo!(),
            VarType::Custom((ident_id, symbol_id_opt)) => {
                // fill symbol_id_opt by looking it up in the current scopes
                *symbol_id_opt = self.lookup(*ident_id);
                match symbol_id_opt {
                    Some(symbol_id) => {
                        let symbol = self.resolve(*symbol_id);
                        match &symbol.kind {
                            SymbolKind::Fn(_) => todo!(),
                            SymbolKind::FnArg(_) => todo!(),
                            SymbolKind::Var(_) => todo!(),
                            SymbolKind::Struct(_) => todo!(),
                        }
                    }
                    None => match self.interner.read().resolve(*ident_id) {
                        "Int" => TypeKind::Int,
                        "Uint" => TypeKind::Uint,
                        "Str" => TypeKind::Str,
                        "CStr" => TypeKind::CStr,
                        "Bool" => TypeKind::Bool,
                        // "CChar" => TypeKind::CChar,
                        _ => TypeKind::Unknown,
                    },
                }
            }
            VarType::Ref(_var_type) => todo!(),
        };

        // allocate the type for the return type
        let return_t = types.alloc(type_kind);

        // allocte fn params
        let mut params = vec![];
        let mut param_symbols = vec![];
        for arg in &func.args {
            let symb = self.resolve_mut(arg.symbol_id);
            let kind = arg.var_type.to_type_kind(types);
            let new_type_id = types.alloc(kind);
            match &mut symb.kind {
                SymbolKind::FnArg(data) => {
                    data.type_id = Some(new_type_id);
                }
                _ => unreachable!("fn arg symbol should have tag for fn arg"),
            }
            params.push(new_type_id);
            param_symbols.push(arg.symbol_id);
        }

        let fn_t = types.alloc(TypeKind::Fn {
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
            StatementKind::Decleration {
                symbol_id: _,
                ident_id: _,
                ident_token_at: _,
                expr,
            } => {
                self.register_expr(expr);
            }
            StatementKind::Assignment {
                ident_id: _,
                ident_token_at: _,
                expr,
                symbol_id: _,
            } => {
                self.register_expr(expr);
            }
            StatementKind::Expr(ast_expr) => {
                self.register_expr(ast_expr);
            }
            StatementKind::ExplicitReturn(ast_expr) => {
                self.register_expr(ast_expr);
            }
            StatementKind::BlockReturn { expr, .. } => {
                self.register_expr(expr);
            }
            StatementKind::WhileLoop { condition, block } => {
                self.register_expr(condition);
                self.register_block(block);
            }
        };
    }
    pub fn register_expr(&mut self, expr: &mut AstExpr) {
        match &mut expr.kind {
            ExprKind::Atom(atom) => match atom {
                Atom::Ident((ident_id, symbol_id)) => {
                    *symbol_id = self.lookup(*ident_id);
                }
                _ => (),
            },
            ExprKind::Op(op) => match &mut **op {
                Op::Add { left, right } => {
                    self.register_expr(left);
                    self.register_expr(right);
                }
                Op::Divide { left, right } => {
                    self.register_expr(left);
                    self.register_expr(right);
                }
                Op::Minus { left, right } => {
                    self.register_expr(left);
                    self.register_expr(right);
                }
                Op::LessThan { left, right } => {
                    self.register_expr(left);
                    self.register_expr(right);
                }
                Op::LessThanEq { left, right } => {
                    self.register_expr(left);
                    self.register_expr(right);
                }
                Op::GreaterThan { left, right } => {
                    self.register_expr(left);
                    self.register_expr(right);
                }
                Op::GreaterThanEq { left, right } => {
                    self.register_expr(left);
                    self.register_expr(right);
                }
                Op::Neg(ast_expr) => {
                    self.register_expr(ast_expr);
                }
                Op::Ref(ast_expr) => {
                    self.register_expr(ast_expr);
                }
                Op::Multiply { left, right } => {
                    self.register_expr(left);
                    self.register_expr(right);
                }
                Op::FnCall { ident, args } => {
                    self.register_expr(ident);
                    args.iter_mut().for_each(|expr| self.register_expr(expr));
                }
                Op::Dot { left, right } => {
                    self.register_expr(left);
                    self.register_expr(right);
                }
                Op::Block(block) => {
                    self.register_block(block);
                }
                Op::Equivalent { left, right } => {
                    self.register_expr(left);
                    self.register_expr(right);
                }
                Op::SquareOpen { left, args } => {
                    self.register_expr(left);
                    args.iter_mut().for_each(|expr| self.register_expr(expr));
                }
                Op::BracketOpen { left, right } => {
                    self.register_expr(left);
                    self.register_expr(right);
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
            },
        }
    }
}

trait ToTypeKind {
    fn to_type_kind(&self, types: &mut TypeArena) -> TypeKind;
}
impl ToTypeKind for VarType {
    fn to_type_kind(&self, types: &mut TypeArena) -> TypeKind {
        match &self {
            VarType::Void => todo!(),
            VarType::Int => TypeKind::Int,
            VarType::Bool => TypeKind::Bool,
            VarType::Uint => TypeKind::Uint,
            VarType::Str => TypeKind::Str,
            VarType::CStr => TypeKind::CStr,
            VarType::CChar => todo!(),
            VarType::Custom(_) => todo!(),
            VarType::Ref(var_type) => TypeKind::Ref(types.var_type_to_typeid(var_type)),
        }
    }
}
