use crate::{
    ast::{
        Ast, VarType,
        ast_block::StatementKind,
        ast_expr::{AstExpr, Atom, ExprKind, Op},
        ast_fn::AstFunc,
    },
    interner::{IdentId, SharedInterner},
    symbols::error::SymbolError,
    type_checker::TypeChecker,
    types::{TypeArena, TypeId, TypeKind},
};
use rustc_hash::FxHashMap;

pub mod error;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymbolId(usize);

#[derive(Debug)]
pub enum SymbolKind {
    Fn {
        fn_type_id: Option<TypeId>,
        param_type_ids: Vec<Option<TypeId>>,
        return_type_id: Option<TypeId>,
    },
    FnArg {
        type_id: Option<TypeId>,
        is_used: bool,
        is_mutable: bool,
    },
    Var {
        type_id: Option<TypeId>,
        is_used: bool,
        is_mutable: bool,
    },
    Struct {
        struct_id: usize,
        param_type_ids: Vec<(IdentId, Option<TypeId>)>,
    },
}
#[derive(Debug)]
pub struct Symbol {
    pub ident_id: IdentId,
    pub scope_depth: usize,
    pub kind: SymbolKind,
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

    pub fn declare(&mut self, ident_id: IdentId, symbol_kind: SymbolKind) -> SymbolId {
        let id = SymbolId(self.symbols.len());
        let scope_depth = self.scopes.len() - 1;
        self.symbols.push(Symbol {
            ident_id,
            kind: symbol_kind,
            scope_depth,
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
        _: &mut Vec<SymbolError>,
    ) {
        // We will not hold a long-lived mutable borrow to `self` while we call lookup/resolve.
        // First, ensure the symbol exists and is a function (immutable borrow).
        let sym_id = func.symbol_id;
        match &self.resolve(sym_id).kind {
            SymbolKind::Fn { .. } => (),
            t => unreachable!("fn_symbol should always have SymbolKind::Fn, got: {t:?}"),
        }

        // Compute the TypeKind for the function return type.
        // This may call self.lookup(...) which requires &mut self, but that's okay because we don't
        // hold any mutable borrows to a particular symbol right now.
        let type_kind = match &mut func.return_type {
            VarType::Void => todo!(),
            VarType::Int => TypeKind::Int,
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
                            SymbolKind::Fn { .. } => todo!(),
                            SymbolKind::FnArg { .. } => todo!(),
                            SymbolKind::Var { .. } => todo!(),
                            SymbolKind::Struct { .. } => todo!(),
                        }
                    }
                    None => match self.interner.read().resolve(*ident_id) {
                        "Int" => TypeKind::Int,
                        "Uint" => TypeKind::Uint,
                        "Str" => TypeKind::Str,
                        "CStr" => TypeKind::CStr,
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
        let params = func
            .args
            .iter_mut()
            .map(|arg| {
                let kind = arg.var_type.to_type_kind(types);
                let type_id = types.alloc(kind);
                arg.type_id = Some(type_id);
                type_id
            })
            .collect();

        let fn_t = types.alloc(TypeKind::Fn {
            params,
            ret: return_t,
        });

        {
            let fn_symbol = self.resolve_mut(sym_id);
            match &mut fn_symbol.kind {
                SymbolKind::Fn {
                    fn_type_id,
                    param_type_ids,
                    return_type_id,
                } => {
                    *return_type_id = Some(return_t);
                    *fn_type_id = Some(fn_t);
                    *param_type_ids = func.args.iter().map(|arg| arg.type_id).collect();
                }
                t => unreachable!("fn_symbol should always have SymbolKind::Fn, got: {t:?}"),
            }
        }

        // also store into the AST func
        func.return_type_id = Some(return_t);

        // register function bodies (locals and expressions)
        if let Some(body) = &mut func.body {
            for statement in &mut body.statements {
                match &mut statement.kind {
                    StatementKind::Decleration {
                        symbol_id,
                        ident_id,
                        ident_token_at: _,
                        expr: _,
                    } => match self.lookup(*ident_id) {
                        Some(t) => {
                            dbg!(t);
                            todo!("duplicate definitions within the same scope: {t:?}");
                        }
                        None => {
                            *symbol_id = Some(self.declare(
                                *ident_id,
                                SymbolKind::Var {
                                    type_id: None,
                                    is_used: false,
                                    is_mutable: false,
                                },
                            ));
                        }
                    },
                    StatementKind::Assignment {
                        ident_id: _,
                        ident_token_at: _,
                        expr: _,
                    } => todo!(),
                    StatementKind::Expr(ast_expr) => {
                        self.register_expr(ast_expr);
                    }
                    StatementKind::Return(ast_expr) => {
                        self.register_expr(ast_expr);
                    }
                };
            }
        }
    }

    pub fn register_expr(&mut self, expr: &mut AstExpr) {
        match &mut expr.kind {
            ExprKind::Atom(atom) => match atom {
                Atom::Ident((ident_id, symbol_id)) => {
                    *symbol_id = self.lookup(*ident_id);
                }
                Atom::Int(_) => (),
                Atom::Str(_) => (),
                Atom::CStr(_) => (),
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
                Op::Block(_) => todo!(),
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
            VarType::Uint => TypeKind::Uint,
            VarType::Str => TypeKind::Str,
            VarType::CStr => TypeKind::CStr,
            VarType::CChar => todo!(),
            VarType::Custom(_) => todo!(),
            VarType::Ref(var_type) => TypeKind::Ref(types.var_type_to_typeid(var_type)),
        }
    }
}
