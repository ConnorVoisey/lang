use crate::{
    ast::VarType,
    interner::IdentId,
    symbols::{SymbolId, SymbolKind, SymbolTable},
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeId(pub usize);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct StructId(pub usize);

#[derive(Debug, Clone)]
pub enum TypeKind {
    Int,
    Uint,
    Str,
    CStr,
    Void,
    Bool,
    Struct(StructId),
    Fn {
        params: Vec<TypeId>,
        param_symbols: Vec<SymbolId>,
        ret: TypeId,
    },
    Ref(TypeId),
    Unknown,
    // Type variables are just IDs managed by union–find
    Var,
}

#[derive(Debug, Clone)]
pub struct TypeKindStruct {
    pub struct_id: StructId,
    pub fields: Vec<(crate::interner::IdentId, TypeId)>,
}

#[derive(Debug)]
pub struct TypeArena {
    pub kinds: Vec<TypeKind>,
    parent: Vec<TypeId>, // union–find parent links
    rank: Vec<u32>,      // union–find ranks for balancing
    pub struct_symbol_to_type: Vec<Option<TypeId>>,
    pub struct_field_types: Vec<Vec<(IdentId, TypeId)>>,

    // Cached primitive types
    pub int_type: TypeId,
    pub uint_type: TypeId,
    pub bool_type: TypeId,
    pub str_type: TypeId,
    pub cstr_type: TypeId,
    pub void_type: TypeId,
}

#[derive(Debug)]
pub enum UnifyErrorWithoutSpan {
    Mismatch(TypeId, TypeKind, TypeId, TypeKind),
}

impl TypeArena {
    pub fn new() -> Self {
        let mut arena = Self {
            kinds: vec![],
            parent: Vec::new(),
            rank: Vec::new(),
            struct_symbol_to_type: Vec::new(),
            struct_field_types: Vec::new(),
            // Initialize with dummy values, will be set below
            int_type: TypeId(0),
            uint_type: TypeId(0),
            bool_type: TypeId(0),
            str_type: TypeId(0),
            cstr_type: TypeId(0),
            void_type: TypeId(0),
        };

        // Allocate primitive types once
        arena.int_type = arena.make(TypeKind::Int);
        arena.uint_type = arena.make(TypeKind::Uint);
        arena.bool_type = arena.make(TypeKind::Bool);
        arena.str_type = arena.make(TypeKind::Str);
        arena.cstr_type = arena.make(TypeKind::CStr);
        arena.void_type = arena.make(TypeKind::Void);

        arena
    }

    fn make(&mut self, kind: TypeKind) -> TypeId {
        let id = TypeId(self.kinds.len());
        self.kinds.push(kind);
        self.parent.push(id); // initially parent is itself
        self.rank.push(0);
        id
    }

    pub fn alloc(&mut self, kind: TypeKind) -> TypeId {
        self.make(kind)
    }

    pub fn alloc_var(&mut self) -> TypeId {
        self.make(TypeKind::Var)
    }

    /// Find with path compression
    pub fn find(&mut self, t: TypeId) -> TypeId {
        let mut root = t;
        while self.parent[root.0] != root {
            root = self.parent[root.0];
        }
        // Path compression
        let mut node = t;
        while self.parent[node.0] != root {
            let next = self.parent[node.0];
            self.parent[node.0] = root;
            node = next;
        }
        root
    }

    pub fn kind(&self, t: TypeId) -> &TypeKind {
        &self.kinds[t.0]
    }

    pub fn kind_mut(&mut self, t: TypeId) -> &mut TypeKind {
        &mut self.kinds[t.0]
    }

    fn union(&mut self, a: TypeId, b: TypeId) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return;
        }
        let rank_a = self.rank[ra.0];
        let rank_b = self.rank[rb.0];
        if rank_a < rank_b {
            self.parent[ra.0] = rb;
        } else if rank_a > rank_b {
            self.parent[rb.0] = ra;
        } else {
            self.parent[rb.0] = ra;
            self.rank[ra.0] += 1;
        }
    }

    /// Unify two types
    pub fn unify(&mut self, a: TypeId, b: TypeId) -> Result<(), UnifyErrorWithoutSpan> {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return Ok(());
        }

        match (self.kinds[ra.0].clone(), self.kinds[rb.0].clone()) {
            (TypeKind::Var, _) => {
                self.union(ra, rb);
                Ok(())
            }
            (_, TypeKind::Var) => {
                self.union(rb, ra);
                Ok(())
            }
            (TypeKind::Int, TypeKind::Int)
            | (TypeKind::Uint, TypeKind::Uint)
            | (TypeKind::Str, TypeKind::Str)
            | (TypeKind::CStr, TypeKind::CStr)
            | (TypeKind::Bool, TypeKind::Bool)
            | (TypeKind::Void, TypeKind::Void) => {
                self.union(ra, rb);
                Ok(())
            }
            (TypeKind::Ref(ta), TypeKind::Ref(tb)) => self.unify(ta, tb),
            (
                TypeKind::Fn {
                    params: p1,
                    ret: r1,
                    ..
                },
                TypeKind::Fn {
                    params: p2,
                    ret: r2,
                    ..
                },
            ) => {
                if p1.len() != p2.len() {
                    return Err(UnifyErrorWithoutSpan::Mismatch(
                        ra,
                        self.kinds[ra.0].clone(),
                        rb,
                        self.kinds[rb.0].clone(),
                    ));
                }
                self.union(ra, rb);
                for (x, y) in p1.into_iter().zip(p2.into_iter()) {
                    self.unify(x, y)?;
                }
                self.unify(r1, r2)
            }
            (TypeKind::Struct(s1), TypeKind::Struct(s2)) => {
                if s1 != s2 {
                    return Err(UnifyErrorWithoutSpan::Mismatch(
                        ra,
                        self.kinds[ra.0].clone(),
                        rb,
                        self.kinds[rb.0].clone(),
                    ));
                }
                self.union(ra, rb);
                Ok(())
            }
            (ka, kb) => Err(UnifyErrorWithoutSpan::Mismatch(ra, ka, rb, kb)),
        }
    }

    pub fn intern_struct_symbol(&mut self, struct_id: StructId) -> TypeId {
        // Ensure vec is large enough
        if struct_id.0 >= self.struct_symbol_to_type.len() {
            self.struct_symbol_to_type.resize(struct_id.0 + 1, None);
        }

        // Return existing TypeId if already interned
        if let Some(type_id) = self.struct_symbol_to_type[struct_id.0] {
            return type_id;
        }

        // Create new TypeId for this struct
        let type_id = self.alloc(TypeKind::Struct(struct_id));
        self.struct_symbol_to_type[struct_id.0] = Some(type_id);
        type_id
    }

    pub fn var_type_to_typeid(&mut self, v: &VarType, symbols: &SymbolTable) -> TypeId {
        match v {
            VarType::Void => self.alloc(TypeKind::Void),
            VarType::Int => self.alloc(TypeKind::Int),
            VarType::Uint => self.alloc(TypeKind::Uint),
            VarType::Str => self.alloc(TypeKind::Str),
            VarType::CStr => self.alloc(TypeKind::CStr),
            VarType::Bool => self.alloc(TypeKind::Bool),
            VarType::Ref(inner) => {
                let inner_id = self.var_type_to_typeid(inner, symbols);
                self.alloc(TypeKind::Ref(inner_id))
            }
            VarType::Custom((_, symbol_id)) => match symbol_id {
                Some(symbol_id) => {
                    let symbol = symbols.resolve(*symbol_id);
                    let kind = match &symbol.kind {
                        SymbolKind::Fn(_) => TypeKind::Fn {
                            params: todo!(),
                            param_symbols: todo!(),
                            ret: todo!(),
                        },
                        SymbolKind::FnArg(_) => todo!(),
                        SymbolKind::Var(_) => todo!(),
                        SymbolKind::Struct(struct_data) => TypeKind::Struct(struct_data.struct_id),
                    };
                    self.alloc(kind)
                }
                None => self.alloc(TypeKind::Unknown),
            },

            VarType::CChar => todo!(),
        }
    }
    pub fn kind_to_string(&self, kind: &TypeKind) -> String {
        match kind {
            TypeKind::Int => "Int".to_string(),
            TypeKind::Uint => "Uint".to_string(),
            TypeKind::Str => "Str".to_string(),
            TypeKind::CStr => "CStr".to_string(),
            TypeKind::Void => "Void".to_string(),
            TypeKind::Bool => "Bool".to_string(),
            TypeKind::Struct(struct_id) => format!("Struct {}", struct_id.0),
            TypeKind::Fn { .. } => "Fn".to_string(),
            TypeKind::Ref(type_id) => format!("&{}", self.kind_to_string(self.kind(*type_id))),
            TypeKind::Unknown => "Unknown".to_string(),
            TypeKind::Var => "Var".to_string(),
        }
    }

    pub fn id_to_string(&self, type_id: TypeId) -> String {
        self.kind_to_string(self.kind(type_id))
    }

    pub fn get_struct_fields(&self, struct_id: StructId) -> &Vec<(IdentId, TypeId)> {
        &self.struct_field_types[struct_id.0]
    }

    pub fn set_struct_fields(&mut self, struct_id: StructId, fields: Vec<(IdentId, TypeId)>) {
        self.struct_field_types.insert(struct_id.0, fields);
    }
}
