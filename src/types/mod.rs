use rustc_hash::FxHashMap;

use crate::ast::VarType;

pub mod error;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeId(pub usize);

#[derive(Debug, Clone)]
pub enum TypeKind {
    Int,
    Uint,
    Str,
    CStr,
    Void,
    Bool,
    Struct {
        struct_id: usize,
        fields: Vec<(crate::interner::IdentId, TypeId)>,
    },
    Fn {
        params: Vec<TypeId>,
        ret: TypeId,
    },
    Ref(TypeId),
    Unknown,
    // Type variables are just IDs managed by union–find
    Var,
}

#[derive(Debug)]
pub struct TypeArena {
    kinds: Vec<TypeKind>,
    parent: Vec<TypeId>, // union–find parent links
    rank: Vec<u32>,      // union–find ranks for balancing
    struct_symbol_to_type: FxHashMap<usize, TypeId>,
}

#[derive(Debug)]
pub enum UnifyErrorWithoutSpan {
    Mismatch(TypeId, TypeKind, TypeId, TypeKind),
}

impl TypeArena {
    pub fn new() -> Self {
        Self {
            kinds: vec![],
            parent: Vec::new(),
            rank: Vec::new(),
            struct_symbol_to_type: FxHashMap::default(),
        }
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
            | (TypeKind::Void, TypeKind::Void) => {
                self.union(ra, rb);
                Ok(())
            }
            (TypeKind::Ref(ta), TypeKind::Ref(tb)) => self.unify(ta, tb),
            (
                TypeKind::Fn {
                    params: p1,
                    ret: r1,
                },
                TypeKind::Fn {
                    params: p2,
                    ret: r2,
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
            (TypeKind::Struct { struct_id: s1, .. }, TypeKind::Struct { struct_id: s2, .. }) => {
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

    pub fn intern_struct_symbol(&mut self, struct_symbol_index: usize) -> TypeId {
        if let Some(&t) = self.struct_symbol_to_type.get(&struct_symbol_index) {
            return t;
        }
        let id = self.alloc(TypeKind::Struct {
            struct_id: struct_symbol_index,
            fields: vec![],
        });
        self.struct_symbol_to_type.insert(struct_symbol_index, id);
        id
    }

    pub fn var_type_to_typeid(&mut self, v: &VarType) -> TypeId {
        match v {
            VarType::Void => self.alloc(TypeKind::Void),
            VarType::Int => self.alloc(TypeKind::Int),
            VarType::Uint => self.alloc(TypeKind::Uint),
            VarType::Str => self.alloc(TypeKind::Str),
            VarType::CStr => self.alloc(TypeKind::CStr),
            VarType::Ref(inner) => {
                let inner_id = self.var_type_to_typeid(inner);
                self.alloc(TypeKind::Ref(inner_id))
            }
            VarType::Custom(_) => self.alloc(TypeKind::Unknown), // TODO: resolve to struct symbol
            _ => self.alloc_var(),                               // fallback for inference
        }
    }
}
