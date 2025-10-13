use crate::{
    interner::IdentId,
    struct_layout::dfs::{StructWithChild, TopologicalSortResult, topological_sort},
    types::{StructId, TypeArena, TypeId, TypeKind, TypeKindStruct},
};
use rustc_hash::FxHashSet;

pub mod dfs;

#[derive(Debug, Clone)]
pub struct StructField {
    pub size: usize,
    pub offset: usize,
    pub ident_id: IdentId,
    pub type_id: TypeId,
}
#[derive(Debug, Clone)]
pub struct StructLayout {
    pub struct_id: StructId,
    pub size: usize,
    pub alignment: usize,
    pub fields: Vec<StructField>,
    pub child_struct_ids: FxHashSet<StructId>,
}

#[derive(Debug)]
pub struct StructLayoutInfo<'a> {
    layouts: Vec<Option<StructLayout>>,
    types: &'a TypeArena,
}

impl<'a> StructLayoutInfo<'a> {
    pub fn new(types: &'a TypeArena) -> Self {
        Self {
            layouts: vec![],
            types,
        }
    }

    pub fn compute_struct_layout(&mut self) -> Vec<StructLayout> {
        // We need to get the childs of all the structs, so if a struct is used directly (not by
        // reference) than it is a parent of that struct
        let struct_iter = self.types.kinds.iter().filter_map(|t| match t {
            TypeKind::Struct(type_kind_struct) => Some(type_kind_struct),
            _ => None,
        });
        let mut structs_with_child = vec![];
        for struct_id in struct_iter {
            let mut child_ids = FxHashSet::default();
            for field in self.types.get_struct_fields(*struct_id).iter() {
                let type_kind = self.types.kind(field.1);
                if let TypeKind::Struct(struct_id) = type_kind {
                    child_ids.insert(*struct_id);
                }
            }
            structs_with_child.push(StructWithChild {
                struct_id: *struct_id,
                child_ids,
            });
        }
        let top_sort_res = topological_sort(&structs_with_child);

        let sorted_struct_ids = match top_sort_res {
            TopologicalSortResult::Success(struct_ids) => struct_ids,
            TopologicalSortResult::Cycle {
                sorted: _,
                cycle_nodes: _,
            } => todo!("handled cyclic struct diagnostics"),
        };

        for struct_id in sorted_struct_ids.iter() {
            let s_type_id = self.types.struct_symbol_to_type[struct_id.0].unwrap();
            let struct_id = match self.types.kind(s_type_id) {
                TypeKind::Struct(struct_id) => *struct_id,
                _ => unreachable!("struct symbol should have a type of struct"),
            };

            self.compute_layout(struct_id);
        }

        // TODO: remove this clone, consider if this needs to be an option to begin with
        self.layouts.iter().filter_map(|s| s.clone()).collect()
    }

    pub fn compute_layout(&mut self, struct_id: StructId) {
        let field_types = self.types.get_struct_fields(struct_id);
        let mut fields = Vec::with_capacity(field_types.len());
        let mut offset = 0;
        let mut struct_alignment = 1;

        for (field_ident_id, field_type_id) in field_types.iter() {
            let (field_size, field_align) = self.size_and_align_of_type(*field_type_id);
            struct_alignment = struct_alignment.max(field_align);
            offset = align_to(offset, field_align);

            fields.push(StructField {
                size: field_size,
                offset,
                ident_id: *field_ident_id,
                type_id: *field_type_id,
            });

            offset += field_size;
        }

        let total_size = align_to(offset, struct_alignment);

        self.set_layout(StructLayout {
            struct_id,
            size: total_size,
            alignment: struct_alignment,
            fields,
            child_struct_ids: FxHashSet::default(),
        });
    }

    fn size_and_align_of_type(&self, type_id: TypeId) -> (usize, usize) {
        use crate::types::TypeKind;

        let type_kind = self.types.kind(type_id);
        match type_kind {
            TypeKind::Int => (4, 4),    // i32
            TypeKind::Uint => (4, 4),   // u32
            TypeKind::Bool => (1, 1),   // i8/bool
            TypeKind::Void => (0, 1),   // void has no size
            TypeKind::CStr => (8, 8),   // pointer to C string
            TypeKind::Str => (16, 8), // fat pointer (ptr + len) - adjust based on your implementation
            TypeKind::Ref(_) => (8, 8), // reference/pointer
            TypeKind::Struct(struct_id) => {
                let layout = self
                    .get(*struct_id)
                    .expect("Struct layout must be computed before use, should have been covered in topological sort");
                (layout.size, layout.alignment)
            }
            TypeKind::Fn { .. } => (8, 8), // function pointer
            TypeKind::Unknown => {
                panic!("Cannot compute size of Unknown - should be resolved by type checker")
            }
            TypeKind::Var => {
                panic!("Cannot compute size of Var type - should be resolved by type checker")
            }
        }
    }

    pub fn set_layout(&mut self, layout: StructLayout) {
        let struct_id = layout.struct_id;
        if struct_id.0 >= self.layouts.len() {
            self.layouts.resize(struct_id.0 + 1, None);
        }
        self.layouts[struct_id.0] = Some(layout);
    }

    pub fn get(&self, struct_id: StructId) -> Option<&StructLayout> {
        self.layouts.get(struct_id.0).and_then(|opt| opt.as_ref())
    }

    pub fn get_mut(&mut self, struct_id: StructId) -> Option<&mut StructLayout> {
        self.layouts
            .get_mut(struct_id.0)
            .and_then(|opt| opt.as_mut())
    }
}

fn align_to(offset: usize, align: usize) -> usize {
    (offset + align - 1) & !(align - 1)
}
