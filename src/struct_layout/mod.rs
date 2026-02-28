use crate::{
    interner::IdentId,
    struct_layout::{
        dfs::{StructWithChild, TopologicalSortResult, topological_sort_rev},
        error::StructLayoutError,
    },
    symbols::SymbolTable,
    types::{StructId, TypeArena, TypeId, TypeKind},
};
use rustc_hash::FxHashSet;

pub mod dfs;
pub mod error;

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
    pub layouts: Vec<Option<StructLayout>>,
    pub types: &'a TypeArena,
    pub symbols: &'a SymbolTable,
}

impl<'a> StructLayoutInfo<'a> {
    pub fn new(types: &'a TypeArena, symbols: &'a SymbolTable) -> Self {
        Self {
            layouts: vec![],
            types,
            symbols,
        }
    }

    pub fn compute_struct_layout(&mut self) -> Result<Vec<StructLayout>, Vec<StructLayoutError>> {
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
        let top_sort_res = topological_sort_rev(&structs_with_child);

        let sorted_struct_ids = match top_sort_res {
            TopologicalSortResult::Success(struct_ids) => struct_ids,
            TopologicalSortResult::Cycle {
                sorted: _,
                cycle_nodes,
            } => {
                let struct_spans: Vec<_> = cycle_nodes
                    .iter()
                    .filter_map(|struct_id| self.symbols.get_struct_span(*struct_id))
                    .collect();
                return Err(vec![StructLayoutError::CyclicDependency { struct_spans }]);
            }
        };

        let mut errors = vec![];
        for struct_id in sorted_struct_ids.iter() {
            let s_type_id = self.types.struct_symbol_to_type[struct_id.0].unwrap();
            let struct_id = match self.types.kind(s_type_id) {
                TypeKind::Struct(struct_id) => *struct_id,
                _ => unreachable!("struct symbol should have a type of struct"),
            };

            if let Err(err) = self.compute_layout(struct_id) {
                errors.push(err);
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }

        // TODO: remove this clone, consider if this needs to be an option to begin with
        Ok(self.layouts.iter().filter_map(|s| s.clone()).collect())
    }

    pub fn compute_layout(&mut self, struct_id: StructId) -> Result<(), StructLayoutError> {
        let field_types = self.types.get_struct_fields(struct_id);
        let mut fields = Vec::with_capacity(field_types.len());
        let mut offset = 0;
        let mut struct_alignment = 1;

        for (field_ident_id, field_type_id) in field_types.iter() {
            let (field_size, field_align) = self.size_and_align_of_type(*field_type_id)?;
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
        Ok(())
    }

    pub fn size_and_align_of_type(
        &self,
        type_id: TypeId,
    ) -> Result<(usize, usize), StructLayoutError> {
        use crate::types::TypeKind;

        let type_kind = self.types.kind(type_id);
        match type_kind {
            TypeKind::IntLiteral(_) | TypeKind::I32 | TypeKind::U32 => Ok((4, 4)),
            TypeKind::U8 => Ok((1, 1)),
            TypeKind::U64 => Ok((8, 8)),
            TypeKind::Bool => Ok((1, 1)),
            TypeKind::Void => Ok((0, 1)),
            TypeKind::CStr => Ok((8, 8)),
            TypeKind::Str => Ok((16, 8)),
            TypeKind::Ref(_) => Ok((8, 8)),
            TypeKind::Struct(struct_id) => {
                let layout = self.get(*struct_id).ok_or_else(|| {
                    StructLayoutError::InternalError {
                        description: format!(
                            "Struct layout for StructId({}) was not computed before use",
                            struct_id.0
                        ),
                    }
                })?;
                Ok((layout.size, layout.alignment))
            }
            TypeKind::Enum(_enum_id) => {
                Err(StructLayoutError::InternalError {
                    description: "Enum types as struct fields are not yet supported for layout computation".to_string(),
                })
            }
            TypeKind::Fn { .. } => Ok((8, 8)),
            TypeKind::Unknown => Err(StructLayoutError::InternalError {
                description: "Cannot compute size of Unknown type - should have been resolved by type checker".to_string(),
            }),
            TypeKind::Become => Err(StructLayoutError::InternalError {
                description: "Cannot compute size of Become type - should have been resolved by type checker".to_string(),
            }),
            TypeKind::Var => Err(StructLayoutError::InternalError {
                description: "Cannot compute size of Var type - should have been resolved by type checker".to_string(),
            }),
            TypeKind::State => Err(StructLayoutError::InternalError {
                description: "Cannot compute size of State type - should not appear in struct layout".to_string(),
            }),
            TypeKind::Array { size, inner_type } => {
                let (elem_size, elem_align) = self.size_and_align_of_type(*inner_type)?;
                Ok((elem_size * size, elem_align))
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
