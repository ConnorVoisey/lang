use crate::{
    interner::IdentId,
    symbols::{SymbolId, SymbolTable},
    types::{StructId, TypeArena, TypeId, TypeKindStruct},
};

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
    pub symbol_id: SymbolId,
    pub size: usize,
    pub alignment: usize,
    pub fields: Vec<StructField>,
}

#[derive(Debug)]
pub struct StructLayoutInfo<'a> {
    layouts: Vec<Option<StructLayout>>,
    symbols: &'a SymbolTable,
    types: &'a TypeArena,
}

impl<'a> StructLayoutInfo<'a> {
    pub fn new(symbols: &'a SymbolTable, types: &'a TypeArena) -> Self {
        Self {
            layouts: Vec::new(),
            symbols,
            types,
        }
    }

    pub fn check_recursive_structs(&mut self) {
        // TODO: implement this, use topological sort, return errors somewhere
    }

    pub fn compute_layout(&mut self, type_kind_struct: &TypeKindStruct, symbol_id: SymbolId) {
        let mut fields = Vec::with_capacity(type_kind_struct.fields.len());
        let mut offset = 0usize;
        let mut struct_alignment = 1usize;

        for (field_ident_id, field_type_id) in &type_kind_struct.fields {
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
            struct_id: type_kind_struct.struct_id,
            symbol_id,
            size: total_size,
            alignment: struct_alignment,
            fields,
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
            TypeKind::Struct(TypeKindStruct { struct_id, .. }) => {
                let layout = self
                    .get(*struct_id)
                    .expect("Struct layout must be computed before use, should have been covered in topological sort");
                (layout.size, layout.alignment)
            }
            TypeKind::Fn { .. } => (8, 8), // function pointer
            TypeKind::Unknown | TypeKind::Var => {
                panic!(
                    "Cannot compute size of Unknown/Var type - should be resolved by type checker"
                )
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
