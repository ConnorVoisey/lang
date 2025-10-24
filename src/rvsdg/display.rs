//! Textual display format for RVSDG
//!
//! Similar to Cranelift's .clif format, this provides a human-readable
//! textual representation of the RVSDG for debugging and inspection.

use super::*;
use crate::{symbols::SymbolTable, types::TypeKind};
use std::fmt::{self, Write};

impl<'a> Module<'a> {
    /// Format the entire module as text
    pub fn display(&self, symbols: &SymbolTable) -> String {
        let mut out = String::new();

        writeln!(&mut out, "; RVSDG Module").unwrap();
        writeln!(
            &mut out,
            "; {} functions, {} extern functions\n",
            self.functions.len(),
            self.extern_functions.len()
        )
        .unwrap();

        // Display extern functions
        for ext_fn in &self.extern_functions {
            ext_fn.display(&mut out, self, symbols).unwrap();
            writeln!(&mut out).unwrap();
        }

        // Display functions
        for func in &self.functions {
            func.display(&mut out, self, symbols).unwrap();
            writeln!(&mut out).unwrap();
        }

        out
    }
}

impl ExternFunction {
    fn display(&self, out: &mut String, module: &Module, symbols: &SymbolTable) -> fmt::Result {
        let name = symbol_name(self.name, module, symbols);

        write!(out, "extern fn {}(", name)?;

        for (i, &param_ty) in self.param_types.iter().enumerate() {
            if i > 0 {
                write!(out, ", ")?;
            }
            write!(out, "{}", type_name(param_ty, module))?;
        }

        write!(out, ") -> {}", type_name(self.return_type, module))
    }
}

impl Function {
    fn display(&self, out: &mut String, module: &Module, symbols: &SymbolTable) -> fmt::Result {
        let name = symbol_name(self.name, module, symbols);
        let export = if self.is_exported { "export " } else { "" };
        let inline = match self.inline_hint {
            InlineHint::Always => " [inline]",
            InlineHint::Never => " [noinline]",
            InlineHint::Auto => "",
        };

        write!(out, "{}fn {}{} [id:{}](", export, name, inline, self.id.0)?;

        // Parameters (inline, compact format)
        for (i, param) in self.params.iter().enumerate() {
            if i > 0 {
                write!(out, ", ")?;
            }
            let param_name = symbol_name(param.name, module, symbols);
            write!(out, "{}: {}", param_name, type_name(param.ty, module))?;
        }

        writeln!(out, ") -> {} {{", type_name(self.return_type, module))?;

        // Display only the root node (which recursively displays regions)
        let root_node = self.node(self.root);
        root_node.display(out, self, module, symbols, 1)?;

        writeln!(out, "}}")
    }
}

impl Node {
    fn display(
        &self,
        out: &mut String,
        func: &Function,
        module: &Module,
        symbols: &SymbolTable,
        indent: usize,
    ) -> fmt::Result {
        let ind = "  ".repeat(indent);

        // Node header with outputs
        write!(out, "{}", ind)?;

        if !self.output_types.is_empty() {
            write!(out, "v{}", self.id.0)?;
            for i in 1..self.output_types.len() {
                write!(out, ", v{}_{}", self.id.0, i)?;
            }
            write!(out, " = ")?;
        }

        // Node kind
        match &self.kind {
            NodeKind::Lambda { region } => {
                writeln!(out, "lambda region:{} {{", region.0)?;
                display_region(out, func, *region, module, symbols, indent + 1)?;
                writeln!(out, "{}}}", ind)?;
            }

            NodeKind::Gamma { regions } => {
                write!(out, "gamma ")?;
                self.display_inputs(out)?;
                writeln!(out, " {{")?;

                for (i, &region_id) in regions.iter().enumerate() {
                    let region_indent = "  ".repeat(indent + 1);

                    // Add branch labels for binary gamma (if/else)
                    if regions.len() == 2 {
                        writeln!(
                            out,
                            "{}region:{} {{  // {} branch",
                            region_indent,
                            region_id.0,
                            if i == 0 { "true" } else { "false" }
                        )?;
                    } else {
                        writeln!(out, "{}region:{} {{", region_indent, region_id.0)?;
                    }

                    display_region(out, func, region_id, module, symbols, indent + 2)?;
                    writeln!(out, "{}}}", region_indent)?;
                }

                writeln!(out, "{}}}", ind)?;
            }

            NodeKind::Theta { region } => {
                write!(out, "theta ")?;
                self.display_inputs(out)?;
                writeln!(out, " region:{} {{", region.0)?;
                display_region(out, func, *region, module, symbols, indent + 1)?;
                writeln!(out, "{}}}", ind)?;
            }

            NodeKind::Parameter { index } => {
                writeln!(out, "param #{}", index)?;
            }

            NodeKind::StateToken => {
                writeln!(out, "state_token")?;
            }

            NodeKind::Const { value } => {
                write!(out, "const ")?;
                match value {
                    ConstValue::I32(i) => writeln!(out, "{}", i)?,
                    ConstValue::U32(u) => writeln!(out, "{}u", u)?,
                    ConstValue::Bool(b) => writeln!(out, "{}", b)?,
                    ConstValue::String(bytes) => {
                        // Display as escaped string, omit trailing null terminator
                        write!(out, "\"")?;
                        let display_bytes = if bytes.last() == Some(&0) {
                            &bytes[..bytes.len() - 1]
                        } else {
                            &bytes[..]
                        };
                        for &byte in display_bytes {
                            match byte {
                                b'\n' => write!(out, "\\n")?,
                                b'\r' => write!(out, "\\r")?,
                                b'\t' => write!(out, "\\t")?,
                                b'\\' => write!(out, "\\\\")?,
                                b'"' => write!(out, "\\\"")?,
                                32..=126 => write!(out, "{}", byte as char)?,
                                _ => write!(out, "\\x{:02x}", byte)?,
                            }
                        }
                        writeln!(out, "\"")?;
                    }
                }
            }

            NodeKind::Binary { op } => {
                write!(out, "{:?} ", op)?;
                self.display_inputs(out)?;
                writeln!(out)?;
            }

            NodeKind::Unary { op } => {
                write!(out, "{:?} ", op)?;
                self.display_inputs(out)?;
                writeln!(out)?;
            }

            NodeKind::Call { function } => {
                write!(out, "call @func{} ", function.0)?;
                self.display_inputs(out)?;
                writeln!(out)?;
            }

            NodeKind::Alloc { ty } => {
                write!(out, "alloc {} ", type_name(*ty, module))?;
                self.display_inputs(out)?;
                writeln!(out)?;
            }

            NodeKind::Load { ty } => {
                write!(out, "load {} ", type_name(*ty, module))?;
                self.display_inputs(out)?;
                writeln!(out)?;
            }

            NodeKind::Store { ty } => {
                write!(out, "store {} ", type_name(*ty, module))?;
                self.display_inputs(out)?;
                writeln!(out)?;
            }

            NodeKind::StructFieldAddr { field } => {
                write!(out, "struct_field_addr .field{} ", field.0)?;
                self.display_inputs(out)?;
                writeln!(out)?;
            }

            NodeKind::StructFieldLoad { field } => {
                write!(out, "struct_field_load .field{} ", field.0)?;
                self.display_inputs(out)?;
                writeln!(out)?;
            }

            NodeKind::StructFieldStore { field } => {
                write!(out, "struct_field_store .field{} ", field.0)?;
                self.display_inputs(out)?;
                writeln!(out)?;
            }

            NodeKind::RegionParam { index } => {
                writeln!(out, "region_param #{}", index)?;
            }

            NodeKind::RegionResult => {
                write!(out, "region_result ")?;
                self.display_inputs(out)?;
                writeln!(out)?;
            }
        }

        Ok(())
    }

    fn display_inputs(&self, out: &mut String) -> fmt::Result {
        write!(out, "(")?;
        for (i, input) in self.inputs.iter().enumerate() {
            if i > 0 {
                write!(out, ", ")?;
            }
            if input.output_index == 0 {
                write!(out, "v{}", input.node.0)?;
            } else {
                write!(out, "v{}_{}", input.node.0, input.output_index)?;
            }
        }
        write!(out, ")")
    }
}

// Helper functions

/// Display the contents of a region
fn display_region(
    out: &mut String,
    func: &Function,
    region_id: RegionId,
    module: &Module,
    symbols: &SymbolTable,
    indent: usize,
) -> fmt::Result {
    let region = func.region(region_id);

    // Display region parameters if any
    if !region.params.is_empty() {
        let ind = "  ".repeat(indent);
        write!(out, "{}; region params: ", ind)?;
        for (i, &param_node_id) in region.params.iter().enumerate() {
            if i > 0 {
                write!(out, ", ")?;
            }
            let param_node = func.node(param_node_id);
            if !param_node.output_types.is_empty() {
                write!(
                    out,
                    "%{}: {}",
                    i,
                    type_name(param_node.output_types[0], module)
                )?;
            } else {
                write!(out, "%{}", i)?;
            }
        }
        writeln!(out)?;
    }

    // Check if region is empty
    if region.nodes.is_empty() {
        let ind = "  ".repeat(indent);
        writeln!(out, "{}; (empty)", ind)?;
        return Ok(());
    }

    // Display nodes in this region
    for &node_id in &region.nodes {
        let node = func.node(node_id);
        node.display(out, func, module, symbols, indent)?;
    }

    Ok(())
}

fn symbol_name(symbol_id: SymbolId, module: &Module, symbols: &SymbolTable) -> String {
    let symbol = symbols.resolve(symbol_id);
    let interner = module.interner.read();
    interner.resolve(symbol.ident_id).to_string()
}

fn type_name(type_id: TypeId, module: &Module) -> String {
    type_kind_to_name(module.types.kind(type_id), module)
}

// TODO: this function is incredibly similar to graphiz.rs
fn type_kind_to_name(type_kind: &TypeKind, module: &Module) -> String {
    match type_kind {
        TypeKind::Int => "i32".to_string(),
        TypeKind::Uint => "u32".to_string(),
        TypeKind::Bool => "bool".to_string(),
        TypeKind::Void => "void".to_string(),
        TypeKind::Str => "str".to_string(),
        TypeKind::CStr => "cstr".to_string(),
        TypeKind::Ref(inner) => format!("&{}", type_name(*inner, module)),
        TypeKind::Struct(id) => format!("struct#{}", id.0),
        TypeKind::Fn { params, ret, .. } => {
            let param_str: Vec<_> = params.iter().map(|&p| type_name(p, module)).collect();
            format!(
                "fn({}) -> {}",
                param_str.join(", "),
                type_name(*ret, module)
            )
        }
        TypeKind::Array { size, inner_type } => {
            format!("[{}; {}]", type_kind_to_name(inner_type, module), size)
        }
        TypeKind::Unknown => "?".to_string(),
        TypeKind::Var => "T".to_string(),
    }
}
