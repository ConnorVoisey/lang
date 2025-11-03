//! Textual display format for RVSDG
//!
//! Similar to Cranelift's .clif format, this provides a human-readable
//! textual representation of the RVSDG for debugging and inspection.

use super::*;
use crate::symbols::SymbolTable;
use std::fmt::{self, Write};

impl<'a> Module<'a> {
    /// Format the entire module as text
    #[tracing::instrument(skip(self, symbols))]
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
            write!(out, "{}", value_name(func, self.id, 0))?;
            for i in 1..self.output_types.len() {
                write!(out, ", {}", value_name(func, self.id, i))?;
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
                self.display_inputs(out, func)?;
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
                self.display_inputs(out, func)?;
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
                self.display_inputs(out, func)?;
                writeln!(out)?;
            }

            NodeKind::Unary { op } => {
                write!(out, "{:?} ", op)?;
                self.display_inputs(out, func)?;
                writeln!(out)?;
            }

            NodeKind::Call { function } => {
                // Get the function name from the module
                let func_name = if let Some(f) = module.functions.iter().find(|f| f.id == *function)
                {
                    symbol_name(f.name, module, symbols)
                } else if let Some(ext) = module.extern_functions.iter().find(|f| f.id == *function)
                {
                    symbol_name(ext.name, module, symbols)
                } else {
                    format!("func{}", function.0)
                };
                write!(out, "call {} [id:{}] ", func_name, function.0)?;
                self.display_inputs(out, func)?;
                writeln!(out)?;
            }

            NodeKind::Alloc { ty } => {
                write!(out, "alloc {} ", type_name(*ty, module))?;
                self.display_inputs(out, func)?;
                writeln!(out)?;
            }

            NodeKind::Load { ty } => {
                write!(out, "load {} ", type_name(*ty, module))?;
                self.display_inputs(out, func)?;
                writeln!(out)?;
            }

            NodeKind::Store { ty } => {
                write!(out, "store {} ", type_name(*ty, module))?;
                self.display_inputs(out, func)?;
                writeln!(out)?;
            }

            NodeKind::StructFieldAddr { field } => {
                write!(out, "struct_field_addr .field{} ", field.0)?;
                self.display_inputs(out, func)?;
                writeln!(out)?;
            }

            NodeKind::StructFieldLoad { field } => {
                write!(out, "struct_field_load .field{} ", field.0)?;
                self.display_inputs(out, func)?;
                writeln!(out)?;
            }

            NodeKind::StructFieldStore { field } => {
                write!(out, "struct_field_store .field{} ", field.0)?;
                self.display_inputs(out, func)?;
                writeln!(out)?;
            }

            NodeKind::RegionParam { index } => {
                writeln!(out, "region_param #{}", index)?;
            }

            NodeKind::RegionResult => {
                let region_id = func
                    .regions
                    .iter()
                    .find(|r| r.results.contains(&self.id))
                    .map(|r| r.id);

                if let Some(rid) = region_id {
                    write!(out, "region_result:{} ", rid.0)?;
                } else {
                    write!(out, "region_result ")?;
                }

                self.display_inputs(out, func)?;
                writeln!(out)?;
            }
        }

        Ok(())
    }

    fn display_inputs(&self, out: &mut String, func: &Function) -> fmt::Result {
        write!(out, "(")?;
        for (i, input) in self.inputs.iter().enumerate() {
            if i > 0 {
                write!(out, ", ")?;
            }
            write!(
                out,
                "{}",
                value_name(func, input.node, input.output_index as usize)
            )?;
        }
        write!(out, ")")
    }
}

// Helper functions

/// Generate a value name with type prefix based on node kind
fn value_name(func: &Function, node_id: NodeId, output_index: usize) -> String {
    let node = func.node(node_id);
    let id = node_id.0;

    let prefix = match &node.kind {
        NodeKind::StateToken => "s",
        NodeKind::Lambda { .. } => "lam",
        NodeKind::Gamma { .. } => "g",
        NodeKind::Theta { .. } => "th",
        NodeKind::Parameter { .. } => "p",
        NodeKind::Const { .. } => "c",
        NodeKind::Binary { op } => match op {
            BinaryOp::Add => "add",
            BinaryOp::Sub => "sub",
            BinaryOp::Mul => "mul",
            BinaryOp::Div => "div",
            BinaryOp::Rem => "rem",
            BinaryOp::Eq => "eq",
            BinaryOp::Ne => "ne",
            BinaryOp::Lt => "lt",
            BinaryOp::Le => "le",
            BinaryOp::Gt => "gt",
            BinaryOp::Ge => "ge",
            BinaryOp::And => "and",
            BinaryOp::Or => "or",
        },
        NodeKind::Unary { op } => match op {
            UnaryOp::Neg => "neg",
            UnaryOp::Not => "not",
        },
        NodeKind::Call { .. } => "call",
        NodeKind::Alloc { .. } => "alloc",
        NodeKind::Load { .. } => "load",
        NodeKind::Store { .. } => "store",
        NodeKind::StructFieldAddr { .. } => "faddr",
        NodeKind::StructFieldLoad { .. } => "fload",
        NodeKind::StructFieldStore { .. } => "fstore",
        NodeKind::RegionParam { .. } => "rp",
        NodeKind::RegionResult => "rr",
    };

    if output_index == 0 {
        format!("{}{}", prefix, id)
    } else {
        format!("{}{}_{}", prefix, id, output_index)
    }
}

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

#[inline]
fn type_name(type_id: TypeId, module: &Module) -> String {
    module.types.id_to_debug_string(type_id)
}
