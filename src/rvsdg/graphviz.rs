//! Graphviz DOT export for RVSDG visualization
//!
//! Exports RVSDG to DOT format for visualization with Graphviz tools.
//! Use: `dot -Tpng module.dot -o module.png` or `dot -Tsvg module.dot -o module.svg`

use super::*;
use crate::symbols::SymbolTable;
use std::fmt::Write;

impl<'a> Module<'a> {
    /// Export the entire module to DOT format
    pub fn to_dot(&self, symbols: &SymbolTable) -> String {
        let mut dot = String::new();

        writeln!(&mut dot, "digraph Module {{").unwrap();
        writeln!(&mut dot, "  rankdir=TB;").unwrap();
        writeln!(&mut dot, "  node [shape=box, style=rounded];").unwrap();
        writeln!(&mut dot, "  edge [fontsize=10];").unwrap();
        writeln!(&mut dot).unwrap();

        // Create a subgraph for each function
        for (i, func) in self.functions.iter().enumerate() {
            writeln!(&mut dot, "  subgraph cluster_func{} {{", i).unwrap();
            writeln!(
                &mut dot,
                "    label=\"{}\";",
                escape_dot(&symbol_name(func.name, self, symbols))
            )
            .unwrap();
            writeln!(&mut dot, "    style=filled;").unwrap();
            writeln!(&mut dot, "    color=lightgrey;").unwrap();
            writeln!(&mut dot).unwrap();

            func.to_dot(&mut dot, self, symbols, 2).unwrap();

            writeln!(&mut dot, "  }}").unwrap();
            writeln!(&mut dot).unwrap();
        }

        writeln!(&mut dot, "}}").unwrap();
        dot
    }

    /// Export a single function to DOT format
    pub fn function_to_dot(&self, func_id: FunctionId, symbols: &SymbolTable) -> Option<String> {
        let func = self.functions.get(func_id.0)?;

        let mut dot = String::new();
        writeln!(&mut dot, "digraph Function {{").unwrap();
        writeln!(&mut dot, "  rankdir=TB;").unwrap();
        writeln!(&mut dot, "  node [shape=box, style=rounded];").unwrap();
        writeln!(&mut dot, "  edge [fontsize=10];").unwrap();
        writeln!(&mut dot).unwrap();

        func.to_dot(&mut dot, self, symbols, 1).unwrap();

        writeln!(&mut dot, "}}").unwrap();
        Some(dot)
    }
}

impl Function {
    fn to_dot(
        &self,
        dot: &mut String,
        module: &Module,
        symbols: &SymbolTable,
        indent: usize,
    ) -> std::fmt::Result {
        let ind = "  ".repeat(indent);

        // Create nodes
        for node in &self.nodes {
            node.to_dot_node(dot, module, symbols, &ind)?;
        }

        writeln!(dot)?;

        // Create edges
        for node in &self.nodes {
            node.to_dot_edges(dot, &ind)?;
        }

        Ok(())
    }
}

impl Node {
    fn to_dot_node(
        &self,
        dot: &mut String,
        module: &Module,
        symbols: &SymbolTable,
        ind: &str,
    ) -> std::fmt::Result {
        let node_id = format!("n{}", self.id.0);

        // Determine node color based on type
        let (color, style) = match &self.kind {
            NodeKind::Lambda { .. } | NodeKind::Gamma { .. } | NodeKind::Theta { .. } => {
                ("lightblue", "filled,rounded")
            }
            NodeKind::Const { .. } => ("lightgreen", "filled,rounded"),
            NodeKind::Binary { .. } | NodeKind::Unary { .. } => ("lightyellow", "filled,rounded"),
            NodeKind::Call { .. } => ("orange", "filled,rounded"),
            NodeKind::Load { .. } | NodeKind::Store { .. } | NodeKind::Alloc { .. } => {
                ("pink", "filled,rounded")
            }
            NodeKind::Parameter { .. } | NodeKind::RegionParam { .. } | NodeKind::StateToken => {
                ("lightcyan", "filled,rounded")
            }
            NodeKind::RegionResult => ("lightgray", "filled,rounded"),
            _ => ("white", "rounded"),
        };

        // Build label
        let label = self.build_dot_label(module, symbols);

        writeln!(
            dot,
            "{}{}  [label=\"{}\", fillcolor={}, style=\"{}\"];",
            ind,
            node_id,
            escape_dot(&label),
            color,
            style
        )
    }

    fn build_dot_label(&self, module: &Module, symbols: &SymbolTable) -> String {
        let mut label = format!("n{}: ", self.id.0);

        match &self.kind {
            NodeKind::Lambda { region } => {
                label.push_str(&format!("λ region:{}", region.0));
            }

            NodeKind::Gamma { regions } => {
                label.push_str("γ [");
                for (i, r) in regions.iter().enumerate() {
                    if i > 0 {
                        label.push_str(", ");
                    }
                    label.push_str(&format!("r{}", r.0));
                }
                label.push(']');
            }

            NodeKind::Theta { region } => {
                label.push_str(&format!("θ region:{}", region.0));
            }

            NodeKind::Parameter { index } => {
                label.push_str(&format!("param#{}", index));
            }

            NodeKind::StateToken => {
                label.push_str("state");
            }

            NodeKind::Const { value } => {
                label.push_str("const ");
                match value {
                    ConstValue::I64(i) => label.push_str(&i.to_string()),
                    ConstValue::U64(u) => label.push_str(&format!("{}u", u)),
                    ConstValue::Bool(b) => label.push_str(&b.to_string()),
                    ConstValue::String(bytes) => {
                        // Show truncated string for graph clarity
                        label.push('"');
                        let display_bytes = if bytes.last() == Some(&0) {
                            &bytes[..bytes.len() - 1]
                        } else {
                            &bytes[..]
                        };
                        // Only show first 20 bytes to keep graph readable
                        let truncated = if display_bytes.len() > 20 {
                            &display_bytes[..20]
                        } else {
                            display_bytes
                        };
                        for &byte in truncated {
                            match byte {
                                b'\n' => label.push_str("\\n"),
                                b'\r' => label.push_str("\\r"),
                                b'\t' => label.push_str("\\t"),
                                b'\\' => label.push_str("\\\\"),
                                b'"' => label.push_str("\\\""),
                                32..=126 => label.push(byte as char),
                                _ => label.push_str(&format!("\\x{:02x}", byte)),
                            }
                        }
                        if display_bytes.len() > 20 {
                            label.push_str("...");
                        }
                        label.push('"');
                    }
                }
            }

            NodeKind::Binary { op } => {
                label.push_str(&format!("{:?}", op));
            }

            NodeKind::Unary { op } => {
                label.push_str(&format!("{:?}", op));
            }

            NodeKind::Call { function } => {
                label.push_str(&format!("call @f{}", function.0));
            }

            NodeKind::Alloc { ty } => {
                label.push_str(&format!("alloc {}", type_name(*ty, module)));
            }

            NodeKind::Load { ty } => {
                label.push_str(&format!("load {}", type_name(*ty, module)));
            }

            NodeKind::Store { ty } => {
                label.push_str(&format!("store {}", type_name(*ty, module)));
            }

            NodeKind::StructFieldAddr { field } => {
                label.push_str(&format!("&.field{}", field.0));
            }

            NodeKind::StructFieldLoad { field } => {
                label.push_str(&format!("load .field{}", field.0));
            }

            NodeKind::StructFieldStore { field } => {
                label.push_str(&format!("store .field{}", field.0));
            }

            NodeKind::RegionParam { index } => {
                label.push_str(&format!("r-param#{}", index));
            }

            NodeKind::RegionResult => {
                label.push_str("r-result");
            }
        }

        // Add type annotations
        if !self.output_types.is_empty() {
            label.push_str("\\n→ ");
            for (i, &ty) in self.output_types.iter().enumerate() {
                if i > 0 {
                    label.push_str(", ");
                }
                label.push_str(&type_name(ty, module));
            }
        }

        label
    }

    fn to_dot_edges(&self, dot: &mut String, ind: &str) -> std::fmt::Result {
        let node_id = format!("n{}", self.id.0);

        for (i, input) in self.inputs.iter().enumerate() {
            let input_id = format!("n{}", input.node.0);
            let label = if self.inputs.len() > 1 {
                format!(" [label=\"{}\"]", i)
            } else {
                String::new()
            };

            writeln!(dot, "{}{}  -> {}{};", ind, input_id, node_id, label)?;
        }

        Ok(())
    }
}

// Helper functions

fn symbol_name(symbol_id: SymbolId, module: &Module, symbols: &SymbolTable) -> String {
    let symbol = symbols.resolve(symbol_id);
    let interner = module.interner.read();
    interner.resolve(symbol.ident_id).to_string()
}

fn type_name(type_id: TypeId, module: &Module) -> String {
    use crate::types::TypeKind;

    match module.types.kind(type_id) {
        TypeKind::Int => "i32".to_string(),
        TypeKind::Uint => "u32".to_string(),
        TypeKind::Bool => "bool".to_string(),
        TypeKind::Void => "void".to_string(),
        TypeKind::Str => "str".to_string(),
        TypeKind::CStr => "cstr".to_string(),
        TypeKind::Ref(inner) => format!("&{}", type_name(*inner, module)),
        TypeKind::Struct(id) => format!("S{}", id.0),
        TypeKind::Fn { .. } => "fn".to_string(),
        TypeKind::Unknown => "?".to_string(),
        TypeKind::Var => "T".to_string(),
    }
}

fn escape_dot(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
}
