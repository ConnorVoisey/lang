use crate::{
    ast::Ast, cl_export::CLExporter, error::CompliationError, interner::SharedInterner,
    lexer::Lexer, rvsdg::lower::AstLowering, struct_layout::StructLayoutInfo, symbols::SymbolTable,
    type_checker::TypeChecker, types::TypeArena,
};
use std::{fs::read_to_string, process::Command};
use target_lexicon::Triple;

pub mod ast;
pub mod cl_export;
pub mod error;
pub mod interner;
pub mod lexer;
pub mod rvsdg;
pub mod struct_layout;
pub mod symbols;
pub mod type_checker;
pub mod types;

#[derive(Debug)]
pub struct ModParser {}

/// Configuration for the compiler pipeline
pub struct CompilerConfig {
    /// Use RVSDG IR layer (true) or go directly to Cranelift (false)
    pub use_rvsdg: bool,
    /// Print IR to stdout and files
    pub print_ir: bool,
    /// Dump RVSDG to files (textual and DOT format)
    pub dump_rvsdg: bool,
}

impl Default for CompilerConfig {
    fn default() -> Self {
        Self {
            use_rvsdg: true, // Default to using RVSDG
            print_ir: true,
            dump_rvsdg: true, // Default to dumping RVSDG for debugging
        }
    }
}

impl ModParser {
    pub fn parse_file(
        file_path: &str,
        interner: &SharedInterner,
    ) -> Result<ModParser, CompliationError> {
        Self::parse_file_with_config(file_path, interner, CompilerConfig::default())
    }

    pub fn parse_file_with_config(
        file_path: &str,
        interner: &SharedInterner,
        config: CompilerConfig,
    ) -> Result<ModParser, CompliationError> {
        let src = match read_to_string(file_path) {
            Ok(v) => v,
            Err(e) => return Err(CompliationError::LexingError(vec![e.into()])),
        };
        let lexer = Lexer::from_src_str(&src, interner)?;
        if !lexer.errs.is_empty() {
            return Err(CompliationError::LexingError(lexer.errs));
        }
        let mut symbols = SymbolTable::new(interner.clone());
        let mut ast = Ast::from_tokens(lexer.tokens, interner.clone(), &mut symbols)?;
        if !ast.errs.is_empty() {
            return Err(CompliationError::AstParseError(ast.errs));
        }
        // dbg!(&ast);
        let mut type_arena = TypeArena::new();
        symbols.register_ast(&mut ast, &mut type_arena);

        let mut type_checker = TypeChecker::new(&mut type_arena, &mut symbols);
        type_checker.check_ast(&mut ast);
        if !type_checker.errors.is_empty() {
            return Err(CompliationError::TypeCheckingError(type_checker.errors));
        }
        let struct_layouts = StructLayoutInfo::new(&type_arena).compute_struct_layout();

        if config.use_rvsdg {
            // RVSDG pipeline: AST -> RVSDG -> Cranelift
            let lowering = AstLowering::new(&ast, &type_arena, &symbols, interner.clone());
            let rvsdg_module = lowering.lower_module();

            println!(
                "RVSDG module created with {} functions",
                rvsdg_module.functions.len()
            );

            // Dump RVSDG if requested
            if config.dump_rvsdg {
                use std::fs;
                use std::io::Write;

                fs::create_dir_all("./lang_tmp").ok();

                // Dump textual format
                let text = rvsdg_module.display(&symbols);
                if let Ok(mut file) = std::fs::File::create("./lang_tmp/rvsdg.txt") {
                    file.write_all(text.as_bytes()).ok();
                    println!("RVSDG textual format written to: lang_tmp/rvsdg.txt");
                }

                // Dump DOT format
                let dot = rvsdg_module.to_dot(&symbols);
                if let Ok(mut file) = std::fs::File::create("./lang_tmp/rvsdg.dot") {
                    file.write_all(dot.as_bytes()).ok();
                    println!("RVSDG DOT format written to: lang_tmp/rvsdg.dot");
                    println!("  View with: dot -Tpng lang_tmp/rvsdg.dot -o lang_tmp/rvsdg.png");
                    println!("  Or online: https://dreampuf.github.io/GraphvizOnline/");
                }
            }

            // TODO: Compile RVSDG to Cranelift
            // For now, fall back to direct compilation
            println!(
                "Note: RVSDG->Cranelift compilation not yet fully implemented, falling back to direct compilation"
            );

            let mut cl_export = CLExporter::new(
                interner.clone(),
                Triple::host(),
                config.print_ir,
                &ast,
                &type_arena,
                &mut symbols,
                struct_layouts,
            );
            cl_export.cl_compile().unwrap();
        } else {
            // Direct pipeline: AST -> Cranelift
            let mut cl_export = CLExporter::new(
                interner.clone(),
                Triple::host(),
                config.print_ir,
                &ast,
                &type_arena,
                &mut symbols,
                struct_layouts,
            );
            cl_export.cl_compile().unwrap();
        }

        let mut cc_comand = Command::new("tcc");
        cc_comand.arg("lang_tmp/out.o").args(["-o", "out"]);

        match cc_comand.output() {
            Ok(_) => (),
            Err(e) => {
                dbg!(e);
                panic!();
            }
        };
        let mod_parser = ModParser {};

        Ok(mod_parser)
    }
}
