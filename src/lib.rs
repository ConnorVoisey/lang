use crate::{
    ast::Ast,
    error::CompliationError,
    interner::SharedInterner,
    lexer::Lexer,
    rvsdg::{lower::AstLowering, to_cranelift::RvsdgToCranelift},
    struct_layout::StructLayoutInfo,
    symbols::SymbolTable,
    type_checker::TypeChecker,
    types::TypeArena,
};
use std::{
    fs::{self, File, read_to_string},
    path::PathBuf,
    process::Command,
};
use target_lexicon::Triple;

pub mod ast;
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

        // Create Cranelift object module (matching cl_export settings)
        use cranelift_codegen::{
            isa,
            settings::{self, Configurable},
        };
        use cranelift_object::{ObjectBuilder, ObjectModule};

        let mut shared_builder = settings::builder();
        shared_builder.enable("is_pic").unwrap();
        shared_builder.set("opt_level", "speed").unwrap();
        let shared_flags = settings::Flags::new(shared_builder);

        let isa_builder = isa::lookup(Triple::host()).unwrap();
        let isa = isa_builder.finish(shared_flags).unwrap();
        let call_conv = isa.default_call_conv();

        let obj_builder =
            ObjectBuilder::new(isa, "main", cranelift_module::default_libcall_names()).unwrap();
        let mut cl_module = ObjectModule::new(obj_builder);

        // Compile RVSDG to Cranelift
        let rvsdg_to_cl = RvsdgToCranelift::new(&rvsdg_module, &symbols, &struct_layouts);
        rvsdg_to_cl
            .compile(&mut cl_module, call_conv)
            .expect("RVSDG to Cranelift compilation failed");

        // Finalize and write object file
        fs::create_dir_all("./lang_tmp").ok();
        let obj_product = cl_module.finish();
        let output = PathBuf::from("./lang_tmp/out.o");
        let mut file = File::create(output).unwrap();
        obj_product.object.write_stream(&mut file).unwrap();

        if config.print_ir {
            println!("\n=== RVSDG->Cranelift compilation complete ===");
            println!("Object file written to: lang_tmp/out.o");
        }

        let mut cc_comand = Command::new("tcc");
        cc_comand.arg("lang_tmp/out.o").args(["-o", "out"]);

        match cc_comand.output() {
            Ok(output) => {
                if !output.status.success() {
                    eprintln!("TCC linking failed with status: {}", output.status);
                    eprintln!("=== TCC stdout ===");
                    eprintln!("{}", String::from_utf8_lossy(&output.stdout));
                    eprintln!("=== TCC stderr ===");
                    eprintln!("{}", String::from_utf8_lossy(&output.stderr));
                    panic!();
                }
            }
            Err(e) => {
                eprintln!("Failed to execute TCC: {}", e);
                return Err(CompliationError::LexingError(vec![e.into()]));
            }
        };
        let mod_parser = ModParser {};

        Ok(mod_parser)
    }
}
