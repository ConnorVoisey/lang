use crate::{
    ast::Ast, cl_export::CLExporter, error::CompliationError, interner::SharedInterner,
    lexer::Lexer, symbols::SymbolTable, type_checker::TypeChecker, types::TypeArena,
};
use std::{fs::read_to_string, process::Command};
use target_lexicon::Triple;

pub mod ast;
pub mod cl_export;
pub mod error;
pub mod interner;
pub mod lexer;
pub mod mlir;
pub mod symbols;
pub mod type_checker;
pub mod types;

#[derive(Debug)]
pub struct ModParser {}
impl ModParser {
    pub fn parse_file(
        file_path: &str,
        interner: &SharedInterner,
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
        let mut type_arena = TypeArena::new();
        symbols.register_ast(&mut ast, &mut type_arena);

        let mut type_checker = TypeChecker::new(&mut type_arena, &mut symbols);
        type_checker.check_ast(&mut ast);
        if !type_checker.errors.is_empty() {
            return Err(CompliationError::TypeCheckingError(type_checker.errors));
        }

        dbg!(&ast.fns[0]);
        let mut cl_export = CLExporter::new(
            interner.clone(),
            Triple::host(),
            true,
            &ast,
            &type_arena,
            &mut symbols,
        );
        cl_export.cl_compile().unwrap();

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
