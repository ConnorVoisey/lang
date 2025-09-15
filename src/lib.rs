use crate::{
    ast::Ast, error::CompliationError, interner::SharedInterner, lexer::Lexer,
    symbols::SymbolTable, type_checker::TypeChecker, types::TypeArena,
};
use std::fs::read_to_string;

pub mod ast;
pub mod error;
pub mod interner;
pub mod lexer;
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

        let mut type_checker = TypeChecker::new(&mut type_arena, &symbols);
        type_checker.check_ast(&mut ast);
        if !type_checker.errors.is_empty() {
            return Err(CompliationError::TypeCheckingError(type_checker.errors));
        }
        let mod_parser = ModParser {};

        Ok(mod_parser)
    }
}
