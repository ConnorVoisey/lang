use super::*;
use crate::{
    interner::{Interner, SharedInterner},
    lexer::Lexer,
};
use parking_lot::RwLock;

mod arithmetic;
mod arrays;
mod comparisons;
mod control_flow;
mod functions;
mod integration;
mod operators;
mod returns;
mod structs;
mod variables;

pub struct TypeCheckTestCase {
    arena: TypeArena,
    symbols: SymbolTable,
    ast: Ast,
}

impl TypeCheckTestCase {
    pub fn from_source(src: &str) -> Self {
        let interner = SharedInterner::new(RwLock::new(Interner::new()));
        let mut symbols = SymbolTable::new(interner.clone());

        let lexer = Lexer::from_src_str(src, &interner).unwrap();
        let mut ast = Ast::from_tokens(lexer.tokens, interner.clone(), &mut symbols).unwrap();

        let mut arena = TypeArena::new();
        symbols.register_ast(&mut ast, &mut arena);

        Self {
            arena,
            symbols,
            ast,
        }
    }

    pub fn check(mut self) -> Vec<TypeCheckingError> {
        let mut checker = TypeChecker::new(&mut self.arena, &mut self.symbols);
        checker.check_ast(&mut self.ast);
        checker.errors
    }
}

pub trait CheckErrs {
    fn assert_no_errors(&self);

    fn assert_error_count(&self, count: usize);

    fn assert_has_error<F>(&self, predicate: F)
    where
        F: Fn(&TypeCheckingError) -> bool;
}
impl CheckErrs for Vec<TypeCheckingError> {
    fn assert_no_errors(&self) {
        assert!(self.is_empty(), "Expected no errors, got: {:?}", self);
    }

    fn assert_error_count(&self, count: usize) {
        assert_eq!(self.len(), count);
    }

    fn assert_has_error<F>(&self, predicate: F)
    where
        F: Fn(&TypeCheckingError) -> bool,
    {
        assert!(
            self.iter().any(predicate),
            "No matching error found in: {:?}",
            self
        );
    }
}
