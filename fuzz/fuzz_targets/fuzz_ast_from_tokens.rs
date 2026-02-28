#![no_main]

use arbitrary::{Arbitrary, Unstructured};
use lang::ast::Ast;
use lang::symbols::SymbolTable;
use lang_fuzz::{setup_interner, FuzzToken};
use libfuzzer_sys::fuzz_target;
use std::sync::LazyLock;

static INTERNER: LazyLock<lang::interner::SharedInterner> = LazyLock::new(setup_interner);

fuzz_target!(|data: &[u8]| {
    let mut u = Unstructured::new(data);

    let token_count: usize = match u.int_in_range(0..=200) {
        Ok(n) => n,
        Err(_) => return,
    };

    let mut tokens = Vec::with_capacity(token_count);
    for _ in 0..token_count {
        match FuzzToken::arbitrary(&mut u) {
            Ok(ft) => tokens.push(ft.0),
            Err(_) => break,
        }
    }

    let interner = INTERNER.clone();
    let mut symbols = SymbolTable::new(interner.clone());

    let _ = Ast::from_tokens(tokens, interner, &mut symbols);
});
