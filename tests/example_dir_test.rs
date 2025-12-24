use lang::{
    ModParser,
    error::CompliationError,
    interner::{Interner, SharedInterner},
};
use parking_lot::RwLock;

// Compile each example in the examples directory, check that each example compiles successfully.

fn compile_example(path: &str) -> Result<ModParser, CompliationError> {
    let interner = Interner::new();
    let shared_interner = SharedInterner::new(RwLock::new(interner));
    ModParser::parse_file(path, &shared_interner)
}

#[test]
fn compile_example_add() {
    compile_example("./examples/add.lang").unwrap();
}
#[test]
fn compile_example_cat() {
    compile_example("./examples/cat.lang").unwrap();
}
#[test]
fn compile_example_fib() {
    compile_example("./examples/fib.lang").unwrap();
}
#[test]
fn compile_example_fn_add() {
    compile_example("./examples/fn_add.lang").unwrap();
}
#[test]
fn compile_example_hello() {
    compile_example("./examples/hello.lang").unwrap();
}
#[test]
fn compile_example_while() {
    compile_example("./examples/while.lang").unwrap();
}
#[test]
fn compile_example_yes() {
    compile_example("./examples/yes.lang").unwrap();
}
