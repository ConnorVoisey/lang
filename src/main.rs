use lang::{
    ModParser,
    interner::{Interner, SharedInterner},
};
use parking_lot::lock_api::RwLock;
use std::fs::read_to_string;

fn main() {
    let file_path = "examples/hello.lang";
    let src_code = &read_to_string(file_path).unwrap();
    let interner = Interner::new();
    let shared_interner = SharedInterner::new(RwLock::new(interner));
    let mod_parser = match ModParser::parse_file(file_path, &shared_interner) {
        Ok(v) => v,
        Err(e) => {
            e.display_error(src_code, file_path);
            return;
        }
    };
    dbg!(mod_parser);
}
