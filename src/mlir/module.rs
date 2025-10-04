use crate::{
    interner::SharedInterner,
    mlir::{FuncId, Function, Module},
    types::TypeArena,
};
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicUsize, Ordering},
};

pub struct ModuleBuilder<'a> {
    next_func_id: AtomicUsize,
    pub module: Arc<Mutex<Module<'a>>>,
}

impl<'a> ModuleBuilder<'a> {
    pub fn new(types: &'a TypeArena, interner: SharedInterner) -> Self {
        Self {
            next_func_id: AtomicUsize::new(0),
            module: Arc::new(Mutex::new(Module {
                types,
                funcs: Vec::new(),
                interner,
            })),
        }
    }

    pub fn allocate_function(&self, f: Function) -> FuncId {
        let id = self.next_func_id.fetch_add(1, Ordering::Relaxed);
        let mut module = self.module.lock().unwrap();
        module.funcs.push(f);
        FuncId(id)
    }
}
