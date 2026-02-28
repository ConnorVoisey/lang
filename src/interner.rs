use parking_lot::RwLock;
use rustc_hash::FxHashMap;
use std::sync::Arc;

pub type SharedInterner = Arc<RwLock<Interner>>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct IdentId(pub usize);

#[derive(Debug)]
pub struct Interner {
    map: FxHashMap<&'static str, IdentId>,
    vec: Vec<Box<str>>,
}

impl Interner {
    pub fn new() -> Self {
        Self {
            map: FxHashMap::default(),
            vec: vec![],
        }
    }
    pub fn lookup_ident(&mut self, ident: &str) -> IdentId {
        if let Some(&id) = self.map.get(ident) {
            id
        } else {
            let id = IdentId(self.vec.len());
            let boxed: Box<str> = ident.to_owned().into_boxed_str();
            let static_ref: &'static str = Box::leak(boxed);
            self.vec.push(Box::from(static_ref));
            self.map.insert(static_ref, id);
            id
        }
    }

    pub fn resolve(&self, id: IdentId) -> &str {
        &self.vec[id.0]
    }
}
