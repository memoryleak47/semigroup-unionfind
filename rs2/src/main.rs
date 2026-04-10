use std::collections::HashMap;

mod uf;
pub use uf::*;

mod slotted;
pub use slotted::*;

trait Language {
}

trait Analysis<L: Language> {
    type G: Group;
    type S: Semilattice<G=Self::G>;

    fn canon(n: &L) -> (Self::G, L);
    fn mk(_: L) -> Self::S;
}

struct EGraph<L: Language, N: Analysis<L>> {
    hashcons: HashMap<L, (N::G, Id)>,
    uf: Unionfind<N::S>,
}

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    pub fn new() -> Self {
        EGraph {
            hashcons: Default::default(),
            uf: Unionfind::new(),
        }
    }

    pub fn add(&mut self, n: &L) -> Id {
        let (g, n) = N::canon(n);
        todo!()
    }
}

fn main() {}
