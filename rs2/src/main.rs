use std::collections::HashMap;

mod slotted;

type Id = usize;

trait Language {
}

trait Group {
    fn identity() -> Self;
    fn compose(_: Self, _: Self) -> Self;
    fn inverse(_: Self) -> Self;
}

trait Analysis<L: Language> {
    type G: Group;

    fn canon(n: &L) -> (Self::G, L);
    fn mv(_: Self, _: Self::G) -> Self;
    fn mk(_: L) -> Self;
    fn merge(_: Self, _: Self) -> Self;
}

struct EGraph<L: Language, N: Analysis<L>> {
    hashcons: HashMap<L, (N::G, Id)>,

    g_hashcons: HashMap<(N::G, Id), Id>,
    uf: HashMap<Id, (N::G, Id)>
}

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    pub fn new() -> Self {
        EGraph {
            hashcons: Default::default(),
            g_hashcons: Default::default(),
            uf: Default::default(),
        }
    }

    pub fn add(&mut self, n: &L) -> Id {
        let (g, n) = N::canon(n);
        todo!()
    }
}

fn main() {}
