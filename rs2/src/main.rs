use std::collections::HashMap;

// TODO do we want interned structured eids, or nah?

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

    fn mv(_: Self, _: Self::G) -> Self;
    fn mk(_: L) -> Self;
    fn merge(_: Self, _: Self) -> Self;
}

struct EGraph<L: Language, N: Analysis<L>> {
    hashcons: HashMap<L, (N::G, Id)>,
}

impl<L: Language, N: Analysis<L>> EGraph<L, N> {
    pub fn new() -> Self {
        EGraph { hashcons: Default::default() }
    }

    pub fn add(&mut self, n: L) -> Id {
        todo!()
    }
}

fn main() {}
