use std::collections::{HashMap, HashSet};
use std::hash::Hash;

mod uf;
pub use uf::*;

mod slotted;
pub use slotted::*;

trait Language: Eq + Hash {
}

trait Analysis<L: Language> {
    type G: Group;
    type S: Semilattice<G=Self::G>;

    fn canon(n: &L, uf: &Unionfind<Self::S>) -> (Self::G, L);
    fn mk(n: &L) -> Self::S;
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

    pub fn add(&mut self, n: &L) -> (N::G, Id) {
        let (g, n2) = N::canon(n, &self.uf);
        if let Some((g2, x)) = self.hashcons.get(&n2) {
            // n == g*n2
            // n2 == g2*x
            // -> n == g*g2*x
            (N::G::compose(&g, &g2), *x)
        } else {
            let s = N::mk(&n2);
            let x = self.uf.makeset(s);
            self.hashcons.insert(n2, (N::G::identity(), x));
            (g, x)
        }
    }

    pub fn union(&mut self, x: (N::G, Id), y: (N::G, Id)) {
        self.uf.union(x, y)
        // TODO rebuild
    }
}

fn main() {}
