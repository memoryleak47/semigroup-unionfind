use crate::*;

pub trait Analysis {
    type G: Group;
    type S: Semilattice<G=Self::G>;
    type L: Eq + Hash;

    fn canon(n: &Self::L, uf: &Unionfind<Self::S>) -> (Self::G, Self::L);

    // should only be called on e-nodes after they have been given `canon`.
    fn mk(n: &Self::L, uf: &Unionfind<Self::S>) -> Self::S;
}

pub struct EGraph<N: Analysis> {
    hashcons: HashMap<N::L, (N::G, Id)>,
    uf: Unionfind<N::S>,
}

impl<N: Analysis> EGraph<N> {
    pub fn new() -> Self {
        EGraph {
            hashcons: Default::default(),
            uf: Unionfind::new(),
        }
    }

    pub fn add(&mut self, n: &N::L) -> (N::G, Id) {
        let (g, n2) = N::canon(n, &self.uf);
        if let Some((g2, x)) = self.hashcons.get(&n2) {
            // n == g*n2
            // n2 == g2*x
            // -> n == g*g2*x
            (N::G::compose(&g, &g2), *x)
        } else {
            let s = N::mk(&n2, &self.uf);
            let x = self.uf.makeset(s);
            self.hashcons.insert(n2, (N::G::identity(), x));
            (g, x)
        }
    }

    pub fn union(&mut self, x: (N::G, Id), y: (N::G, Id)) {
        self.uf.union(x, y);
        self.rebuild();
    }

    fn rebuild(&mut self) {
        loop {
            let mut dirty = false;
            for (n, (g, x)) in std::mem::take(&mut self.hashcons) {
                // n == g*x
                let (g2, n2) = N::canon(&n, &self.uf);
                // n == g2*n2
                // -> g*x = g2*n2
                // -> n2 = g2⁻¹*g*x
                let gn = N::G::compose(&g2.inverse(), &g);
                // -> n2 = gn*x

                let s = N::mk(&n2, &self.uf);
                dirty |= self.uf.merge_s((gn.clone(), x), s);

                if let Some((g3, x3)) = self.hashcons.get(&n2) {
                    dirty |= self.uf.union((g3.clone(), *x3), (gn, x));
                } else {
                    self.hashcons.insert(n2, (gn, x));
                }
            }
            if !dirty { break }
        }
    }
}
