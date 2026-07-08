use crate::*;

pub struct EGraph<N: Analysis> {
    pub hashcons: HashMap<N::L, (N::G, Id)>,
    pub uf: Unionfind<N::S>,
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
        let n2 = match n2 {
            Either::L(n2) => n2,
            Either::R(ii) => return (g, ii),
        };
        if let Some((g2, x)) = self.hashcons.get(&n2) {
            // n == g*n2
            // n2 == g2*x
            // -> n == g*g2*x
            (N::G::compose(&g, &g2), *x)
        } else {
            let s = N::mk(&n2, self.uf.next_id(), &self.uf);
            let x = self.uf.makeset(s);
            self.hashcons.insert(n2, (N::G::identity(), x));
            (g, x)
        }
    }

    pub fn lookup(&self, n: &N::L) -> Option<(N::G, Id)> {
        let (g, n2) = N::canon(n, &self.uf);
        let n2 = match n2 {
            Either::L(n2) => n2,
            Either::R(ii) => return Some((g, ii)),
        };
        let (g2, x) = self.hashcons.get(&n2)?;
        // n == g*n2
        // n2 == g2*x
        // -> n == g*g2*x
        Some((N::G::compose(&g, &g2), *x))
    }

    pub fn lookup_term(&self, t: &Term<N>) -> Option<(N::G, Id)> {
        match t {
            Pattern::PVar(_) => panic!("lookup_term called on pattern with pvar!"),
            Pattern::Node(n, children) => {
                let mut n = n.clone();
                for (ptr, child) in N::children_mut(&mut n).into_iter().zip(children) {
                    *ptr = self.lookup_term(child)?;
                }
                self.lookup(&n)
            },
        }
    }

    pub fn union(&mut self, x: (N::G, Id), y: (N::G, Id)) {
        self.uf.union(x, y);
        self.rebuild();
    }

    pub fn rebuild(&mut self) {
        loop {
            let mut dirty = false;

            for x in self.classes() {
                let s = self.uf.get_leader_semilattice(x);
                if let Some(n) = N::reify(s) {
                    let x2 = self.add(&n);
                    dirty |= self.uf.union(x2, (N::G::identity(), x));
                }
            }

            'hcloop: for (n, (g, x)) in std::mem::take(&mut self.hashcons) {
                let (g, x) = self.find((g, x));
                // n == g*x
                let (g2, n2) = N::canon(&n, &self.uf);
                let n2 = match n2 {
                    Either::L(n2) => n2,
                    Either::R(ii) => {
                        dirty |= self.uf.union((g2, ii), (g, x));
                        continue 'hcloop;
                    },
                };
                // n == g2*n2
                // -> g*x = g2*n2
                // -> n2 = g2⁻¹*g*x
                let gn = N::G::compose(&g2.inverse(), &g);
                // -> n2 = gn*x

                let s = N::mk(&n2, x, &self.uf);
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

    pub fn is_equal(&self, x: (N::G, Id), y: (N::G, Id)) -> bool {
        self.uf.is_equal(x, y)
    }

    pub fn find(&self, x: (N::G, Id)) -> (N::G, Id) {
        self.uf.find(x)
    }

    pub fn get_g_between(&self, x1: (N::G, Id), x2: (N::G, Id)) -> Option<N::G> {
        self.uf.get_g_between(x1, x2)
    }

    pub fn nodes_of(&self, (g, x): (N::G, Id)) -> Box<[(N::G, N::L)]> {
        self.nodes_of_bare(x).into_iter().map(|(g2, n)| (N::G::compose(&g, &g2), n)).collect()
    }

    pub fn nodes_of_bare(&self, x: Id) -> Box<[(N::G, N::L)]> {
        // x has to be a leader.
        assert!(self.find((N::G::identity(), x)).1 == x);

        let it1 = self.hashcons.iter().filter_map(|(n, (g, i))| {
            if *i == x {
                Some((g.inverse(), n.clone()))
            } else { None }
        });

        let it2 = N::implied_nodes(x, self).into_iter();

        it1.chain(it2).collect()
    }

    pub fn classes(&self) -> Box<[Id]> {
        self.uf.classes()
    }

    pub fn dump(&self) where N::S: Debug, N::G: Debug, N::L: Debug {
        self.uf.dump();
        for (n, i) in &self.hashcons {
            println!("hc: {n:?} -> {i:?}");
        }
    }

    pub fn get_semilattice(&self, x: &(N::G, Id)) -> N::S {
        self.uf.get_semilattice(x)
    }

    pub fn get_leader_semilattice(&self, x: Id) -> &N::S {
        self.uf.get_leader_semilattice(x)
    }
}
