use crate::*;

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub struct Id(usize);

pub trait Group: Clone {
    fn identity() -> Self;

    // We typically left-multiply stuff with G, so `g*_`.
    // composition is compatible with that order, so that `g1*(g2*x) = (g1*g2)*x = compose(g1, g2)*x`.
    fn compose(_: &Self, _: &Self) -> Self;

    fn inverse(&self) -> Self;
}

pub trait Semilattice {
    type G: Group;

    fn act(g: &Self::G, s: &Self) -> Self;
    fn merge(&mut self, _: Self);

    fn insert_self_edge(&mut self, g: Self::G);
    fn contains_self_edge(&self, g: &Self::G) -> bool;
}

struct UFClass<S: Semilattice> {
    s: S,
    leader: (S::G, Id),
}

// NOTE: For now, we don't intern structured e-ids.
// Maybe later?
// It would require a g_hashcons: Map<(G, Id), Id>, as otherwise shapes would be non-unique.
// Further, a "hash"-cons isn't enough if two different G are effectively equal due to certain redundancies/symmetries.
// Thus we'd need a `canon_g(G, S) -> G` function that canonicalizes g*s to g'*s for some s: S. This (g*) we can then use for g_hashconsing.
pub struct Unionfind<S: Semilattice> {
    v: Vec<UFClass<S>>,
}

impl<S: Semilattice> Unionfind<S> {
    pub fn new() -> Self {
        Unionfind { v: Vec::new() }
    }

    pub fn makeset(&mut self, s: S) -> Id {
        let i = Id(self.v.len());
        self.v.push(UFClass {
            s,
            leader: (S::G::identity(), i),
        });
        i
    }

    pub fn find1(&self, x: Id) -> (S::G, Id) {
        let (g, x) = &self.v[x.0].leader;
        self.find((g.clone(), *x)) // potentially unnecessary clone!
    }

    pub fn find(&self, (mut g, mut x): (S::G, Id)) -> (S::G, Id) {
        loop {
            let (g2, x2) = &self.v[x.0].leader;
            if *x2 == x { return (g, x) }

            // we want to return g*x where g2*x2 = x.
            (g, x) = (S::G::compose(&g, g2), *x2);
        }
    }

    pub fn union(&mut self, x1: (S::G, Id), x2: (S::G, Id)) -> bool {
        let (g1, x1) = self.find(x1);
        let (g2, x2) = self.find(x2);

        // g1*x1 = g2*x2
        // x1 = g1⁻¹*g2*x2
        let gg = S::G::compose(&g1.inverse(), &g2);
        // x1 = gg * x2

        if x1 == x2 {
            if !self.v[x1.0].s.contains_self_edge(&gg) {
                self.v[x1.0].s.insert_self_edge(gg);
                true
            } else { false }
        } else {
            let acted = S::act(&gg.inverse(), &self.v[x1.0].s); // gg⁻¹*x1
            self.v[x2.0].s.merge(acted);
            self.v[x1.0].leader = (gg, x2);
            true
        }
    }

    pub fn get_semilattice(&self, gx: &(S::G, Id)) -> S {
        let (g, x) = gx;
        let (g, x) = self.find((g.clone(), *x));
        S::act(&g, &self.v[x.0].s)
    }
}
