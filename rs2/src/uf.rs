use crate::*;

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub struct Id(usize);

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
        let i = self.next_id();
        self.v.push(UFClass {
            s,
            leader: (S::G::identity(), i),
        });
        i
    }

    pub fn next_id(&self) -> Id {
        Id(self.v.len())
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

    pub fn merge_s(&mut self, (g, x): (S::G, Id), s: S) -> bool {
        let s = S::act(&g.inverse(), &s);
        self.v[x.0].s.merge(s)
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

    pub fn get_leader_semilattice(&self, x: Id) -> &S {
        assert_eq!(self.v[x.0].leader.1, x);
        &self.v[x.0].s
    }

    pub fn is_equal(&self, x1: (S::G, Id), x2: (S::G, Id)) -> bool {
        let (g1, x1) = self.find(x1);
        let (g2, x2) = self.find(x2);
        if x1 != x2 { return false }
        let g = S::G::compose(&g1.inverse(), &g2);
        self.v[x1.0].s.contains_self_edge(&g)
    }

    pub fn get_g_between(&self, x1: (S::G, Id), x2: (S::G, Id)) -> Option<S::G> {
        let (g1, x1) = self.find(x1);
        let (g2, x2) = self.find(x2);
        if x1 != x2 { return None }
        let g = S::G::compose(&g1.inverse(), &g2);
        Some(g)
    }
}
