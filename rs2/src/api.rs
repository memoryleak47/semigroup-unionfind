use crate::*;

pub trait Group: Clone {
    fn identity() -> Self;

    // We typically left-multiply stuff with G, so `g*_`.
    // composition is compatible with that order, so that `g1*(g2*x) = (g1*g2)*x = compose(g1, g2)*x`.
    fn compose(_: &Self, _: &Self) -> Self;

    fn inverse(&self) -> Self;
}

// Note: This Semilattice encodes a subgroup of G.
// After all, self-edges are closed under composition and inversion.
pub trait Semilattice {
    type G: Group;

    fn act(g: &Self::G, s: &Self) -> Self;
    fn merge(&mut self, _: Self) -> bool; // returns whether "self" was changed.

    fn insert_self_edge(&mut self, g: Self::G);
    fn contains_self_edge(&self, g: &Self::G) -> bool;
}

pub trait Analysis {
    type G: Group;
    type S: Semilattice<G=Self::G>;
    type L: Eq + Hash;

    fn canon(n: &Self::L, uf: &Unionfind<Self::S>) -> (Self::G, Self::L);

    // should only be called on e-nodes after they have been given `canon`.
    fn mk(n: &Self::L, id: Id, uf: &Unionfind<Self::S>) -> Self::S;
}
