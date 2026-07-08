use crate::*;

pub trait Group: Clone + Eq {
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

pub enum Either<L, R> {
    L(L),
    R(R),
}

pub trait Analysis: Sized {
    type G: Group;
    type S: Semilattice<G=Self::G>;
    type L: Eq + Hash + Clone;

    fn canon(n: &Self::L, uf: &Unionfind<Self::S>) -> (Self::G, Either<Self::L, Id>);

    // should only be called on e-nodes after they have been given `canon`.
    fn mk(n: &Self::L, id: Id, uf: &Unionfind<Self::S>) -> Self::S;

    fn reify(s: &Self::S) -> Option<Self::L> { None }

    fn children_mut(l: &mut Self::L) -> Box<[&mut (Self::G, Id)]> { todo!("children_mut unsupported!") }
    fn implied_nodes(i: Id, eg: &EGraph<Self>) -> Box<[(Self::G, Self::L)]> { Box::new([]) }
}
