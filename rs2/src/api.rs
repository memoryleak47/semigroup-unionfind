use crate::*;

// We don't really require this to be a group, the name is historic.
// We require compose to be associative, and we require (a*b)⁻¹ = b⁻¹*a⁻¹, and I guess a*a⁻¹*a = a.
// not super sure, let's determine what we need from the code.
// Why do we even have an identity?
pub trait Group: Clone + Eq + Debug + Hash + PartialEq {
    // We typically left-multiply stuff with G, so `g*_`.
    // composition is compatible with that order, so that `g1*(g2*x) = (g1*g2)*x = compose(g1, g2)*x`.
    fn compose(_: &Self, _: &Self) -> Self;

    fn inverse(&self) -> Self;
    fn identity() -> Self; // unused!
}

// Note: This Semilattice encodes a subgroup of G.
// After all, self-edges are closed under composition and inversion.
pub trait Semilattice: Clone + Debug {
    type G: Group;

    fn act(g: &Self::G, s: &Self) -> Self;
    fn merge(&mut self, _: Self) -> bool; // returns whether "self" was changed.

    fn insert_self_edge(&mut self, g: Self::G);
    fn contains_self_edge(&self, g: &Self::G) -> bool;

    fn local_identity(&self) -> Self::G { todo!() }
    fn coset(g: &Self::G, s: &Self) -> Self::G { todo!() }
}

#[derive(PartialEq, Eq, Debug, Clone)]
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

    // child_strings as Box<[String]> is the worst thing you could do performance-wise. But printing perf doesn't matter rn.
    fn prettyprint(l: &Self::L, child_strings: Box<[String]>) -> String { format!("<can't prettyprint>") }

    // returns whether those are equal up to some G, excluding children.
    fn matches(n1: &Self::L, n2: &Self::L) -> bool {
        let nil = (Self::G::identity(), Id(0));
        let mut n1 = n1.clone();
        let mut n2 = n2.clone();
        for x in Self::children_mut(&mut n1) { *x = nil.clone(); }
        for x in Self::children_mut(&mut n2) { *x = nil.clone(); }
        n1 == n2
    }
    fn ematch(eg: &EGraph<Self>, id: Id, pat: &Pattern<Self>) -> Vec<Subst<Self>> { todo!("ematch unsupported!") }

    // if you have g*x, where s is the semilattice of x, then you can simplify it to g'*x, where g' = coset(g, s).
    fn coset(g: &Self::G, s: &Self::S) -> Self::G { todo!() }
}
