use crate::*;

pub struct Id(usize);

pub trait Group {
    fn identity() -> Self;
    fn compose(_: Self, _: Self) -> Self;
    fn inverse(_: Self) -> Self;
}

pub trait Semilattice {
    type G: Group;

    fn act(g: Self::G, s: Self) -> Self;
    fn merge(_: Self, _: Self) -> Self;

    fn add_loop(g: Self::G, s: Self) -> Self;
    fn contains_loop(g: &Self::G, s: &Self) -> bool;
}

pub struct Unionfind<S: Semilattice> {
    v: Vec<(S::G, Id)>,
}

impl<S: Semilattice> Unionfind<S> {
    pub fn new() -> Self {
        Unionfind { v: Vec::new() }
    }
}
