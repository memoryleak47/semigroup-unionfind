use crate::*;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Offset(i64);

impl Group for Offset {
    fn identity() -> Offset {
        Offset(0)
    }

    fn compose(l: &Offset, r: &Offset) -> Offset {
        Offset(l.0 + r.0)
    }

    fn inverse(&self) -> Offset {
        Offset(-self.0)
    }
}

struct OffsetSemilattice;

impl Semilattice for OffsetSemilattice {
    type G = Offset;

    fn act(g: &Self::G, s: &Self) -> Self {
        OffsetSemilattice
    }

    fn merge(&mut self, other: Self) -> bool { false }

    fn insert_self_edge(&mut self, g: Self::G) {
        assert_eq!(g.0, 0);
    }

    fn contains_self_edge(&self, g: &Self::G) -> bool { *g == Offset(0) }
}

type OffsetId = (Offset, Id);

#[derive(Hash, PartialEq, Eq, Clone, Copy)]
enum OffsetLang {
    Add([OffsetId; 2]),
    Mul([OffsetId; 2]),
    Const(i64),
    Symbol(Symbol),
}

struct OffsetAnalysis;

impl Analysis for OffsetAnalysis {
    type G = Offset;
    type S = OffsetSemilattice;
    type L = OffsetLang;

    fn canon(n: &Self::L, uf: &Unionfind<Self::S>) -> (Self::G, Either<Self::L, Id>) {
        match n {
            OffsetLang::Add([x, y]) => {
                let (o1, x) = uf.find(*x);
                let (o2, y) = uf.find(*y);
                (Offset(o1.0 + o2.0), Either::L(OffsetLang::Add([(Offset(0), x), (Offset(0), y)])))
            },
            OffsetLang::Mul([x, y]) => {
                (Offset(0), Either::L(OffsetLang::Mul([uf.find(*x), uf.find(*y)])))
            },
            OffsetLang::Const(c) => (Offset(*c), Either::L(OffsetLang::Const(0))),
            OffsetLang::Symbol(s) => (Offset(0), Either::L(OffsetLang::Symbol(*s))),
        }
    }

    fn mk(n: &Self::L, id: Id, uf: &Unionfind<Self::S>) -> Self::S {
        OffsetSemilattice
    }
}
