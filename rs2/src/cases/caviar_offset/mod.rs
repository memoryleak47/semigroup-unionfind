use crate::*;

mod matching;
use matching::*;

mod testing;
use testing::*;

mod analysis;
use analysis::*;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Offset(i64);

impl Offset {
    pub fn apply(&self, x: i64) -> i64 {
        x + self.0
    }
}

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

pub struct ConstProp(Option<i64>);

impl Semilattice for ConstProp {
    type G = Offset;

    fn act(g: &Self::G, s: &Self) -> Self {
        match s {
            ConstProp(Some(x)) => ConstProp(Some(g.apply(*x))),
            ConstProp(None) => ConstProp(None),
        }
    }

    fn merge(&mut self, other: Self) -> bool {
        let ConstProp(Some(o)) = other else { return false };

        match *self {
            ConstProp(None) => {
                *self = ConstProp(Some(o));
                true
            },
            ConstProp(Some(x)) => {
                assert_eq!(x, o);
                false
            },
        }
    }

    fn insert_self_edge(&mut self, g: Self::G) {
        assert!(g == Offset(0));
    }

    fn contains_self_edge(&self, g: &Self::G) -> bool {
        *g == Offset(0)
    }
}

pub type OffsetId = (Offset, Id);

#[derive(Hash, PartialEq, Eq, Clone, Copy)]
pub enum OffsetLang {
    Add([OffsetId; 2]),
    Const(i64),

    // Symbol + App are able to express anything.
    Symbol(Symbol),
    App([OffsetId; 2]),
}
