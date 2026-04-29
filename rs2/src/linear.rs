use crate::*;

use ordered_float::OrderedFloat;
type F64 = OrderedFloat<f64>;
fn f(x: f64) -> F64 { OrderedFloat(x) }

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Linear {
    factor: F64, // is never allowed to be zero!
    offset: F64
}

impl Linear {
    pub fn apply(&self, x: F64) -> F64 {
        self.factor * x + self.offset
    }
}

impl Group for Linear {
    fn identity() -> Linear {
        Linear {
            factor: f(1.0),
            offset: f(0.0),
        }
    }

    fn compose(l: &Linear, r: &Linear) -> Linear {
        Linear {
            factor: l.factor*r.factor,
            offset: l.factor*r.offset + l.offset,
        }
    }

    fn inverse(&self) -> Linear {
        Linear {
            factor: f(1.0) / self.factor,
            offset: -self.offset/self.factor,
        }
    }
}

struct ConstProp(Option<F64>);

fn is_close(x: F64, y: F64) -> bool { (x - y).abs() <= 1e-10 }

impl Semilattice for ConstProp {
    type G = Linear;

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
                assert!(is_close(x, o));
                false
            },
        }
    }

    // TODO this has notable overlap with "merge". Maybe it should just be `from_self_edge(g) -> Self`.
    // and then "merge" returning false can be used to detect contains_self_edge.
    fn insert_self_edge(&mut self, g: Self::G) {
        // a*x + b = x
        // (a-1)*x = -b
        // x = b/(1-a)
        let other = if is_close(g.factor, f(1.0)) {
            assert!(is_close(g.offset, f(0.0)));
            None
        } else {
            Some(g.offset / (f(1.0) - g.factor))
        };
        self.merge(ConstProp(other));
    }

    fn contains_self_edge(&self, g: &Self::G) -> bool {
        match *self {
            ConstProp(Some(v)) => g.apply(v) == v,
            ConstProp(None) => is_close(g.factor, f(1.0)) && is_close(g.offset, f(0.0)),
        }
    }
}

type LinearId = (Linear, Id);

#[derive(Hash, PartialEq, Eq, Clone, Copy)]
enum LinearLang {
    Add([LinearId; 2]),
    Mul([LinearId; 2]),
    Const(F64),
    Symbol(Symbol),
}

struct LinearAnalysis;

impl Analysis for LinearAnalysis {
    type G = Linear;
    type S = ConstProp;
    type L = LinearLang;

    fn canon(n: &Self::L, uf: &Unionfind<Self::S>) -> (Self::G, Self::L) {
        match n {
            LinearLang::Add([x, y]) => (Linear::identity(), LinearLang::Add([uf.find(*x), uf.find(*y)])), // TODO more canon!
            LinearLang::Mul([x, y]) => (Linear::identity(), LinearLang::Mul([uf.find(*x), uf.find(*y)])), // TODO more canon!
            LinearLang::Const(c) => (Linear { factor: f(1.0), offset: *c }, LinearLang::Const(f(0.0))),
            LinearLang::Symbol(s) => (Linear::identity(), LinearLang::Symbol(*s)),
        }
    }

    fn mk(n: &Self::L, id: Id, uf: &Unionfind<Self::S>) -> Self::S {
        match n {
            LinearLang::Add([x, y]) => todo!(),
            LinearLang::Mul([x, y]) => todo!(),
            LinearLang::Const(c) => ConstProp(Some(*c)), // TODO merge classes that have const-prop'd to 1*c so that they all get merged.
            LinearLang::Symbol(_) => ConstProp(None),
        }
    }
}

#[test]
fn lintest() {
    let l = Linear {
        factor: f(22.),
        offset: f(-4.),
    };

    assert!(Linear::compose(&l, &l.inverse()) == Linear::identity());
    assert!(Linear::compose(&l.inverse(), &l) == Linear::identity());
}
