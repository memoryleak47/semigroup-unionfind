use crate::*;

#[derive(Clone, PartialEq)]
struct Linear {
    factor: f64,
    offset: f64
}

impl Linear {
    pub fn apply(&self, x: f64) -> f64 {
        self.factor * x + self.offset
    }
}

impl Group for Linear {
    fn identity() -> Linear {
        Linear {
            factor: 1.0,
            offset: 0.0,
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
            factor: 1.0 / self.factor,
            offset: -self.offset/self.factor,
        }
    }
}

struct ConstProp(Option<f64>);

fn is_close(x: f64, y: f64) -> bool { (x - y).abs() <= 1e-10 }

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
        let other = if is_close(g.factor, 1.0) {
            None
        } else {
            Some(g.offset / (1.0 - g.factor - 1.0))
        };
        self.merge(ConstProp(other));
    }

    fn contains_self_edge(&self, g: &Self::G) -> bool {
        match *self {
            ConstProp(Some(v)) => g.apply(v) == v,
            ConstProp(None) => is_close(g.factor, 1.0) && is_close(g.offset, 0.0),
        }
    }
}

#[test]
fn lintest() {
    let l = Linear {
        factor: 22.,
        offset: -4.,
    };

    assert!(Linear::compose(&l, &l.inverse()) == Linear::identity());
    assert!(Linear::compose(&l.inverse(), &l) == Linear::identity());
}
