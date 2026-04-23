use crate::*;

// represents `\x -> factor*x + offset`
#[derive(Clone, PartialEq)]
struct Linear {
    factor: f64,
    offset: f64
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

#[test]
fn lintest() {
    let l = Linear {
        factor: 22.,
        offset: -4.,
    };

    assert!(Linear::compose(&l, &l.inverse()) == Linear::identity());
    assert!(Linear::compose(&l.inverse(), &l) == Linear::identity());
}
