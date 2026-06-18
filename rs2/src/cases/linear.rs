use crate::*;

use ordered_float::OrderedFloat;
type F64 = OrderedFloat<f64>;
fn f(x: f64) -> F64 { OrderedFloat(x) }

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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

fn add_offset(l: Linear, o: F64) -> Linear {
    let offset = l.offset + o;
    let factor = l.factor;
    Linear { offset, factor }
}

fn add_factor(l: Linear, f: F64) -> Linear {
    let offset = l.offset * f;
    let factor = l.factor * f;
    Linear { factor, offset }
}

impl Analysis for LinearAnalysis {
    type G = Linear;
    type S = ConstProp;
    type L = LinearLang;

    fn canon(n: &Self::L, uf: &Unionfind<Self::S>) -> (Self::G, Either<Self::L, Id>) {
        match n {
            LinearLang::Add([x, y]) => {
                match (uf.get_semilattice(x).0, uf.get_semilattice(y).0) {
                    (None, None) => (Linear::identity(), Either::L(LinearLang::Add([uf.find(*x), uf.find(*y)]))), // TODO extract common offsets.
                    (Some(x), None) => {
                        let (y_g, y) = y;
                        let l = add_offset(*y_g, x);
                        (l, Either::R(*y))
                    },
                    (None, Some(y)) => {
                        let (x_g, x) = x;
                        let l = add_offset(*x_g, y);
                        (l, Either::R(*x))
                    },
                    (Some(x), Some(y)) => (Linear { factor: f(1.0), offset: x+y }, Either::L(LinearLang::Const(f(0.0)))),
                }
            },
            LinearLang::Mul([x, y]) => {
                match (uf.get_semilattice(x).0, uf.get_semilattice(y).0) {
                    (None, None) => (Linear::identity(), Either::L(LinearLang::Mul([uf.find(*x), uf.find(*y)]))),
                    (Some(x), None) => {
                        let (y_g, y) = y;
                        let l = add_factor(*y_g, x);
                        (l, Either::R(*y))
                    },
                    (None, Some(y)) => {
                        let (x_g, x) = x;
                        let l = add_factor(*x_g, y);
                        (l, Either::R(*x))
                    },
                    (Some(x), Some(y)) => (Linear { factor: f(1.0), offset: x*y }, Either::L(LinearLang::Const(f(0.0)))),
                }
            },
            LinearLang::Const(c) => (Linear { factor: f(1.0), offset: *c }, Either::L(LinearLang::Const(f(0.0)))),
            LinearLang::Symbol(s) => (Linear::identity(), Either::L(LinearLang::Symbol(*s))),
        }
    }

    fn mk(n: &Self::L, id: Id, uf: &Unionfind<Self::S>) -> Self::S {
        match n {
            LinearLang::Add([x, y]) => {
                let Some(x) = uf.get_semilattice(x).0 else { return ConstProp(None) };
                let Some(y) = uf.get_semilattice(y).0 else { return ConstProp(None) };
                ConstProp(Some(x+y))
            },
            LinearLang::Mul([x, y]) => {
                let Some(x) = uf.get_semilattice(x).0 else { return ConstProp(None) };
                let Some(y) = uf.get_semilattice(y).0 else { return ConstProp(None) };
                ConstProp(Some(x*y))
            },
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

#[test]
fn small_linear_test() {
    let s = |i| LinearLang::Symbol(Symbol::new(format!("x{i}")));
    let mut eg: EGraph<LinearAnalysis> = EGraph::new();

    let three = eg.add(&LinearLang::Const(f(3.)));
    let five = eg.add(&LinearLang::Const(f(5.)));

    let s0 = eg.add(&s(0));
    let s1 = eg.add(&s(1));

    let s0_3 = eg.add(&LinearLang::Add([s0, three]));
    eg.union(s0_3, s1);
    // s1 = s0 + 3

    dbg!(eg.get_g_between(s0, s1));

    let s0_5 = eg.add(&LinearLang::Mul([five, s0]));
    dbg!(eg.get_g_between(s0, s0_5));

    eg.union(s0_5, s1);
    // 5*s0 = s1

    // 5*(s1-3) = s1
    // 5*s1 - 15 = s1
    // 4*s1 = 15
    // s1 = 15/4

    let result = eg.get_semilattice(&s1).0.unwrap();
    assert!(is_close(result, f(15./4.)));
}

#[test]
fn big_linear_test() {
    let s = |i| LinearLang::Symbol(Symbol::new(format!("x{i}")));
    let mut eg: EGraph<LinearAnalysis> = EGraph::new();

    let seven = eg.add(&LinearLang::Const(f(7.)));
    let four = eg.add(&LinearLang::Const(f(4.)));
    let five = eg.add(&LinearLang::Const(f(5.)));

    for i in 0..1000 {
        let si = eg.add(&s(i));
        let sip = eg.add(&s(i+1));

        let si7 = eg.add(&LinearLang::Add([si, seven]));
        let sip4 = eg.add(&LinearLang::Add([sip, four]));
        eg.union(si7, sip4);
        // s[i] + 7 = s[i+1] + 4
        // s[i+1] = s[i] + 3
    }

    // let s[0] be x, and s[1000] be y, then
    // y = 3*1000 + x
    // y = 3000 + x

    let s0 = eg.add(&s(0));
    let s0_5 = eg.add(&LinearLang::Mul([five, s0]));
    let s1000 = eg.add(&s(1000));
    eg.union(s0_5, s1000);

    // 5x = y
    // 5x = 3000 + x
    // 4x = 3000
    // x = 3000/4
    // x = 750
    // -> y = 3750

    let result = eg.get_semilattice(&s1000).0.unwrap();
    assert!(is_close(result, f(3750.)));
}
