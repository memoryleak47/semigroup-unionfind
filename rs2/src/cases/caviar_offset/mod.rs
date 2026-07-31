use crate::*;
use std::time::Instant;

mod matching;
use matching::*;

// mod testing;
// use testing::*;

mod analysis;
use analysis::*;

mod parse;
use parse::*;

mod rules;
use rules::*;

type Pat = Pattern<CaviarAnalysis>;

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

impl Semilattice for Option<i64> {
    type G = Offset;

    fn act(g: &Self::G, s: &Self) -> Self {
        s.map(|x| g.apply(x))
    }

    fn merge(&mut self, other: Self) -> bool {
        let Some(o) = other else { return false };

        match *self {
            None => {
                *self = Some(o);
                true
            },
            Some(x) => {
                assert_eq!(x, o);
                false
            },
        }
    }

    fn insert_self_edge(&mut self, g: Self::G) {
        assert_eq!(g, Offset(0));
    }

    fn contains_self_edge(&self, g: &Self::G) -> bool {
        *g == Offset(0)
    }
}

pub type OffsetId = (Offset, Id);

#[derive(Hash, PartialEq, Eq, Clone, Copy, Debug)]
pub enum CaviarLang {
    Add([OffsetId; 2]),
    Sub([OffsetId; 2]),
    Mul([OffsetId; 2]),
    Div([OffsetId; 2]),
    Mod([OffsetId; 2]),
    Max([OffsetId; 2]),
    Min([OffsetId; 2]),
    Lt([OffsetId; 2]),
    Gt([OffsetId; 2]),
    Not(OffsetId),
    Let([OffsetId;2]),
    Get([OffsetId;2]),
    Eq([OffsetId; 2]),
    IEq([OffsetId; 2]),
    Or([OffsetId; 2]),
    And([OffsetId; 2]),
    Constant(i64),
    Symbol(Symbol),
}

pub fn run_caviar() {
    let rules = mk_rules();

    let arg = std::env::args().nth(1).unwrap();
    let expr = parse(&arg);

    let mut eg = EGraph::new();
    let i = add_expr(&expr, &mut eg);

    let one = add_expr(&parse("1"), &mut eg);
    let zero = add_expr(&parse("0"), &mut eg);

    let mut iter = 0;
    loop {
        general_eqsat::<CaviarAnalysis, CaviarMatcher>(&mut eg, &*rules, 1);
        
        iter += 1;
        println!("iter {iter} done, size={}", eg.hashcons.len());

        if eg.is_equal(zero, i) {
            println!("PROOF FOUND: it's equal to 0");
            break
        }
        if eg.is_equal(one, i) {
            println!("PROOF FOUND: it's equal to 1");
            break
        }
    }
}
