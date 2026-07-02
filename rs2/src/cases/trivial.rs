use crate::*;
use std::rc::Rc;
use std::collections::HashMap;
use smallvec::*;

impl Group for () {
    fn identity() {}
    fn compose(l: &(), r: &()) {}
    fn inverse(&self) {}
}

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct TrivialLang {
    f: Symbol,
    args: Box<[Id]>,
}

impl Semilattice for () {
    type G = ();

    fn act(g: &(), s: &()) { }
    fn merge(&mut self, other: ()) -> bool { false }
    fn insert_self_edge(&mut self, g: ()) {}
    fn contains_self_edge(&self, g: &()) -> bool { true }
}

impl Analysis for () {
    type G = ();
    type S = ();
    type L = TrivialLang;

    fn canon(n: &TrivialLang, uf: &Unionfind<()>) -> ((), Either<TrivialLang, Id>) {
        let mut args = Vec::new();
        for x in &n.args {
            let ((), y) = uf.find(((), x.clone()));
            args.push(y);
        }
        let n = TrivialLang {
            f: n.f,
            args: args.into(),
        };
        ((), Either::L(n))
    }

    fn mk(n: &TrivialLang, id: Id, uf: &Unionfind<()>) {}
}

/// E-Matching

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
enum Pattern {
    PVar(PVar),
    Node(Symbol, Box<[Pattern]>),
}

// terms share the same layout as patterns.
type Term = Pattern;

type PVar = Symbol;
type L = TrivialLang;

// semantics:
// a := applying the subst to the pattern
// b := canonical term of x
// proof translates a to b
fn ematch(x: Id, pat: &Pattern, eg: &EGraph<()>) -> Vec<Subst> {
    ematch_impl(x, pat, eg, &Subst::new())
}

fn ematch_impl(x: Id, pat: &Pattern, eg: &EGraph<()>, subst: &Subst) -> Vec<Subst> {
    match pat {
        Pattern::PVar(v) => {
            let mut subst = subst.clone();
            if let Some(a) = subst.get(v) {
                if a != x { return Vec::new() }
            } else {
                subst.insert(v.clone(), x);
            }
            vec![subst]
        },
        Pattern::Node(f, subpats) => {
            let mut out = Vec::new();
            for ((), n) in eg.nodes_of_bare(x) {
                if n.f != *f { continue }

                let mut acc = vec![subst.clone()];
                for (subid, subpat) in n.args.iter().zip(subpats.iter()) {
                    for subst in std::mem::take(&mut acc) {
                        acc.extend(ematch_impl(*subid, subpat, eg, &subst));
                    }
                }
                out.extend(acc);
            }
            out
        },
    }
}

fn instantiate(pattern: &Pattern, subst: &Subst, eg: &mut EGraph<()>) -> Id {
    match pattern {
        Pattern::PVar(v) => subst.get(v).unwrap(),
        Pattern::Node(f, pargs) => {
            let f = *f;
            let mut args = Vec::new();
            for p in pargs {
                args.push(instantiate(p, subst, eg));
            }
            let args = args.into_boxed_slice();
            eg.add(&TrivialLang { f, args }).1
        }
    }
}

fn eqsat(eg: &mut EGraph<()>, rules: &Rules, n: usize) {
    for _ in 0..n {
        // 1. e-match
        let mut future_unions = Vec::new();
        for (rule_id, (_, lhs, _)) in rules.iter().enumerate() {
            for x in eg.classes() {
                for subst in ematch(x, lhs, eg) {
                    future_unions.push((rule_id, subst));
                }
            }
        }

        // 2. add instantiations
        let mut real_future_unions = Vec::new();
        for (rule_id, subst) in future_unions {
            let (_, lhs, rhs) = &rules[rule_id];
            let lhs = instantiate(lhs, &subst, eg);
            let rhs = instantiate(rhs, &subst, eg);
            real_future_unions.push((lhs, rhs));
        }

        // 3. add unions
        for (lhs, rhs) in real_future_unions {
            eg.uf.union(((), lhs), ((), rhs));
        }

        // 4. rebuild
        eg.rebuild();
    }
}

/// Tests

fn atom(s: &str) -> &'static Pattern {
    Box::leak(Box::new(Pattern::Node(Symbol::new(s), Box::new([]))))
}

fn pvar(s: &str) -> &'static Pattern {
    Box::leak(Box::new(Pattern::PVar(Symbol::new(s))))
}

fn add(p1: &'static Pattern, p2: &'static Pattern) -> &'static Pattern {
    Box::leak(Box::new(Pattern::Node(Symbol::new("add"), Box::new([p1.clone(), p2.clone()]))))
}

fn neg(p: &'static Pattern) -> &'static Pattern {
    Box::leak(Box::new(Pattern::Node(Symbol::new("neg"), Box::new([p.clone()]))))
}

fn zero() -> &'static Pattern {
    Box::leak(Box::new(Pattern::Node(Symbol::new("zero"), Box::new([]))))
}

fn add_term(term: &Term, eg: &mut EGraph<()>) -> ((), Id) {
    match term {
        Pattern::PVar(_) => panic!("can't add pvar!"),
        Pattern::Node(f, pargs) => {
            let f = *f;
            let mut args = Vec::new();
            for p in pargs {
                args.push(add_term(p, eg).1);
            }
            let args = args.into_boxed_slice();
            eg.add(&TrivialLang { f, args })
        },
    }
}

type Rules<'a> = [(Symbol, &'a Pattern, &'a Pattern)];

fn eqsat_test(t1: &Term, t2: &Term, rules: &Rules, n: usize) {
    let eg: &mut EGraph<()> = &mut EGraph::new();

    let x1 = add_term(t1, eg);
    let x2 = add_term(t2, eg);

    eqsat(eg, rules, n);
    dbg!(eg.hashcons.len());
    let () = eg.get_g_between(x1.clone(), x2.clone()).unwrap();
}

// This is intended to be a slightly more bulky test. To see how we stand in memory consumption.
#[test]
fn test_trivial_arith() {
    let rule1 = (
        Symbol::new("add-neg"),
        add(neg(pvar("?a")), pvar("?a")),
        zero()
    );

    let rule2 = (
        Symbol::new("add-zero"),
        add(pvar("?a"), zero()),
        pvar("?a")
    );

    let rule3 = (
        Symbol::new("add-comm"),
        add(pvar("?a"), pvar("?b")),
        add(pvar("?b"), pvar("?a"))
    );

    let rule4 = (
        Symbol::new("add-assoc1"),
        add(add(pvar("?a"), pvar("?b")), pvar("?c")),
        add(pvar("?a"), add(pvar("?b"), pvar("?c"))),
    );

    let rule5 = (
        Symbol::new("add-assoc2"),
        add(pvar("?a"), add(pvar("?b"), pvar("?c"))),
        add(add(pvar("?a"), pvar("?b")), pvar("?c")),
    );

    let mut t1 = zero();
    for i in 0..3 {
        let a = atom(&format!("a{i}"));
        t1 = add(t1, a);
    }
    for i in 0..3 {
        let a = atom(&format!("a{i}"));
        t1 = add(neg(a), t1);
    }

    let t2 = zero();
    let rules = &[rule1, rule2, rule3, rule4, rule5];
    eqsat_test(t1, t2, rules, 6);
}

#[derive(Clone)]
pub struct Subst(SmallVec<[(PVar, Id); 3]>);

impl Subst {
    pub fn new() -> Self {
        Subst(SmallVec::new())
    }

    pub fn get(&self, x: &PVar) -> Option<Id> {
        for (a, b) in &self.0 {
            if x == a { return Some(*b) }
        }
        None
    }

    pub fn insert(&mut self, x: PVar, y: Id) {
        assert_eq!(self.get(&x), None);
        self.0.push((x, y));
    }
}
