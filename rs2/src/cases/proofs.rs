use crate::*;
use std::rc::Rc;
use std::collections::HashMap;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum ProofObj {
    Refl,
    Sym(Proof),
    Trans(Proof, Proof), // works in compose order. So Trans(a, b) first applies b, then a.
    Congr(Box<[Proof]>),
    Rule(Symbol),
}

type Proof = Rc<ProofObj>;

impl Group for Proof {
    fn identity() -> Proof {
        Rc::new(ProofObj::Refl)
    }

    fn compose(l: &Proof, r: &Proof) -> Proof {
        mk_trans(l.clone(), r.clone())
    }

    fn inverse(&self) -> Proof {
        mk_sym(self.clone())
    }
}

fn is_refl(x: &Proof) -> bool {
    matches!(**x, ProofObj::Refl)
}

// smart constructors:
fn mk_refl() -> Proof {
    Rc::new(ProofObj::Refl)
}

fn mk_trans(x: Proof, y: Proof) -> Proof {
    if is_refl(&x) {
        y
    } else if is_refl(&y) {
        x
    } else {
        Rc::new(ProofObj::Trans(x, y))
    }
}

fn mk_sym(x: Proof) -> Proof {
    if let ProofObj::Sym(xx) = &*x {
        xx.clone()
    } else if is_refl(&x) {
        mk_refl()
    } else {
        Rc::new(ProofObj::Sym(x))
    }
}

fn mk_congr(argproofs: Box<[Proof]>) -> Proof {
    if argproofs.iter().all(is_refl) {
        mk_refl()
    } else {
        Rc::new(
            ProofObj::Congr(argproofs)
        )
    }
}

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
struct ProofLang {
    f: Symbol,
    args: Box<[(Proof, Id)]>,
}

#[derive(Clone, Debug)]
struct ProofData;

impl Semilattice for ProofData {
    type G = Proof;

    fn act(g: &Self::G, s: &Self) -> Self { ProofData }
    fn merge(&mut self, other: Self) -> bool { false }
    fn insert_self_edge(&mut self, g: Self::G) {}
    fn contains_self_edge(&self, g: &Self::G) -> bool { true }
}

struct ProofAnalysis;

impl Analysis for ProofAnalysis {
    type G = Proof;
    type S = ProofData;
    type L = ProofLang;

    fn canon(n: &Self::L, uf: &Unionfind<Self::S>) -> (Self::G, Either<Self::L, Id>) {
        let mut proofs = Vec::new();
        let mut args = Vec::new();
        for x in &n.args {
            let (p, y) = uf.find(x.clone());
            proofs.push(p.clone());
            args.push((mk_refl(), y));
        }
        let p = mk_congr(proofs.into());
        let n = ProofLang {
            f: n.f,
            args: args.into(),
        };
        (p, Either::L(n))
    }

    fn mk(n: &Self::L, id: Id, uf: &Unionfind<Self::S>) -> Self::S { ProofData }
}

fn justify((p, x): (Proof, Id), j: Symbol) -> (Proof, Id) {
    let p2 = Rc::new(ProofObj::Rule(j));
    (Proof::compose(&p2, &p), x)
}

/// E-Matching

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
enum Pattern {
    PVar(PVar),
    Node(Symbol, Box<[Pattern]>),
}

// terms share the same layout as patterns.
type Term = Pattern;

type PVar = String;
type Subst = HashMap<PVar, Id>;
type L = ProofLang;
type G = Proof;

// semantics:
// a := applying the subst to the pattern
// b := canonical term of x
// proof translates a to b
fn ematch(x: Id, pat: &Pattern, eg: &EGraph<ProofAnalysis>) -> Vec<Subst> {
    ematch_impl(x, pat, eg, &Subst::new())
}

fn ematch_impl(x: Id, pat: &Pattern, eg: &EGraph<ProofAnalysis>, subst: &Subst) -> Vec<Subst> {
    match pat {
        Pattern::PVar(v) => {
            let mut subst = subst.clone();
            if let Some(a) = subst.get(v) {
                if *a != x { return Vec::new() }
            } else {
                subst.insert(v.clone(), x);
            }
            vec![subst]
        },
        Pattern::Node(f, subpats) => {
            let mut out = Vec::new();
            for (_, n) in eg.nodes_of_bare(x) {
                // g*n = i
                if n.f != *f { continue }

                let mut acc = vec![subst.clone()];
                for ((grefl, subid), subpat) in n.args.iter().zip(subpats.iter()) {
                    assert_eq!(*grefl, G::identity());
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

fn instantiate(pattern: &Pattern, subst: &Subst, eg: &mut EGraph<ProofAnalysis>) -> (Proof, Id) {
    match pattern {
        Pattern::PVar(v) => (G::identity(), subst[v]),
        Pattern::Node(f, pargs) => {
            let f = *f;
            let mut args = Vec::new();
            for p in pargs {
                args.push(instantiate(p, subst, eg));
            }
            let args = args.into_boxed_slice();
            eg.add(&ProofLang { f, args })
        }
    }
}

fn eqsat(eg: &mut EGraph<ProofAnalysis>, rules: &Rules, n: usize) {
    for _ in 0..n {
        let mut future_unions = Vec::new();
        for (rule_name, lhs, rhs) in rules.iter() {
            for x in eg.classes() {
                for subst in ematch(x, lhs, eg) {
                    future_unions.push((*rule_name, lhs, rhs, subst));
                }
            }
        }
        for (rule_name, lhs, rhs, subst) in future_unions {
            let lhs = instantiate(lhs, &subst, eg);
            let rhs = instantiate(rhs, &subst, eg);

            let lhs = justify(lhs.clone(), rule_name);
            eg.union(lhs, rhs);
        }
    }
}

/// Tests

// TODO: you can't apply a proof, which uses rules like "?a + (-?a) => 0" as it could use those rules in "reverse" mode, where you have to *guess* the ?a.
fn apply_proof(term: &Term, p: &Proof, rules: &Rules) -> Term {
    apply_proof_impl(term, p, rules, false)
}

fn apply_proof_impl(term: &Term, p: &Proof, rules: &Rules, rev: bool) -> Term {
    match &**p {
        ProofObj::Refl => term.clone(),
        ProofObj::Sym(p) => apply_proof_impl(term, p, rules, !rev),
        ProofObj::Trans(p1, p2) => {
            if rev {
                let term = apply_proof_impl(term, p1, rules, rev);
                let term = apply_proof_impl(&term, p2, rules, rev);
                term
            } else {
                let term = apply_proof_impl(term, p2, rules, rev);
                let term = apply_proof_impl(&term, p1, rules, rev);
                term
            }
        },
        ProofObj::Congr(subs) => {
            let Term::Node(f, args) = term else { panic!() };
            assert_eq!(subs.len(), args.len());
            let mut outs = Vec::new();
            for (t, p) in args.iter().zip(subs) {
                outs.push(apply_proof_impl(t, p, rules, rev));
            }
            Term::Node(*f, outs.into_boxed_slice())
        },
        ProofObj::Rule(r) => {
            let (_, lhs, rhs) = rules.iter().find(|(name, _, _)| name == r).unwrap();
            let (lhs, rhs) = if rev { (rhs, lhs) } else { (lhs, rhs) };
            let subst = &mut TermSubst::new();

            term_match(term, lhs, subst);
            pattern_apply(rhs, subst)
        },
    }
}

type TermSubst = HashMap<PVar, Term>;

fn term_match(term: &Term, pat: &Pattern, subst: &mut TermSubst) {
    match pat {
        Pattern::PVar(v) => {
            if let Some(t) = subst.get(&*v) {
                assert_eq!(term, t);
            } else {
                subst.insert(v.clone(), term.clone());
            }
        },
        Pattern::Node(p_f, p_args) => {
            let Term::Node(t_f, t_args) = term else { panic!() };
            assert_eq!(p_f, t_f);
            assert_eq!(p_args.len(), t_args.len());
            for (tt, pp) in t_args.iter().zip(p_args) {
                term_match(tt, pp, subst);
            }
        },
    }
}

fn pattern_apply(pattern: &Pattern, subst: &TermSubst) -> Term {
    match pattern {
        Pattern::PVar(v) => subst[v].clone(),
        Pattern::Node(f, args) => {
            let mut outargs = Vec::new();
            for a in args {
                outargs.push(pattern_apply(a, subst));
            }
            let outargs = outargs.into_boxed_slice();
            Term::Node(*f, outargs)
        },
    }
}

fn atom(s: &str) -> &'static Pattern {
    Box::leak(Box::new(Pattern::Node(Symbol::new(s), Box::new([]))))
}

fn pvar(s: &str) -> &'static Pattern {
    Box::leak(Box::new(Pattern::PVar(s.to_string())))
}

fn f(p1: &'static Pattern, p2: &'static Pattern) -> &'static Pattern {
    Box::leak(Box::new(Pattern::Node(Symbol::new("f"), Box::new([p1.clone(), p2.clone()]))))
}

fn h(p: &'static Pattern) -> &'static Pattern {
    Box::leak(Box::new(Pattern::Node(Symbol::new("h"), Box::new([p.clone()]))))
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

fn add_term(term: &Term, eg: &mut EGraph<ProofAnalysis>) -> (Proof, Id) {
    match term {
        Pattern::PVar(_) => panic!("can't add pvar!"),
        Pattern::Node(f, pargs) => {
            let f = *f;
            let mut args = Vec::new();
            for p in pargs {
                args.push(add_term(p, eg));
            }
            let args = args.into_boxed_slice();
            eg.add(&ProofLang { f, args })
        },
    }
}

type Rules<'a> = [(Symbol, &'a Pattern, &'a Pattern)];

const DEBUGGING: bool = false;
fn eqsat_test(t1: &Term, t2: &Term, rules: &Rules, n: usize) {
    let eg: &mut EGraph<ProofAnalysis> = &mut EGraph::new();

    let x1 = add_term(t1, eg);
    let x2 = add_term(t2, eg);

    eqsat(eg, rules, n);
    if DEBUGGING {
        eg.dump();
        dbg!(&x1);
        dbg!(&x2);
        dbg!(&eg.find(x1.clone()));
        dbg!(&eg.find(x2.clone()));
    }
    let p = eg.get_g_between(x1.clone(), x2.clone()).unwrap();
    if DEBUGGING {
        dbg!(&p);
    }

    // TODO: this can fail as explained above.
    // assert_eq!(apply_proof(t1, &p, rules), t2.clone());
}

#[test]
fn test_proofs() {
    let rule = (
        Symbol::new("a -> b"),
        atom("a"),
        atom("b"),
    );
    let t1 = h(atom("a"));
    let t2 = h(atom("b"));
    eqsat_test(t1, t2, &[rule], 3);
}

#[test]
fn test_proofs2() {
    let rule = (
        Symbol::new("h(?a) -> ?a"),
        h(pvar("?a")),
        pvar("?a")
    );
    let t1 = h(atom("a"));
    let t2 = atom("a");
    eqsat_test(t1, t2, &[rule], 1);
}

#[test]
fn test_proofs3() {
    let rule1 = (
        Symbol::new("f(?x,?y) -> ?y"),
        f(pvar("?x"), pvar("?y")),
        pvar("?y"),
    );
    let rule2 = (
        Symbol::new("x -> f(x,y)"),
        atom("x"),
        f(atom("x"), atom("y")),
    );
    let t1 = atom("x");
    let t2 = atom("y");
    let rules = &[rule1, rule2];
    eqsat_test(t1, t2, rules, 2);
}

#[test]
fn test_proofs4() {
    let rule1 = (
        Symbol::new("f(?a, ?b) -> f(?a, h(?b))"),
        f(pvar("?a"), pvar("?b")),
        f(pvar("?a"), h(pvar("?b"))),
    );
    let rule2 = (
        Symbol::new("f(?a, ?b) -> f(h(?a), ?b)"),
        f(pvar("?a"), pvar("?b")),
        f(h(pvar("?a")), pvar("?b")),
    );
    let rule3 = (
        Symbol::new("f(h(?a), h(?b)) -> f(h(?b), h(?a))"),
        f(h(pvar("?a")), h(pvar("?b"))),
        f(h(pvar("?b")), h(pvar("?a"))),
    );
    let t1 = f(atom("x"), atom("y"));
    let t2 = f(atom("y"), atom("x"));
    let rules = &[rule1, rule2, rule3];
    eqsat_test(t1, t2, rules, 4);
}

#[test]
fn test_proofs5() {
    let rule1 = (
        Symbol::new("r1"),
        atom("a"),
        atom("b"),
    );
    let t1 = atom("b");
    let t2 = atom("a");
    let rules = &[rule1];
    eqsat_test(t1, t2, rules, 1);
}

#[test]
fn test_proofs6() {
    let rule1 = (
        Symbol::new("rule1"),
        atom("a"),
        atom("b"),
    );
    let rule2 = (
        Symbol::new("rule2"),
        atom("b"),
        atom("c")
    );
    let t1 = atom("a");
    let t2 = atom("b");
    let rules = &[rule1, rule2];
    eqsat_test(t1, t2, rules, 2);
}

#[test]
fn test_proofs7() {
    let rule1 = (
        Symbol::new("c -> y"),
        atom("c"),
        atom("y"),
    );
    let rule2 = (
        Symbol::new("x -> c"),
        atom("x"),
        atom("c"),
    );
    let t1 = atom("x");
    let t2 = atom("y");
    let rules = &[rule1, rule2];
    eqsat_test(t1, t2, rules, 2);
}

#[test]
fn test_proofs8() {
    let rule1 = (
        Symbol::new("f(?x, ?y) -> f(?y, ?x)"),
        f(pvar("?x"), pvar("?y")),
        f(pvar("?y"), pvar("?x")),
    );
    let rule2 = (
        Symbol::new("f(?x, h(?y)) -> h(f(?x, ?y))"),
        f(pvar("?x"), h(pvar("?y"))),
        h(f(pvar("?x"), pvar("?y"))),
    );
    let rule3 = (
        Symbol::new("h(h(?x)) -> ?x"),
        h(h(pvar("?x"))),
        pvar("?x"),
    );
    let t1 = f(h(atom("a")), h(atom("b")));
    let t2 = h(h(f(atom("b"), atom("a"))));
    let rules = &[rule1, rule2, rule3];
    eqsat_test(t1, t2, rules, 3);
}

#[test]
fn test_proofs9() {
    let rule1 = (
        Symbol::new("f(?a, ?b) -> f(?b, ?a)"),
        f(pvar("?a"), pvar("?b")),
        f(pvar("?b"), pvar("?a")),
    );
    let rule2 = (
        Symbol::new("f(f(?a, ?b), ?c) -> f(?a, f(?b, ?c))"),
        f(f(pvar("?a"), pvar("?b")), pvar("?c")),
        f(pvar("?a"), f(pvar("?b"), pvar("?c"))),
    );
    let rule3 = (
        Symbol::new("f(?a, h(?a)) -> h(f(?a, ?a))"),
        f(pvar("?a"), h(pvar("?a"))),
        h(f(pvar("?a"), pvar("?a"))),
    );
    let t1 = f(f(atom("x"), h(atom("x"))), atom("y"));
    let t2 = f(atom("y"), h(f(atom("x"), atom("x"))));
    let rules = &[rule1, rule2, rule3];
    eqsat_test(t1, t2, rules, 1);
}

#[test]
fn test_proofs10() {
    let rule1 = (
        Symbol::new("f(?a, h(?b)) -> h(f(?a, ?b))"),
        f(pvar("?a"), h(pvar("?b"))),
        h(f(pvar("?a"), pvar("?b"))),
    );
    let rule2 = (
        Symbol::new("f(?a, ?b) -> f(?b, ?a)"),
        f(pvar("?a"), pvar("?b")),
        f(pvar("?b"), pvar("?a")),
    );
    let t1 = f(h(h(h(h(h(atom("x")))))), atom("y"));
    let t2 = f(atom("x"), h(h(h(h(h(atom("y")))))));
    let rules = &[rule1, rule2];
    eqsat_test(t1, t2, rules, 10);
}

// This is intended to be a slightly more bulky test. To see how we stand in memory consumption.
#[test]
fn test_proofs_arith() {
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
    eqsat_test(t1, t2, rules, 4);
}
