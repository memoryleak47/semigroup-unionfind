use crate::*;
use std::rc::Rc;
use std::collections::HashMap;

type Pat = Pattern<ProofAnalysis>;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum ProofObj {
    Refl,
    Sym(Proof),
    Trans(Proof, Proof), // works in compose order. So Trans(a, b) first applies b, then a.
    Congr(Box<[Proof]>),
    Rule(Rc<(Pattern<ProofAnalysis>, Pattern<ProofAnalysis>)>, Box<[(PVar, Term<ProofAnalysis>)]>), // NOTE: the PVar can be ommitted, if we use the Ord order for PVars.
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

type PId = (Proof, Id);

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
struct ProofLang {
    f: Symbol,
    args: Box<[PId]>,
}

fn inst(pat: &Pattern<ProofAnalysis>, subst: &[(PVar, Term<ProofAnalysis>)]) -> Term<ProofAnalysis> {
    match pat {
        Pattern::PVar(var) => {
            subst.iter().find(|(x, _)| x == var).unwrap().1.clone()
        },
        Pattern::Node(n, args) => {
            let mut args = args.iter().map(|x| inst(x, subst)).collect();
            Pattern::Node(n.clone(), args)
        },
        Pattern::G(..) => todo!(),
    }
}

fn act(g: &Proof, t: &Term<ProofAnalysis>, flipped: bool) -> Term<ProofAnalysis> {
    match &**g {
        ProofObj::Refl => t.clone(),
        ProofObj::Sym(g) => act(g, t, !flipped),
        ProofObj::Trans(g1, g2) => {
            if flipped { act(g2, &act(g1, t, true), true) }
            else { act(g1, &act(g2, t, false), false) }
        },
        ProofObj::Congr(gs) => {
            let Term::Node(n, children) = t else { panic!() };
            let mut children2: Vec<Term<ProofAnalysis>> = Vec::new();
            for (sub_g, sub_t) in gs.iter().zip(children.iter()) {
                children2.push(act(sub_g, sub_t, flipped));
            }
            Term::Node(n.clone(), children2.into())
        },
        ProofObj::Rule(rule, subst) => {
            let (lhs, rhs) = &**rule;
            let (lhs, rhs) = if flipped { (rhs, lhs) } else { (lhs, rhs) };
            let lhs = inst(lhs, subst);
            let rhs = inst(rhs, subst);
            assert_eq!(&lhs, t);
            rhs
        },
    }
}

impl Semilattice for Term<ProofAnalysis> {
    type G = Proof;

    fn act(g: &Proof, t: &Self) -> Self {
        act(g, t, false)
    }

    fn merge(&mut self, other: Self) -> bool {
        // what if children disagree on how canonicalized their children are?
        // assert_eq!(self, &other);

        false
    }

    fn insert_self_edge(&mut self, g: Proof) {}
    fn contains_self_edge(&self, g: &Proof) -> bool { true }
}

struct ProofAnalysis;

impl Analysis for ProofAnalysis {
    type G = Proof;
    type S = Term<ProofAnalysis>; // We store a canonical term in every e-class.
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

    fn mk(n: &Self::L, id: Id, uf: &Unionfind<Self::S>) -> Self::S {
        let mut n = n.clone();
        let mut ch = Vec::new();
        for x in n.args.iter_mut() {
            ch.push(uf.get_semilattice(x));
            *x = (mk_refl(), Id(0));
        }
        Term::Node(n, ch.into())
    }

    fn children_mut(node: &mut ProofLang) -> Box<[&mut (Proof, Id)]> {
        node.args.iter_mut().collect()
    }

    fn ematch(eg: &EGraph<Self>, i: Id, pat: &Pattern<Self>) -> Vec<Subst<Self>> {
        skeleton_ematch(eg, i, pat).into_iter().map(|(subst, _)| {
            subst.into_iter().map(|(k, v)| (k, (mk_refl(), v))).collect()
        }).collect()
    }
}

/// Tests

fn atom(s: &str) -> Pat {
    let node = ProofLang {
        f: Symbol::new(s),
        args: Box::new([]),
    };
    Pattern::Node(node, Box::new([]))
}

fn pvar(s: &str) -> Pat {
    Pattern::PVar(Symbol::new(s))
}

fn f(p1: Pat, p2: Pat) -> Pat {
    let nil = (mk_refl(), Id(0));
    let node = ProofLang {
        f: Symbol::new("f"),
        args: Box::new([nil.clone(), nil.clone()]),
    };
    Pattern::Node(node, Box::new([p1, p2]))
}

fn h(p: Pat) -> Pat {
    let nil = (mk_refl(), Id(0));
    let node = ProofLang {
        f: Symbol::new("h"),
        args: Box::new([nil]),
    };
    Pattern::Node(node, Box::new([p]))
}

fn add(p1: Pat, p2: Pat) -> Pat {
    let nil = (mk_refl(), Id(0));
    let node = ProofLang {
        f: Symbol::new("add"),
        args: Box::new([nil.clone(), nil.clone()]),
    };
    Pattern::Node(node, Box::new([p1, p2]))
}

fn neg(p: Pat) -> Pat {
    let nil = (mk_refl(), Id(0));
    let node = ProofLang {
        f: Symbol::new("neg"),
        args: Box::new([nil]),
    };
    Pattern::Node(node, Box::new([p]))
}

fn zero() -> Pat {
    atom("zero")
}

type Rules = [(Symbol, Pat, Pat)];

fn eqsat_test(t1: Term<ProofAnalysis>, t2: Term<ProofAnalysis>, rules: &Rules, n: usize) {
    let rules: Box<[Rule<ProofAnalysis>]> = rules.iter().map(|(rule_id, l, r)| {

        let rule_id: Symbol = *rule_id;
        let l: Pattern<ProofAnalysis> = l.clone();
        let r: Pattern<ProofAnalysis> = r.clone();
        let lr = Rc::new((l.clone(), r.clone()));

        let r: Applier<ProofAnalysis> = Box::new(move |lhs_eclass, subst, eg| {
            let rhs_eclass = instantiate(&r, eg, &subst);

            let subst: Box<[(PVar, Term<ProofAnalysis>)]> = subst.iter().map(|(k, v)| (*k, eg.get_semilattice(&v))).collect();

            let annotation = Rc::new(ProofObj::Rule(lr.clone(), subst)).inverse();
            let rhs_eclass = (Proof::compose(&annotation, &rhs_eclass.0), rhs_eclass.1);
            eg.union(lhs_eclass, rhs_eclass);
        });

        (l, r)
    }).collect();

    let eg: &mut EGraph<ProofAnalysis> = &mut EGraph::new();
    let x1 = add_expr(&t1, eg);
    let x2 = add_expr(&t2, eg);

    eqsat::<_>(eg, &rules, Box::new([]), Duration::MAX, usize::MAX, n);
    let p = eg.get_g_between(x1.clone(), x2.clone()).unwrap();
    let t1_ = eg.get_semilattice(&x1);
    let t2_ = eg.get_semilattice(&x2);
    assert_eq!(t1_, t1);
    assert_eq!(t2_, t2);
    assert_eq!(act(&p, &t1, false), t2);
    assert_eq!(act(&p, &t2, true), t1);

    dbg!(eg.hashcons.len());
}

#[test]
fn test_proofs_triv1() {
    let t1 = atom("a");
    let t2 = atom("a");
    eqsat_test(t1, t2, &[], 3);
}

#[test]
fn test_proofs_triv2() {
    let rule = (
        Symbol::new("a -> b"),
        atom("a"),
        atom("b"),
    );
    let t1 = atom("a");
    let t2 = atom("b");
    eqsat_test(t1, t2, &[rule], 3);
}

#[test]
fn test_proofs_triv3() {
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
#[ignore] // takes too long with this trivial encoding
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
    eqsat_test(t1, t2, rules, 6);
}
