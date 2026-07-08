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

    fn children_mut(node: &mut ProofLang) -> Box<[&mut (Proof, Id)]> {
        node.args.iter_mut().collect()
    }
}

fn justify((p, x): (Proof, Id), j: Symbol) -> (Proof, Id) {
    let p2 = Rc::new(ProofObj::Rule(j));
    (Proof::compose(&p2, &p), x)
}

/// E-Matching

struct ProofMatcher;

impl Matcher<ProofAnalysis> for ProofMatcher {
    type SymG = ();

    // l*r*x, thus r is applied first.
    fn compose(_: &(), _: &()) {}
    fn inverse(_: &()) {}

    fn from_gvar(_: GVar) {}
    fn from_g(_: &Proof) {}

    fn expand(node: &ProofLang, fresh_gvar: impl FnMut() -> GVar) -> ((), Box<[()]>) {
        let arity = ProofAnalysis::children_mut(&mut node.clone()).len();
        ((), vec![(); arity].into_boxed_slice())
    }

    fn solve<'eg>(state: State<'eg, ProofAnalysis, Self>) -> Option<Subst<ProofAnalysis>> {
        Some(state.subst.into_iter().map(|(pvar, ((), i))| (pvar, (mk_refl(), i))).collect())
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
    let rules: Box<[(Pat, Pat)]> = rules.iter().map(|(rule_id, l, r)| {
        let annotation = Rc::new(ProofObj::Rule(*rule_id)).inverse();

        let l = l.clone();
        let r = Pattern::G(annotation, Box::new(r.clone()));

        (l, r)
    }).collect();

    let eg: &mut EGraph<ProofAnalysis> = &mut EGraph::new();
    let x1 = add_expr(&t1, eg);
    let x2 = add_expr(&t2, eg);

    eqsat::<_, ProofMatcher>(eg, &rules, n);
    let p = eg.get_g_between(x1.clone(), x2.clone()).unwrap();

    dbg!(eg.hashcons.len());
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
    eqsat_test(t1, t2, rules, 6);
}
