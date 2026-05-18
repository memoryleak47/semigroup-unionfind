use crate::*;
use std::rc::Rc;
use std::collections::HashMap;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum ProofObj {
    Refl,
    Sym(Proof),
    Trans(Proof, Proof),
    Congr(Box<[Proof]>),
    User(Symbol), // the symbol contains information about the rule application
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

#[derive(Clone)]
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

    fn canon(n: &Self::L, uf: &Unionfind<Self::S>) -> (Self::G, Self::L) {
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
        (p, n)
    }

    fn mk(n: &Self::L, id: Id, uf: &Unionfind<Self::S>) -> Self::S { ProofData }
}
fn justify((p, x): (Proof, Id), j: &str) -> (Proof, Id) {
    let j = Symbol::from(j);
    let p2 = Rc::new(ProofObj::User(j));
    (Proof::compose(&p, &p2), x)
}

/// E-Matching

#[derive(PartialEq, Eq, Hash, Clone)]
enum Pattern {
    PVar(PVar),
    Node(Symbol, Box<[Pattern]>),
}

type PVar = String;
type Subst = HashMap<PVar, Id>;
type L = ProofLang;
type G = Proof;

// semantics:
// a := applying the subst to the pattern
// b := canonical term of x
// proof translates a to b
fn ematch(x: Id, pat: &Pattern, eg: &EGraph<ProofAnalysis>) -> Vec<(Proof, Subst)> {
    ematch_impl(x, pat, eg, &Subst::new())
}

fn ematch_impl(x: Id, pat: &Pattern, eg: &EGraph<ProofAnalysis>, subst: &Subst) -> Vec<(Proof, Subst)> {
    match pat {
        Pattern::PVar(v) => {
            let mut subst = subst.clone();
            if let Some(a) = subst.get(v) {
                if *a != x { return Vec::new() }
            } else {
                subst.insert(v.clone(), x);
            }
            vec![(G::identity(), subst)]
        },
        Pattern::Node(f, subpats) => {
            let mut out = Vec::new();
            for (g, n) in eg.nodes_of_bare(x) {
                // g*n = i
                if n.f != *f { continue }

                let mut acc = vec![(g, subst.clone())];
                for ((grefl, subid), subpat) in n.args.iter().zip(subpats.iter()) {
                    assert_eq!(*grefl, G::identity());
                    for (g, subst) in std::mem::take(&mut acc) {
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

fn eqsat(eg: &mut EGraph<ProofAnalysis>, rules: &[(Pattern, Pattern)], n: usize) {
    for _ in 0..n {
        for (rule_id, (lhs, rhs)) in rules.iter().enumerate() {
            for x in eg.classes() {
                for (p, subst) in ematch(x, lhs, eg) {
                    let lhs = instantiate(lhs, &subst, eg);
                    let rhs = instantiate(rhs, &subst, eg);
                    eg.union(justify(lhs.clone(), &format!("{rule_id}")), rhs.clone());
                }
            }
        }
    }
}

/// Tests

#[test]
fn test_proofs() {
    let eg: &mut EGraph<ProofAnalysis> = &mut EGraph::new();

    let asym = Symbol::new("a");
    let bsym = Symbol::new("b");
    let csym = Symbol::new("c");

    let fsym = Symbol::new("f");

    let a = eg.add(&ProofLang {
        f: asym,
        args: Box::new([]),
    });

    let b = eg.add(&ProofLang {
        f: bsym,
        args: Box::new([]),
    });

    let fa = eg.add(&ProofLang {
        f: fsym,
        args: Box::new([a.clone()]),
    });

    let fb = eg.add(&ProofLang {
        f: fsym,
        args: Box::new([b.clone()]),
    });

    eg.union(justify(a.clone(), "a = b"), b.clone());

    dbg!(eg.get_g_between(fa.clone(), fb.clone()));
}


