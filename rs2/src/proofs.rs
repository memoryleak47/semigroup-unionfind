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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Proof(Rc<ProofObj>);

impl Group for Proof {
    fn identity() -> Proof {
        Proof(Rc::new(ProofObj::Refl))
    }

    fn compose(l: &Proof, r: &Proof) -> Proof {
        Proof(Rc::new(ProofObj::Trans(l.clone(), r.clone())))
    }

    fn inverse(&self) -> Proof {
        Proof(Rc::new(ProofObj::Sym(self.clone())))
    }
}

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
struct ProofLang {
    f: Symbol,
    args: Box<[(Proof, Id)]>,
}

#[derive(Clone)]
struct ProofData {
    // This helps to reconstruct the "original term" for every Id.
    syn: HashMap<Id, ProofLang>,
}

impl Semilattice for ProofData {
    type G = Proof;

    fn act(g: &Self::G, s: &Self) -> Self {
        s.clone()
    }

    fn merge(&mut self, other: Self) -> bool {
        let mut dirty = false;
        for (k, n) in &other.syn {
            if self.syn.contains_key(&k) { continue }
            self.syn.insert(*k, n.clone());
            dirty = true
        }

        dirty
    }

    fn insert_self_edge(&mut self, g: Self::G) {
        // We ignore redundant proofs. We assume proof irrelevance.
    }

    fn contains_self_edge(&self, g: &Self::G) -> bool {
        true
    }
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
            args.push((p, y));
        }
        let p = Proof(Rc::new(
            ProofObj::Congr(proofs.into())
        ));
        let n = ProofLang {
            f: n.f,
            args: args.into(),
        };
        (p, n)
    }

    fn mk(n: &Self::L, id: Id, uf: &Unionfind<Self::S>) -> Self::S {
        ProofData {
            syn: std::iter::once((id, n.clone())).collect(),
        }
    }
}

#[test]
fn test_proofs() {
    let eg: &mut EGraph<ProofAnalysis> = &mut EGraph::new();

    let asym = Symbol::new("a");
    let bsym = Symbol::new("b");

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

    eg.union(justify(a.clone(), "hey"), b.clone());

    dbg!(eg.find(a));
    dbg!(eg.find(b));
    assert!(false);
}

fn justify((p, x): (Proof, Id), j: &str) -> (Proof, Id) {
    let j = Symbol::from(j);
    let p2 = Proof(Rc::new(ProofObj::User(j)));
    (Proof::compose(&p, &p2), x)
}
