use crate::*;
use std::rc::Rc;
use std::collections::HashMap;

#[derive(Clone, PartialEq, Eq, Hash)]
enum ProofObj {
    Refl,
    Sym(Proof),
    Trans(Proof, Proof),
    Congr(Box<[Proof]>),
}

#[derive(Clone, PartialEq, Eq, Hash)]
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

struct ProofLang {
    f: Symbol,
    args: Box<[Id]>,
}

struct ProofData {
    // This helps to reconstruct the "original term" for every Id.
    syn: HashMap<Id, ProofLang>,

    // These are all the proofs proving that all the Ids of syn.keys() are equal.
    // It's at least a spanning tree, but maybe more.
    proofs: Vec<(Id, Id, Proof)>,
}

impl Semilattice for ProofData {
    type G = Proof;

    fn act(g: &Self::G, s: &Self) -> Self {
        todo!()
    }

    fn merge(&mut self, other: Self) -> bool {
        if other.syn.is_empty() && other.proofs.is_empty() { return false }
        self.syn.extend(other.syn);
        self.proofs.extend(other.proofs);
        true
    }

    fn insert_self_edge(&mut self, g: Self::G) {
        self.proofs.push((todo!(), todo!(), g));
    }

    fn contains_self_edge(&self, g: &Self::G) -> bool {
        todo!()
    }
}
