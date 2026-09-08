use crate::*;

pub type Subst<N: Analysis> = HashMap<PVar, (N::G, Id)>;
pub type PVar = Symbol;

pub enum Pattern<N: Analysis> {
    PVar(PVar),

    // We entirely ignore the children of the Node L here.
    // They are considered to be replaced by these pattern-children.
    Node(N::L, Box<[Pattern<N>]>),

    G(N::G, Box<Pattern<N>>),
}

pub fn is_term<N: Analysis>(pat: &Pattern<N>) -> bool {
    match pat {
        Pattern::PVar(_) => false,
        Pattern::Node(_, subpats) => subpats.iter().all(is_term::<N>),
        Pattern::G(..) => false,
    }
}

pub enum Skel<N: Analysis> {
    PVar(Id),
    Node(N::L, Box<[SkelEdge<N>]>),
}
pub type SkelEdge<N: Analysis> = (N::G, N::S, Skel<N>);

// Matches in the e-graph while disregarding the G annotations
pub fn skeleton_ematch<N: Analysis>(eg: &EGraph<N>) -> (HashMap<PVar, Id>, Skel<N>) {
    todo!()
}

impl<N: Analysis> Clone for Pattern<N> {
    fn clone(&self) -> Self {
        match self {
            Pattern::PVar(v) => Pattern::PVar(*v),
            Pattern::Node(n, children) => Pattern::Node(n.clone(), children.clone()),
            Pattern::G(g, pat) => Pattern::G(g.clone(), pat.clone()),
        }
    }
}

impl<N: Analysis> PartialEq for Pattern<N> {
    fn eq(&self, other: &Pattern<N>) -> bool {
        match (self, other) {
            (Pattern::PVar(v1), Pattern::PVar(v2)) => v1 == v2,
            (Pattern::Node(n1, children1), Pattern::Node(n2, children2)) => n1 == n2 && children1 == children2,
            (Pattern::G(g1, pat1), Pattern::G(g2, pat2)) => g1 == g2 && pat1 == pat2,
            _ => false,
        }
    }
}
impl<N: Analysis> Eq for Pattern<N> {}

impl<N: Analysis> Hash for Pattern<N> {
    fn hash<H>(&self, state: &mut H) where H: std::hash::Hasher {
        match self {
            Pattern::PVar(v) => (0u32, v).hash(state),
            Pattern::Node(n, x) => (1u32, n, x).hash(state),
            Pattern::G(g, children) => (2u32, g, children).hash(state),
        }
    }
}
