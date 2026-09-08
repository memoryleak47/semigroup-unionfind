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

pub fn ematch_all<N: Analysis>(eg: &EGraph<N>, pat: &Pattern<N>) -> Vec<Subst<N>> {
    let mut vec = Vec::new();
    for i in eg.classes() {
        vec.extend(N::ematch(eg, i, pat));
    }
    vec
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
    Node(N::G, N::L, Box<[(N::G, N::S, Skel<N>)]>),
}

// Matches in the e-graph while disregarding the G annotations.
pub fn skeleton_ematch<N: Analysis>(eg: &EGraph<N>, id: Id, pat: &Pattern<N>) -> Vec<(HashMap<PVar, Id>, Skel<N>)> {
    ematch_impl(id, pat, eg, HashMap::new())
}

fn ematch_impl<N: Analysis>(id: Id, pat: &Pattern<N>, eg: &EGraph<N>, subst: HashMap<PVar, Id>) -> Vec<(HashMap<PVar, Id>, Skel<N>)> {
    match pat {
        Pattern::PVar(var) => {
            let mut subst = subst;
            if let Some(old_id) = subst.insert(*var, id) && id != old_id { return Vec::new() }
            vec![(subst, Skel::PVar(id))]
        },
        Pattern::Node(pn, pargs) => {
            let mut out = Vec::new();
            for (g, n) in eg.nodes_of_bare(id) {
                out.extend(ematch_node(g, &n, pn, pargs, eg, subst.clone()));
            }
            out
        },
        Pattern::G(..) => unimplemented!(),
    }
}

fn ematch_node<N: Analysis>(g_base: N::G, node: &N::L, patnode: &N::L, pat_args: &[Pattern<N>], eg: &EGraph<N>, subst: HashMap<PVar, Id>) -> Vec<(HashMap<PVar, Id>, Skel<N>)> {
    if !matches::<N>(node, patnode) { return Vec::new() }

    let mut node = node.clone();

    let mut out: Vec<(_, Vec<(N::G, N::S, Skel<N>)>)> = vec![(subst, Vec::new())];
    for ((cg, cid), cp) in N::children_mut(&mut node).into_iter().zip(pat_args) {
        for (subst, children) in std::mem::take(&mut out) {
            for (sub_subst, sub_skel) in ematch_impl::<N>(*cid, cp, eg, subst) {
                let mut children = children.clone();
                children.push((cg.clone(), eg.uf.get_id_semilattice(*cid), sub_skel));
                out.push((sub_subst, children));
            }
        }
    }
    let out = out.into_iter().map(|(subst, children)| (subst, Skel::Node(g_base.clone(), node.clone(), children.into_boxed_slice()))).collect();
    out
}

pub fn matches<N: Analysis>(n1: &N::L, n2: &N::L) -> bool {
    clear_node::<N>(n1) == clear_node::<N>(n2)
}

fn clear_node<N: Analysis>(n: &N::L) -> N::L {
    let mut n = n.clone();
    for c in N::children_mut(&mut n) {
        *c = (N::G::identity(), Id(0));
    }
    n
}

/// impls ///

impl<N: Analysis> Clone for Skel<N> {
    fn clone(&self) -> Self {
        match self {
            Skel::PVar(id) => Skel::PVar(*id),
            Skel::Node(g, n, children) => Skel::Node(g.clone(), n.clone(), children.clone()),
        }
    }
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
