use crate::*;

pub type Subst<N: Analysis> = HashMap<PVar, (N::G, Id)>;
pub type PVar = Symbol;

pub enum Pattern<L> {
    PVar(PVar),

    // We entirely ignore the children of the Node L here.
    // They are considered to be replaced by these pattern-children.
    Node(L, Box<[Pattern<L>]>),
}

pub fn ematch<N: Analysis>(id: Id, pat: &Pattern<N::L>, eg: &EGraph<N>) -> Vec<Subst<N>> {
    // TODO this already excludes some of the e-nodes of the e-class due to G things being in the way.
    let gid = (N::G::identity(), id);
    ematch_impl::<N>(gid, pat, eg, Subst::<N>::new())
}

pub fn ematch_impl<N: Analysis>(gid: (N::G, Id), pat: &Pattern<N::L>, eg: &EGraph<N>, subst: Subst<N>) -> Vec<Subst<N>> {
    match pat {
        Pattern::PVar(var) => {
            let mut subst = subst;
            if let Some(old_gid) = subst.insert(*var, gid.clone()) && !eg.is_equal(gid, old_gid) { return Vec::new() }
            vec![subst]
        },
        Pattern::Node(pn, pargs) => {
            let mut out = Vec::new();
            for (g, n) in eg.nodes_of(gid) {
                // If the g is "in the way", we have to discard the e-node.
                if g != N::G::identity() { continue }

                out.extend(ematch_node(&n, pn, pargs, eg, subst.clone()));
            }
            out
        },
    }
}

fn clear_node<N: Analysis>(n: &N::L) -> N::L {
    let mut n = n.clone();
    for c in N::children_mut(&mut n) {
        *c = (N::G::identity(), Id(0));
    }
    n
}

pub fn ematch_node<N: Analysis>(node: &N::L, patnode: &N::L, pat_args: &[Pattern<N::L>], eg: &EGraph<N>, subst: Subst<N>) -> Vec<Subst<N>> {
    if clear_node::<N>(node) != clear_node::<N>(patnode) { return Vec::new() }

    let mut node = node.clone();

    let mut out = vec![subst];
    for (c, cp) in N::children_mut(&mut node).into_iter().zip(pat_args) {
        for subst in std::mem::take(&mut out) {
            out.extend(ematch_impl::<N>(c.clone(), cp, eg, subst));
        }
    }
    out
}
