use crate::*;

type Subst = HashMap<PVar, Id>;
type PVar = Symbol;

pub enum Pattern<L> {
    PVar(PVar),

    // We entirely ignore the children of the Node L here.
    // They are considered to be replaced by these pattern-children.
    Node(L, Box<[Pattern<L>]>),
}

pub fn ematch<N: Analysis>(id: Id, pat: &Pattern<N::L>, eg: &EGraph<N>) -> Vec<Subst> {
    ematch_impl(id, pat, eg, Subst::new())
}

pub fn ematch_impl<N: Analysis>(id: Id, pat: &Pattern<N::L>, eg: &EGraph<N>, subst: Subst) -> Vec<Subst> {
    match pat {
        Pattern::PVar(var) => {
            let mut subst = subst;
            if let Some(old_id) = subst.insert(*var, id) && old_id != id { return Vec::new() }
            vec![subst]
        },
        Pattern::Node(pn, pargs) => {
            let mut out = Vec::new();
            for (g, n) in eg.nodes_of_bare(id) {
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

pub fn ematch_node<N: Analysis>(node: &N::L, patnode: &N::L, pat_args: &[Pattern<N::L>], eg: &EGraph<N>, subst: Subst) -> Vec<Subst> {
    if clear_node::<N>(node) != clear_node::<N>(patnode) { return Vec::new() }

    let mut node = node.clone();

    let mut out = vec![subst];
    for ((_, c), cp) in N::children_mut(&mut node).into_iter().zip(pat_args) {
        for subst in std::mem::take(&mut out) {
            out.extend(ematch_impl(*c, cp, eg, subst));
        }
    }
    out
}
