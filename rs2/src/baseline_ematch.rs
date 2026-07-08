use crate::*;

pub fn baseline_ematch<N: Analysis>(id: Id, pat: &Pattern<N>, eg: &EGraph<N>) -> Vec<Subst<N>> {
    // TODO this already excludes some of the e-nodes of the e-class due to G things being in the way.
    let gid = (N::G::identity(), id);
    ematch_impl::<N>(gid, pat, eg, Subst::<N>::new())
}

fn ematch_impl<N: Analysis>(gid: (N::G, Id), pat: &Pattern<N>, eg: &EGraph<N>, subst: Subst<N>) -> Vec<Subst<N>> {
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
        Pattern::G(..) => unimplemented!(),
    }
}

fn ematch_node<N: Analysis>(node: &N::L, patnode: &N::L, pat_args: &[Pattern<N>], eg: &EGraph<N>, subst: Subst<N>) -> Vec<Subst<N>> {
    if !matches::<N>(node, patnode) { return Vec::new() }

    let mut node = node.clone();

    let mut out = vec![subst];
    for (c, cp) in N::children_mut(&mut node).into_iter().zip(pat_args) {
        for subst in std::mem::take(&mut out) {
            out.extend(ematch_impl::<N>(c.clone(), cp, eg, subst));
        }
    }
    out
}
