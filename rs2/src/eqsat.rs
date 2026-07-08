use crate::*;

pub type Rule<N: Analysis> = (Pattern<N::L>, Pattern<N::L>);

// Terms are just patterns that don't contain PVars.
pub type Term<N: Analysis> = Pattern<N::L>;

pub fn eqsat<N: Analysis, M: Matcher<N>>(term: Term<N>, rules: &[Rule<N>], n: usize) {
    let mut eg: EGraph<N> = EGraph::new();
    add_expr(&term, &mut eg);

    for _ in 0..n {
        let mut matches = Vec::new();
        for (lhs, rhs) in rules.iter() {
            matches.push(ematch::<N, M>(lhs, &eg));
        }

        for (matches_inner, (lhs, rhs)) in matches.into_iter().zip(rules) {
            for subst in matches_inner {
                let l = instantiate(lhs, &mut eg, &subst);
                let r = instantiate(lhs, &mut eg, &subst);
                eg.uf.union(l, r);
            }
        }
        eg.rebuild();
    }
}

pub fn add_expr<N: Analysis>(t: &Term<N>, eg: &mut EGraph<N>) -> (N::G, Id) {
    instantiate(t, eg, &Subst::<N>::new())
}

fn instantiate<N: Analysis>(pat: &Pattern<N::L>, eg: &mut EGraph<N>, subst: &Subst<N>) -> (N::G, Id) {
    match pat {
        Pattern::PVar(var) => subst[var].clone(),
        Pattern::Node(n, pargs) => {
            let mut n = n.clone();
            for (c, nc) in N::children_mut(&mut n).into_iter().zip(pargs) {
                *c = instantiate(nc, eg, subst);
            }
            eg.add(&n)
        },
    }
}
