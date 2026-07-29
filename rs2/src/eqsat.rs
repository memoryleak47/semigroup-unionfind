use crate::*;

pub type Rule<N: Analysis> = (Pattern<N>, Pattern<N>);

pub type GeneralRule<N: Analysis> = (Pattern<N>, Applier<N>);
pub type Applier<N: Analysis> = Box<dyn Fn((N::G, Id), Subst<N>, &mut EGraph<N>)>;

pub fn pattern_applier<N: Analysis + 'static>(rhs_pat: Pattern<N>) -> Applier<N> {
    Box::new(move |lhs_eclass, subst, eg| {
        let rhs_eclass = instantiate(&rhs_pat, eg, &subst);
        eg.union(lhs_eclass, rhs_eclass);
    })
}

// Terms are just patterns that don't contain PVars.
pub type Term<N: Analysis> = Pattern<N>;

pub fn eqsat<N: Analysis, M: Matcher<N>>(eg: &mut EGraph<N>, rules: &[Rule<N>], n: usize) {
    for _ in 0..n {
        let mut matches = Vec::new();
        for (lhs, _) in rules.iter() {
            matches.push(ematch::<N, M>(lhs, eg));
        }

        for (matches_inner, (lhs, rhs)) in matches.into_iter().zip(rules) {
            for subst in matches_inner {
                let lhs_eclass = instantiate(lhs, eg, &subst);
                let rhs_eclass = instantiate(rhs, eg, &subst);
                eg.union(lhs_eclass, rhs_eclass);
            }
        }
        eg.rebuild();
    }
}

pub fn general_eqsat<N: Analysis, M: Matcher<N>>(eg: &mut EGraph<N>, rules: &[GeneralRule<N>], n: usize) {
    for _ in 0..n {
        let mut matches = Vec::new();
        for (lhs, _) in rules.iter() {
            matches.push(ematch::<N, M>(lhs, eg));
        }

        for (matches_inner, (lhs, applier)) in matches.into_iter().zip(rules) {
            for subst in matches_inner {
                let lhs_eclass = instantiate(lhs, eg, &subst);
                applier(lhs_eclass, subst, eg);
            }
        }
        eg.rebuild();
    }
}

pub fn add_expr<N: Analysis>(t: &Term<N>, eg: &mut EGraph<N>) -> (N::G, Id) {
    instantiate(t, eg, &Subst::<N>::new())
}

fn instantiate<N: Analysis>(pat: &Pattern<N>, eg: &mut EGraph<N>, subst: &Subst<N>) -> (N::G, Id) {
    match pat {
        Pattern::PVar(var) => subst[var].clone(),
        Pattern::Node(n, pargs) => {
            let mut n = n.clone();
            for (c, nc) in N::children_mut(&mut n).into_iter().zip(pargs) {
                *c = instantiate(nc, eg, subst);
            }
            eg.add(&n)
        },
        Pattern::G(g, pat) => {
            let (g2, x) = instantiate(pat, eg, subst);
            let g = N::G::compose(&g, &g2);
            (g, x)
        },
    }
}
