use crate::*;

pub type Rule<N: Analysis> = (Pattern<N::L>, Pattern<N::L>);

// Terms are just patterns that don't contain PVars.
pub type Term<N: Analysis> = Pattern<N::L>;

pub fn eqsat<N: Analysis>(term: Term<N>, rules: &[Rule<N>], n: usize) {
    let mut eg: EGraph<N> = EGraph::new();
    add_expr(&term, &mut eg);

    for _ in 0..n {
        let mut matches = Vec::new();
        for (rule_id, (lhs, rhs)) in rules.iter().enumerate() {
            for i in eg.classes() {
                let matches_ = ematch(i, lhs, &eg);
                if matches_.len() > 0 {
                    matches.push((rule_id, i, matches_));
                }
            }
        }

        for (rule_id, i, matches_) in matches {
            for subst in matches_ {
                let (lhs, rhs) = &rules[rule_id];
                let l = instantiate(lhs, &mut eg, &subst);
                let r = instantiate(lhs, &mut eg, &subst);
                eg.uf.union(l, r);
            }
        }
        eg.rebuild();
    }
}

fn add_expr<N: Analysis>(t: &Term<N>, eg: &mut EGraph<N>) -> (N::G, Id) {
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
