use crate::*;

// Things that might help for the lean case study.

pub struct RecExpr<L> {
    inner: Vec<L>,
}

pub type RecExprPattern<L> = RecExpr<ENodeOrVar<L>>;

pub enum ENodeOrVar<L> {
    ENode(L),
    Var(PVar),
}

pub fn pattern_to_recexpr_pattern<N: Analysis>(x: &Pattern<N>) -> RecExprPattern<N::L> {
    let mut inner = Vec::new();
    pattern_to_recexpr_pattern_impl(x, &mut inner);
    RecExprPattern { inner }
}

// pushes the pattern x fully onto the thing.
fn pattern_to_recexpr_pattern_impl<N: Analysis>(x: &Pattern<N>, inner: &mut Vec<ENodeOrVar<N::L>>) {
    match x {
        Pattern::PVar(v) => inner.push(ENodeOrVar::Var(*v)),
        Pattern::Node(n, children) => {
            let mut children2 = Vec::new();
            for c in children {
                pattern_to_recexpr_pattern_impl(c, inner);
                children2.push(inner.len()-1);
            }
            let mut n = n.clone();
            for (cptr, c2) in N::children_mut(&mut n).into_iter().zip(children2.into_iter()) {
                *cptr = (N::G::identity(), Id(c2));
            }
            inner.push(ENodeOrVar::ENode(n));
        },
        Pattern::G(..) => panic!("This should not happen"),
    }
}

pub fn recexpr_pattern_to_pattern<N: Analysis>(x: &RecExprPattern<N::L>) -> Pattern<N> {
    recexpr_pattern_to_pattern_impl(x, x.inner.len()-1)
}

fn recexpr_pattern_to_pattern_impl<N: Analysis>(x: &RecExprPattern<N::L>, i: usize) -> Pattern<N> {
    match &x.inner[i] {
        ENodeOrVar::ENode(n) => {
            let mut n = n.clone();
            let mut args = Vec::new();
            for c in N::children_mut(&mut n) {
                let sub = recexpr_pattern_to_pattern_impl(x, c.1.0);
                args.push(sub);
                *c = (N::G::identity(), Id(0));
            }
            Pattern::Node(n, args.into_boxed_slice())
        }
        ENodeOrVar::Var(v) => Pattern::PVar(*v),
    }
}
