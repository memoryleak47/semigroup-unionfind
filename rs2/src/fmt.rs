use crate::*;

impl<N: Analysis> Debug for Pattern<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        use Pattern::*;
        match self {
            PVar(v) => write!(f, "{v}"),
            Node(n, subs) => {
                let subs = subs.iter().map(|x| format!("{x:?}")).collect::<Box<[_]>>();
                write!(f, "{}", N::prettyprint(n, subs))
            },
            G(g, pat) => write!(f, "{g:?} * {pat:?}"),
        }
    }
}
