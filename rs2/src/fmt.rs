use crate::*;

impl<N: Analysis> Debug for Pattern<N>
        where N::L: Debug, N::G: Debug {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        use Pattern::*;
        match self {
            PVar(v) => write!(f, "{v}"),
            Node(n, subs) => write!(f, "({n:?} >< {subs:?})"),
            G(g, pat) => write!(f, "{g:?} * {pat:?}"),
        }
    }
}
