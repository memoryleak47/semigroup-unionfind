use crate::*;

pub trait Matcher<N: Analysis>: Sized {
    type SymG: Clone;

    fn from_mvar(id: GVar) -> Self::SymG;

    fn expand(node: &N::L) -> (/*up*/Self::SymG, /*children*/Box<[Self::SymG]>);

    fn solve<'eg>(state: State<'eg, N, Self>) -> Option<Subst<N>>;
}

pub type GVar = usize;

pub struct State<'eg, N: Analysis, M: Matcher<N>> {
    pub g_constraints: Vec<M::SymG>,
    pub gs_constraints: HashMap<GVar, &'eg N::S>,
    pub subst: HashMap<PVar, (M::SymG, Id)>,
    gvar_counter: usize,
}

fn alloc_gvar<N: Analysis, M: Matcher<N>>(state: &mut State<N, M>) -> GVar {
    let x = state.gvar_counter;
    state.gvar_counter += 1;
    x
}

fn ematch<N: Analysis, M: Matcher<N>>(pat: &Pattern<N::L>, eg: &EGraph<N>) -> Vec<Subst<N>> {
    let mut state: State<N, M> = Default::default();
    let gv0 = alloc_gvar(&mut state);
    let g0 = M::from_mvar(gv0);

    let mut states = Vec::new();
    for x in eg.classes() {
        let g0 = g0.clone();
        let state = state.clone();
        states.extend(ematch_impl((g0, x), pat, eg, state));
    }

    states.into_iter().map(M::solve).flatten().collect()
}

fn ematch_impl<'eg, N: Analysis, M: Matcher<N>>(gid: (M::SymG, Id), pat: &Pattern<N::L>, eg: &'eg EGraph<N>, state: State<'eg, N, M>) -> Vec<State<'eg, N, M>> {
    todo!()
}

// boring stuff
impl<'eg, N: Analysis, M: Matcher<N>> Clone for State<'eg, N, M> {
    fn clone(&self) -> Self {
        State {
            g_constraints: self.g_constraints.clone(),
            gs_constraints: self.gs_constraints.clone(),
            subst: self.subst.clone(),
            gvar_counter: self.gvar_counter,
        }
    }
}

impl<'eg, N: Analysis, M: Matcher<N>> Default for State<'eg, N, M> {
    fn default() -> Self {
        State {
            g_constraints: Default::default(),
            gs_constraints: Default::default(),
            subst: Default::default(),
            gvar_counter: Default::default(),
        }
    }
}
