use crate::*;

pub trait Matcher<N: Analysis>: Sized {
    type SymG: Clone;

    // l*r*x, thus r is applied first.
    fn compose(l: &Self::SymG, r: &Self::SymG) -> Self::SymG;
    fn inverse(x: &Self::SymG) -> Self::SymG;

    fn from_gvar(id: GVar) -> Self::SymG;
    fn from_g(g: &N::G) -> Self::SymG;

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
    let g0 = M::from_gvar(gv0);

    let mut states = Vec::new();
    for x in eg.classes() {
        let g0 = g0.clone();
        let state = state.clone();
        states.extend(ematch_impl((g0, x), pat, eg, state));
    }

    states.into_iter().map(M::solve).flatten().collect()
}

fn ematch_impl<'eg, N: Analysis, M: Matcher<N>>(gid: (M::SymG, Id), pat: &Pattern<N::L>, eg: &'eg EGraph<N>, mut state: State<'eg, N, M>) -> Vec<State<'eg, N, M>> {
    let id_v = alloc_gvar(&mut state);
    let gid = (M::compose(&gid.0, &M::from_gvar(id_v)), gid.1);
    state.gs_constraints.insert(id_v, eg.get_leader_semilattice(gid.1));

    match pat {
        Pattern::PVar(v) => {
            if let Some((g, i)) = state.subst.get(v) {
                if *i != gid.1 { return Vec::new() }
                let cons = M::compose(&M::inverse(&gid.0), &g);
                state.g_constraints.push(cons);
            } else {
                state.subst.insert(*v, gid);
            }
            vec![state]
        },
        Pattern::Node(n, childpats) => {
            todo!()
        },
    }
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
