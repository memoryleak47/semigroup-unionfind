use crate::*;

pub trait Matcher<N: Analysis>: Sized {
    type SymG: Clone;

    // l*r*x, thus r is applied first.
    fn compose(l: &Self::SymG, r: &Self::SymG) -> Self::SymG;
    fn inverse(x: &Self::SymG) -> Self::SymG;

    fn from_gvar(id: GVar) -> Self::SymG;
    fn from_g(g: &N::G) -> Self::SymG;

    fn expand(node: &N::L, fresh_gvar: impl FnMut() -> GVar) -> (/*up*/Self::SymG, /*children*/Box<[Self::SymG]>);

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

pub fn symmatch<N: Analysis, M: Matcher<N>>(pat: &Pattern<N::L>, eg: &EGraph<N>) -> Vec<Subst<N>> {
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

fn ematch_impl<'eg, N: Analysis, M: Matcher<N>>((g, id): (M::SymG, Id), pat: &Pattern<N::L>, eg: &'eg EGraph<N>, mut state: State<'eg, N, M>) -> Vec<State<'eg, N, M>> {
    let id_v = alloc_gvar(&mut state);
    let g = M::compose(&g, &M::from_gvar(id_v));
    state.gs_constraints.insert(id_v, eg.get_leader_semilattice(id));

    // This handles subpatterns without pvars, i.e. terms.
    // Just an optimization, but required for constants/slot-vars,
    // as we need to call "canon" on consts in the pattern anyways.
    if is_term::<N>(pat) {
        let Some((g2, id2)) = eg.lookup_term(pat) else { return Vec::new() };
        if id != id2 { return Vec::new() }
        let cons = M::compose(&M::inverse(&g), &M::from_g(&g2));
        state.g_constraints.push(cons);
        return vec![state]
    }

    match pat {
        Pattern::PVar(v) => {
            if let Some((g2, id2)) = state.subst.get(v) {
                if id != *id2 { return Vec::new() }
                let cons = M::compose(&M::inverse(&g), &g2);
                state.g_constraints.push(cons);
            } else {
                state.subst.insert(*v, (g, id));
            }
            vec![state]
        },
        Pattern::Node(patnode, childpats) => {
            let mut states = Vec::new();
            for (gn, mut node) in eg.nodes_of_bare(id) {
                if !matches::<N>(&node, patnode) { continue }

                let mut state = state.clone();
                let (pexp, chexp) = M::expand(&node, || alloc_gvar(&mut state));

                // goal: g*id = Pattern::Node(patnode, childpats)
                // fact: gn*node = id
                // -> g*gn*node = Pattern::Node(patnode, childpats)

                // with expansion:
                // -> g*gn*pexp*node = Pattern::Node(patnode, childpats)

                let cons = M::compose(
                    &M::compose(&g, &M::from_g(&gn)),
                    &pexp
                );
                state.g_constraints.push(cons);

                let mut substates = vec![state.clone()];
                let children: Box<[(N::G, Id)]> = N::children_mut(&mut node).into_iter().map(|x| x.clone()).collect();
                for i in 0..childpats.len() {
                    for state in std::mem::take(&mut substates) {
                        let (chg, chi) = &children[i];
                        let chg = M::compose(&chexp[i], &M::from_g(&chg));
                        substates.extend(ematch_impl((chg, *chi), &childpats[i], eg, state));
                    }
                }
                states.extend(substates);
            }
            states
        },
    }
}

fn matches<N: Analysis>(n1: &N::L, n2: &N::L) -> bool {
    clear_node::<N>(n1) == clear_node::<N>(n2)
}

fn clear_node<N: Analysis>(n: &N::L) -> N::L {
    let mut n = n.clone();
    for c in N::children_mut(&mut n) {
        *c = (N::G::identity(), Id(0));
    }
    n
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

