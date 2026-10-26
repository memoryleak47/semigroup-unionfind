use super::*;

fn enodes_applied(gid: (SlotMap, Id), eg: &EGraph<Slotted>) -> Vec<SlottedLang> {
    eg.nodes_of(gid).iter().map(|(x, y)| apply(x, y)).collect()
}

use std::sync::atomic::{AtomicUsize, Ordering};

static SLOT_COUNTER: AtomicUsize = AtomicUsize::new(10_000);

fn fresh_slot() -> Slot {
    SLOT_COUNTER.fetch_add(1, Ordering::SeqCst)
}

// private slots of `n` are supposed to not be part of `map.keys()`.
fn apply(map: &SlotMap, n: &SlottedLang) -> SlottedLang {
    let mut map: HashMap<Slot, Slot> = map.iter().collect();
    let mut n = n.clone();
    
    for p in get_slots_mut(&mut n) {
        if !map.contains_key(&p) {
            map.insert(*p, fresh_slot());
        }
        *p = map[p];
    }
    n
}

pub fn final_subst(st: State) -> Subst<Slotted> {
    let mut subst = st.subst;
    for (_pvar, (m, _id)) in &mut subst {
        *m = SlotMap::mk(m.iter().map(|(a, b)| {
            if let Some(b2) = st.relation.get(&b) { (a, *b2) }
            else { (a, b) }
        }));
    }
    subst
}

fn get_slots_mut(n: &mut SlottedLang) -> Box<[&mut Slot]> {
    use SlottedLang::*;
    match n {
        Lam(v, b) => std::iter::once(v).chain(b.0.vals_mut()).collect(),
        App(x, y) => x.0.vals_mut().chain(y.0.vals_mut()).collect(),
        Var(v) => Box::new([v]),
        Let(t, v, b) => t.0.vals_mut().chain(std::iter::once(v)).chain(b.0.vals_mut()).collect(),
        Number(_)|Symbol(_) => Box::new([]),
    }
}

#[derive(Clone, Default)]
pub struct State {
    pub relation: HashMap<Slot, Slot>, // relates our fresh slots (keys) to the pattern slots (values).
    pub subst: Subst<Slotted>,
}

type Pat = Pattern<Slotted>;

fn try_relate(x: Slot, y: Slot, st: &mut State) -> bool {
    if let Some(yy) = st.relation.get(&x) { return *yy == y }

    if st.relation.values().any(|yy| *yy == y) { return false }

    st.relation.insert(x, y);
    true
}

fn ematch_node(n: &SlottedLang, n_pattern: &SlottedLang, children_pattern: &[Pat], mut st: State, eg: &EGraph<Slotted>) -> Vec<State> {
    use SlottedLang::*;
    match (n, n_pattern) {
        (Lam(x, b), Lam(xp, _)) => {
            if !try_relate(*x, *xp, &mut st) { return Vec::new() }
            ematch_impl(b.clone(), &children_pattern[0], st, eg)
        },
        (App(x, y), App(..)) => {
            let mut out = Vec::new();
            for st in ematch_impl(x.clone(), &children_pattern[0], st, eg) {
                out.extend(ematch_impl(y.clone(), &children_pattern[1], st, eg));
            }
            out
        },
        (Var(x), Var(y)) => {
            if !try_relate(*x, *y, &mut st) { return Vec::new() }
            vec![st]
        },
        (Number(x), Number(y)) => if x == y { vec![st] } else { Vec::new() },
        (Symbol(x), Symbol(y)) => if x == y { vec![st] } else { Vec::new() },
        (Let(t, v, b), Let(_, vp, _)) => {
            if !try_relate(*v, *vp, &mut st) { return Vec::new() }
            let mut out = Vec::new();
            for st in ematch_impl(t.clone(), &children_pattern[0], st, eg) {
                out.extend(ematch_impl(b.clone(), &children_pattern[1], st, eg));
            }
            out
            
        },
        _ => Vec::new(),
    }
}

pub fn ematch_impl(gid: (SlotMap, Id), pat: &Pat, st: State, eg: &EGraph<Slotted>) -> Vec<State> {
    match pat {
        Pattern::PVar(v) => {
            let mut st = st.clone();
            if let Some(old) = st.subst.insert(*v, gid.clone()) && !eg.is_equal(gid, old) {
                return Vec::new()
            }
            vec![st]
        },
        Pattern::Node(n_pat, children_pat) => {
            let mut out = Vec::new();
            for n in enodes_applied(gid, eg) {
                out.extend(ematch_node(&n, n_pat, children_pat, st.clone(), eg));
            }
            out
        },
        Pattern::G(..) => unreachable!(),
    }
}
