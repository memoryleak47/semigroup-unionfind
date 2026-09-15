use crate::*;

type Slot = usize;

/// SlotMap ///

// invariant: injective. Its set of keys typically comes from the public slots of some e-class.
#[derive(Clone, Hash, PartialEq, Eq, Debug)]
struct SlotMap {
    v: Vec<(Slot, Slot)>
}

impl SlotMap {
    pub fn mk(it: impl Iterator<Item=(Slot, Slot)>) -> SlotMap {
        let mut v: Vec<(Slot, Slot)> = it.collect();
        v.sort_by_key(|(x, _)| *x);
        SlotMap { v }
    }

    pub fn keys(&self) -> Vec<Slot> { self.v.iter().map(|(k, _)| *k).collect() }
    pub fn values(&self) -> Vec<Slot> { self.v.iter().map(|(_, v)| *v).collect() }

    pub fn get(&self, x: Slot) -> Option<Slot> {
        if let Some((_, b)) = self.v.iter().find(|(a, b)| *a == x) { Some(*b) }
        else { None }
    }

    pub fn iter(&self) -> impl Iterator<Item=(Slot,Slot)> {
        self.v.iter().copied()
    }
}

impl Group for SlotMap {
    // TODO this identity is wrong. Either we build a "global identity", or we don't require it.
    fn identity() -> SlotMap { SlotMap::mk(std::iter::empty()) }

    // l*(r*_)
    // This is partial compose!
    fn compose(l: &SlotMap, r: &SlotMap) -> SlotMap {
        let mut v = Vec::new();
        for (x, y) in r.iter() {
            if let Some(z) = l.get(y) {
                v.push((x, z));
            }
        }
        SlotMap { v }
    }

    fn inverse(&self) -> SlotMap {
        SlotMap::mk(self.iter().map(|(x, y)| (y, x)))
    }
}

/// SlottedData ///

#[derive(PartialEq, Eq, Debug, Clone)]
struct SlottedData {
    slots: HashSet<Slot>,
    group: HashSet<SlotMap>,
}

impl Semilattice for SlottedData {
    type G = SlotMap;

    fn act(g: &Self::G, s: &Self) -> Self {
        let slots = s.slots.iter().flat_map(|x| g.get(*x)).collect();
        let group = s.group.iter().map(|p| {
            // We know p*s = s and s' = g*s.
            // We want to return p' with p'*s' = s'.
            // p*s = s -> p*g⁻¹*s' = g⁻¹*s' -> g*p*g⁻¹*s' = s'
            SlotMap::compose(&SlotMap::compose(&g, &p), &g.inverse())
        }).collect();
        SlottedData { slots, group }
    }

    fn merge(&mut self, other: Self) -> bool {
        let slots = &self.slots & &other.slots;
        let group = &self.group | &other.group;
        let mut out = SlottedData { slots, group };
        complete_data(&mut out);
        if &out == self { return false }
        *self = out;
        true
    }

    fn insert_self_edge(&mut self, g: Self::G) {
        self.group.insert(g);
        complete_data(self);
    }

    fn contains_self_edge(&self, g: &Self::G) -> bool {
        let Some(g) = restrict(g, &self.slots) else { return false };
        self.group.contains(&g)
    }
}

// Returns None, if some slots go in or out of `slots`.
fn restrict(m: &SlotMap, slots: &HashSet<Slot>) -> Option<SlotMap> {
    let mut out = Vec::new();
    for (x, y) in m.iter() {
        let sx = slots.contains(&x);
        let sy = slots.contains(&y);
        if sx != sy { return None }
        if sx {
            out.push((x, y));
        }
    }
    Some(SlotMap::mk(out.into_iter()))
}

fn complete_data(d: &mut SlottedData) {
    // fix redundancies & symmetries.
    loop {
        let mut dirty = false;
        for old_p in std::mem::take(&mut d.group) {
            let mut p = Vec::new();
            for (x, y) in old_p.iter() {
                let contains_x = d.slots.contains(&x);
                let contains_y = d.slots.contains(&y);
                match (contains_x, contains_y) {
                    (true, true) => { p.push((x, y)); },
                    (false, true) => { d.slots.remove(&y); dirty = true; },
                    (true, false) => { d.slots.remove(&x); dirty = true; },
                    (false, false) => { dirty = true; },
                }
            }
            let p = SlotMap::mk(p.into_iter());
            d.group.insert(p);
        }
        if !dirty { break }
    }

    // saturate group.
    d.group.insert(SlotMap::identity());
    loop {
        let old_group = std::mem::take(&mut d.group);
        for p1 in &old_group {
            for p2 in &old_group {
                d.group.insert(SlotMap::compose(p1, p2));
            }
        }
        if d.group.len() == old_group.len() { break }
    }
}

/// SlottedLang ///

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
enum SlottedLang {
    // For simplicity, we represent (lam $x $x) as (lam (var $x) (var $x)).
    Lam((SlotMap, Id), (SlotMap, Id)),
    App((SlotMap, Id), (SlotMap, Id)),
    Var(Slot),
    Sym(Symbol),
}

/// Slotted ///

#[derive(Debug)]
struct Slotted;

impl Analysis for Slotted {
    type G = SlotMap;
    type S = SlottedData;
    type L = SlottedLang;

    fn canon(n: &Self::L, uf: &Unionfind<Self::S>) -> (Self::G, Either<Self::L, Id>) {
        let f = |x1: &(SlotMap, Id), x2: &(SlotMap, Id), cb: fn((SlotMap, Id), (SlotMap, Id)) -> SlottedLang| {
            let (g1, i1) = uf.find(x1.clone());
            let (g2, i2) = uf.find(x2.clone());

            let mut d: HashMap<Slot, Slot> = HashMap::new();
            // d :: slots(n) -> SHAPE

            for s in g1.values().into_iter().chain(g2.values().into_iter()) {
                if !d.contains_key(&s) { d.insert(s, d.len()); }
            }
            let d = SlotMap::mk(d.into_iter());

            let m1 = SlotMap::compose(&d, &g1);
            let m2 = SlotMap::compose(&d, &g2);

            (d.inverse(), Either::L(cb((m1, i1), (m2, i2))))
        };
        match n {
            SlottedLang::Lam(x1, x2) => f(x1, x2, SlottedLang::Lam),
            SlottedLang::App(x1, x2) => f(x1, x2, SlottedLang::App),
            SlottedLang::Var(x) => {
                let g = SlotMap::mk([(0, *x)].into_iter());
                (g, Either::L(SlottedLang::Var(0)))
            },
            SlottedLang::Sym(_) => (SlotMap::identity(), Either::L(n.clone())),
        }
    }

    fn mk(n: &Self::L, _id: Id, uf: &Unionfind<Self::S>) -> Self::S {
        let slots = match n {
            SlottedLang::Lam(x1, x2) => &uf.get_semilattice(x2).slots - &uf.get_semilattice(x1).slots,
            SlottedLang::App(x1, x2) => &uf.get_semilattice(x1).slots | &uf.get_semilattice(x2).slots,
            SlottedLang::Var(x) => std::iter::once(*x).collect(),
            SlottedLang::Sym(_) => std::iter::empty().collect(),
        };
        let mut group = HashSet::new();
        group.insert(SlotMap::identity());
        SlottedData { slots, group }
    }

    fn children_mut(n: &mut Self::L) -> Box<[&mut (SlotMap, Id)]> {
        match n {
            SlottedLang::Lam(x1, x2)|SlottedLang::App(x1, x2) => Box::new([x1, x2]),
            SlottedLang::Var(_)|SlottedLang::Sym(_) => Box::new([]),
        }
    }

    fn prettyprint(n: &Self::L, children: Box<[String]>) -> String {
        match n {
            SlottedLang::Lam(..) => format!("(lam {} {})", &children[0], &children[1]),
            SlottedLang::App(..) => format!("(app {} {})", &children[0], &children[1]),
            SlottedLang::Var(x) => format!("(var {x})"),
            SlottedLang::Sym(s) => s.to_string(),
        }
    }

    fn matches(n1: &SlottedLang, n2: &SlottedLang) -> bool {
        match (n1, n2) {
            (SlottedLang::Lam(..),SlottedLang::Lam(..)) => true,
            (SlottedLang::App(..),SlottedLang::App(..)) => true,
            (SlottedLang::Var(..),SlottedLang::Var(..)) => true,
            (SlottedLang::Sym(s1),SlottedLang::Sym(s2)) => s1 == s2,
            _ => false,
        }
    }

    fn ematch(eg: &EGraph<Self>, id: Id, pattern: &Pattern<Self>) -> Vec<Subst<Self>> {
        /*
        let mut out = Vec::new();
        for (_, skel) in skeleton_ematch(eg, id, pattern) {
            let slots = &eg.uf.get_id_semilattice(id).slots;

            let mut pslots = HashSet::new();
            pat_slots(pattern, &mut pslots);

            let mut state = State::default();
            add_diseqs(&pslots, &mut state);

            for st in ematch_impl(SlotMap::identity(), &skel, pattern, slots, eg, state) {
                for st in final_refine(st, eg) {
                    out.push(find_subst(st, eg));
                }
            }
        }
        out
        */
        todo!("ematching unsupported")
    }
}

/*
fn find_subst(state: State, eg: &EGraph<Slotted>) -> Subst<Slotted> {
    state.subst.iter().map(|(pvar, (m, id))| {
        let mut d = HashMap::new();
        for &s in &eg.uf.get_id_semilattice(*id).slots {
            let s_out = m.get(s);
            let s_out = slot_find(s_out, &state);
            d.insert(s, s_out);
        }
        let m = complete(d);
        (*pvar, (m, *id))
    }).collect()
}

fn final_refine(state: State, eg: &EGraph<Slotted>) -> Vec<State> {
    let slots: HashSet<Slot> = state.subst.iter().flat_map(|(_, (m, id))|
        eg.uf.get_id_semilattice(*id).slots.iter().map(|s| m.get(*s)).collect::<Vec<_>>()
    ).collect();

    for &x in &slots {
        for &y in &slots {
            let x = slot_find(x, &state);
            let y = slot_find(y, &state);
            if x == y { continue }
            if let Some(st2) = slot_unify(x, y, &state) {
                let mut st1 = state;
                add_diseqs(&[x, y].into_iter().collect(), &mut st1);

                let mut out = final_refine(st1, eg);
                out.extend(final_refine(st2, eg));
                return out
            }
        }
    }
    vec![state]
}

fn pat_slots(pat: &Pattern<Slotted>, pslots: &mut HashSet<Slot>) {
    match pat {
        Pattern::Node(SlottedLang::Var(v), _) => { pslots.insert(*v); },
        Pattern::Node(_, children) => {
            children.iter().for_each(|p| pat_slots(p, pslots));
        },
        Pattern::PVar(_) => {},
        Pattern::G(..) => unreachable!(),
    }
}

/// ematching ///

fn exposed_slots(n: &SlottedLang, children: &[(SlotMap, SlottedData, Skel<Slotted>)]) -> HashSet<Slot> {
    if let SlottedLang::Var(v) = n { return std::iter::once(*v).collect() }
    children.iter().flat_map(|(g, s, _)|
        s.slots.iter().map(|x| g.get(*x))
    ).collect()
}

fn apply_slotmap(m: SlotMap, n: &mut SlottedLang, children: &mut [(SlotMap, SlottedData, Skel<Slotted>)]) {
    if let SlottedLang::Var(v) = n { *n = SlottedLang::Var(m.get(*v)); }
    children.iter_mut().for_each(|(m2, _, _)| {
        *m2 = SlotMap::compose(&m, m2);
    });
}

// makes redundant slots fresh.
fn refresh(n: &mut SlottedLang, children: &mut [(SlotMap, SlottedData, Skel<Slotted>)], slots: &HashSet<Slot>) {
    let exposed = exposed_slots(n, children);
    let redundant = &exposed - slots;
    let fresh = std::iter::from_fn(|| Some(fresh_slot()));
    let it: Vec<(Slot, Slot)> = redundant.into_iter().zip(fresh).collect();
    let m = SlotMap::mk(it.iter().copied().chain(it.iter().map(|(x, y)| (*y, *x))));
    apply_slotmap(m, n, children);
}

fn add_diseqs(slots: &HashSet<Slot>, state: &mut State) {
    for &x in slots {
        let entry = state.diseqs.entry(x).or_default();
        entry.extend(slots.iter().filter(|a| **a != x));
    }
}

#[derive(Clone, Default)]
struct State {
    slot_uf: HashMap<Slot, Slot>,
    diseqs: HashMap<Slot, HashSet<Slot>>,
    subst: Subst<Slotted>,
}

// g * skel = pat
fn ematch_impl(g: SlotMap, skel: &Skel<Slotted>, pat: &Pattern<Slotted>, slots: &HashSet<Slot>, eg: &EGraph<Slotted>, mut state: State) -> Vec<State> {
    use SlottedLang::*;
    match (skel, pat) {
        (Skel::PVar(id), Pattern::PVar(v)) => {
            let new = (g.clone(), *id);
            if let Some((old_g, id2)) = state.subst.insert(*v, new.clone()) {
                assert_eq!(*id, id2);
                let d = eg.uf.get_id_semilattice(*id);
                return appid_unify(&g, &old_g, &d, &state)
            } else { return vec![state] }
        },
        (Skel::Node(g_skel, node, skel_children), Pattern::Node(pat_node, pat_children)) => {
            let effective_g = SlotMap::compose(&g, g_skel);
            let mut node = node.clone();
            let mut skel_children = skel_children.clone();
            apply_slotmap(effective_g.clone(), &mut node, &mut skel_children);

            let effective_slots: HashSet<Slot> = slots.iter().map(|x| effective_g.get(*x)).collect();
            refresh(&mut node, &mut *skel_children, &effective_slots);

            let slots = exposed_slots(&node, &skel_children);
            add_diseqs(&slots, &mut state);

            match (node, pat_node) {
                (SlottedLang::Sym(_), SlottedLang::Sym(_)) => vec![state],

                (SlottedLang::Var(v0), SlottedLang::Var(v1)) => slot_unify(v0, *v1, &state).into_iter().collect(),

                (SlottedLang::App(..), SlottedLang::App(..))
               |(SlottedLang::Lam(..), SlottedLang::Lam(..)) => {
                    // (app g0*c0 g1*c1) = (app p0 p1)
                    let mut out = Vec::new();
                    for (cg0, cg1) in branch_nodes(&skel_children) {
                        let (_, cs, subskel) = &skel_children[0];
                        for state2 in ematch_impl(cg0, subskel, &pat_children[0], &cs.slots, eg, state.clone()) {
                            let (_, cs, subskel) = &skel_children[1];
                            out.extend(ematch_impl(cg1.clone(), subskel, &pat_children[1], &cs.slots, eg, state2));
                        }
                    }
                    out
                },
                _ => unreachable!(),
            }
        },
        _ => unreachable!(),
    }
}

type SkelChildren = Box<[(SlotMap, SlottedData, Skel<Slotted>)]>;

fn branch_nodes(skel_children: &SkelChildren) -> Vec<(SlotMap, SlotMap)> {
    if skel_children.is_empty() { return Vec::new() }
    assert_eq!(skel_children.len(), 2);

    let (g0, s0, ch0) = &skel_children[0];
    let (g1, s1, ch1) = &skel_children[1];
    let group0 = &s0.group;
    let group1 = &s1.group;
    let mut out = Vec::new();
    for gg0 in group0.iter() {
        let cg0 = SlotMap::compose(g0, gg0);
        for gg1 in group1.iter() {
            let cg1 = SlotMap::compose(g1, gg1);
            out.push((cg0.clone(), cg1));
        }
    }
    out
}

fn slot_unify(x: Slot, y: Slot, state: &State) -> Option<State> {
    let x = slot_find(x, state);
    let y = slot_find(y, state);
    if x == y { return Some(state.clone()) }

    let mut state = state.clone();
    if state.diseqs.entry(x).or_default().contains(&y) { return None }
    if state.diseqs.entry(y).or_default().contains(&x) { return None }
    state.slot_uf.insert(x, y);
    let x_diseq = state.diseqs.remove(&x).unwrap_or_default();
    state.diseqs.entry(y).or_default().extend(x_diseq);

    for (_, a) in state.diseqs.iter_mut() {
        if a.contains(&x) {
            a.remove(&x);
            a.insert(y);
        }
    }
    Some(state)
}

fn appid_unify(x: &SlotMap, y: &SlotMap, d: &SlottedData, state: &State) -> Vec<State> {
    let mut out = Vec::new();

    let xslots: HashSet<Slot> = d.slots.iter().map(|s| slot_find(x.get(*s), state)).collect();
    let yslots: HashSet<Slot> = d.slots.iter().map(|s| slot_find(y.get(*s), state)).collect();

    let xonly = &xslots - &yslots;
    let yonly = &yslots - &xslots;
    if xonly.len() != yonly.len() { return Vec::new() }

    if !xonly.is_empty() {
        let x0 = *xonly.iter().next().unwrap();
        for y0 in yonly {
            if let Some(state) = slot_unify(x0, y0, state) {
                out.extend(appid_unify(x, y, d, &state));
            }
        }
        return out
    }

    // Here we know that xslots == yslots.
    'outer: for g in &d.group {
        let x = SlotMap::compose(x, g);
        let mut state = state.clone();
        for &slot in &d.slots {
            let Some(state2) = slot_unify(x.get(slot), y.get(slot), &mut state) else { continue 'outer };
            state = state2;
        }
        out.push(state);
    }
    out
}

fn slot_find(mut x: Slot, state: &State) -> Slot {
    while let Some(y) = state.slot_uf.get(&x) {
        x = *y;
    }
    x
}

type Pat = Pattern<Slotted>;
fn nil() -> (SlotMap, Id) { (SlotMap::identity(), Id(0)) }
fn mk_lam(p1: Pat, p2: Pat) -> Pat { Pattern::Node(SlottedLang::Lam(nil(), nil()), Box::new([p1, p2])) }
fn mk_app(p1: Pat, p2: Pat) -> Pat { Pattern::Node(SlottedLang::App(nil(), nil()), Box::new([p1, p2])) }

fn mk_sym(s: &str) -> Pat { Pattern::Node(SlottedLang::Sym(Symbol::new(s)), Box::new([])) }
fn mk_var(s: Slot) -> Pat { Pattern::Node(SlottedLang::Var(s), Box::new([])) }
fn mk_pvar(s: &str) -> Pat { Pattern::PVar(Symbol::new(s)) }

#[test]
// (app (var $x) (var $y)) matches (app ?x ?y)
fn slotted_ematching_test() {
    let mut eg: EGraph<Slotted> = EGraph::new();
    add_expr(&mk_app(mk_var(3), mk_var(4)), &mut eg);
    eg.rebuild_nodes();
    let pat = mk_app(mk_pvar("?x"), mk_pvar("?y"));
    let matches = ematch_all(&eg, &pat);
    assert_eq!(matches.len(), 1);
}

#[test]
fn slotted_ematching_test2() {
    let mut eg: EGraph<Slotted> = EGraph::new();
    let a = add_expr(&
        mk_app(mk_lam(mk_var(3), mk_var(3)),
            mk_lam(mk_var(3), mk_var(3))),
        &mut eg);
    eg.rebuild_nodes();

    let pat =
        mk_app(mk_lam(mk_var(2), mk_var(2)),
            mk_lam(mk_var(4), mk_var(4)));

    let matches = ematch_all(&eg, &pat);
    assert_eq!(matches.len(), 1);
}

#[test]
fn slotted_ematching_test3() {
    let mut eg: EGraph<Slotted> = EGraph::new();
    let a = add_expr(&
        mk_lam(mk_var(3), mk_var(3)),
        &mut eg);
    eg.rebuild_nodes();

    let pat = mk_lam(mk_var(10), mk_var(11));

    let matches = ematch_all(&eg, &pat);
    assert_eq!(matches.len(), 0);
}

#[test]
fn slotted_ematching_test4() {
    let mut eg: EGraph<Slotted> = EGraph::new();
    let a = add_expr(&
        mk_lam(mk_var(3), mk_var(4)),
        &mut eg);
    eg.rebuild_nodes();

    let pat = mk_lam(mk_var(10), mk_var(10));

    let matches = ematch_all(&eg, &pat);
    assert_eq!(matches.len(), 0);
}

#[test]
fn slotted_ematching_test5() {
    let mut eg: EGraph<Slotted> = EGraph::new();
    let a = add_expr(&
        mk_app(
            mk_lam(mk_var(2), mk_var(2)),
            mk_lam(mk_var(3), mk_var(3))
        ),
        &mut eg);
    eg.rebuild_nodes();

    let pat =
        mk_app(
            mk_lam(mk_var(1), mk_pvar("?a")),
            mk_lam(mk_var(1), mk_pvar("?a"))
        );

    let matches = ematch_all(&eg, &pat);
    assert_eq!(matches.len(), 1);
}

#[test]
fn slotted_ematching_test6() {
    let mut eg: EGraph<Slotted> = EGraph::new();
    let a = add_expr(&
        mk_app(
            mk_lam(mk_var(2), mk_var(2)),
            mk_lam(mk_var(3), mk_var(3))
        ),
        &mut eg);
    eg.rebuild_nodes();

    let pat =
        mk_app(
            mk_lam(mk_var(1), mk_pvar("?a")),
            mk_lam(mk_var(2), mk_pvar("?a"))
        );

    let matches = ematch_all(&eg, &pat);
    assert_eq!(matches.len(), 0);
}

#[test]
fn slotted_ematching_test7() {
    let mut eg: EGraph<Slotted> = EGraph::new();
    let a = add_expr(&
        mk_app(
            mk_lam(mk_var(2), mk_var(2)),
            mk_lam(mk_var(3), mk_var(3))
        ),
        &mut eg);
    eg.rebuild_nodes();

    let pat =
        mk_app(
            mk_lam(mk_var(1), mk_pvar("?a")),
            mk_lam(mk_var(2), mk_pvar("?b"))
        );

    let matches = ematch_all(&eg, &pat);
    assert_eq!(matches.len(), 1);
}

#[test]
fn slotted_ematching_test8() {
    let mut eg: EGraph<Slotted> = EGraph::new();
    let a = add_expr(&
        mk_app(
            mk_lam(mk_var(2), mk_var(2)),
            mk_lam(mk_var(3), mk_var(3))
        ),
        &mut eg);
    eg.rebuild_nodes();

    let pat =
        mk_app(
            mk_lam(mk_var(1), mk_pvar("?a")),
            mk_lam(mk_var(1), mk_pvar("?a"))
        );

    let matches = ematch_all(&eg, &pat);
    assert_eq!(matches.len(), 1);
}

#[test]
fn slotted_ematching_test9() {
    let mut eg: EGraph<Slotted> = EGraph::new();
    let a = add_expr(&
        mk_app(
            mk_lam(mk_var(2), mk_var(2)),
            mk_lam(mk_var(3), mk_var(3))
        ),
        &mut eg);
    eg.rebuild_nodes();

    let pat =
        mk_app(
            mk_lam(mk_pvar("?a"), mk_pvar("?a")),
            mk_lam(mk_pvar("?b"), mk_pvar("?b"))
        );

    let matches = ematch_all(&eg, &pat);
    dbg!(&matches);
    assert!(matches[0] != matches[1]);
    assert_eq!(matches.len(), 2);
}

#[test]
fn slotted_ematching_test10() {
    let mut eg: EGraph<Slotted> = EGraph::new();
    // here we test symmetries.
    let a = add_expr(&mk_app(mk_var(2), mk_var(3)), &mut eg);
    let b = add_expr(&mk_app(mk_var(3), mk_var(2)), &mut eg);
    eg.union(a, b);

    add_expr(&
        mk_app(
            mk_app(mk_var(1), mk_var(2)),
            mk_app(mk_var(1), mk_var(2))
        ),
    &mut eg);
    eg.rebuild_nodes();

    let pat =
        mk_app(
            mk_app(mk_pvar("?a"), mk_pvar("?b")),
            mk_app(mk_pvar("?b"), mk_pvar("?a"))
        );

    let matches = ematch_all(&eg, &pat);
    dbg!(&matches);
    assert!(matches.len() > 0);
}


// For now, the user isn't allowed to use explicit slots >= 10_000.
use std::sync::atomic::{AtomicUsize, Ordering};
static FRESH_COUNTER: AtomicUsize = AtomicUsize::new(10_000);
pub fn fresh_slot() -> Slot {
    FRESH_COUNTER.fetch_add(1, Ordering::Relaxed)
}
*/
