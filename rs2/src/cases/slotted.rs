use crate::*;

type Slot = usize;

/// SlotMap ///

// invariant: bijective & total (every missing key is the identity).
// Thus the key & value sets are equal, we call them the support.
// Every identity pairs are missing in v. v is sorted by keys.
#[derive(Clone, Hash, PartialEq, Eq, Debug)]
struct SlotMap {
    v: Vec<(Slot, Slot)>
}

impl SlotMap {
    pub fn mk(it: impl Iterator<Item=(Slot, Slot)>) -> SlotMap {
        let mut v: Vec<(Slot, Slot)> = it.filter(|(x, y)| x != y).collect();

        { // DEBUGGING
            for (x, y) in &v {
                assert!(x != y);
            }
            let kset = v.iter().map(|(x, _)| *x).collect::<HashSet<Slot>>();
            let vset = v.iter().map(|(_, y)| *y).collect::<HashSet<Slot>>();
            assert!(kset == vset);
            assert!(kset.len() == v.len()); // no duplicates
        }

        v.sort_by_key(|(x, _)| *x);
        SlotMap { v }
    }

    pub fn support(&self) -> impl Iterator<Item=Slot> {
        self.v.iter().map(|(x, _)| *x)
    }

    pub fn get(&self, x: Slot) -> Slot {
        if let Some((_, b)) = self.v.iter().find(|(a, b)| *a == x) { *b }
        else { x }
    }

    pub fn iter(&self) -> impl Iterator<Item=(Slot,Slot)> {
        self.v.iter().copied()
    }
}

impl Group for SlotMap {
    fn identity() -> SlotMap { SlotMap::mk(std::iter::empty()) }

    // l*(r*_)
    fn compose(l: &SlotMap, r: &SlotMap) -> SlotMap {
        let set = l.support().chain(r.support()).collect::<HashSet<Slot>>();
        SlotMap::mk(set.into_iter()
                       .map(|x| (x, l.get(r.get(x))))
                       .filter(|(x, y)| x != y)
                   )
    }

    fn inverse(&self) -> SlotMap {
        SlotMap::mk(self.iter().map(|(x, y)| (y, x)))
    }
}

/// SlottedData ///

#[derive(PartialEq, Eq, Debug)]
struct SlottedData {
    slots: HashSet<Slot>,
    group: HashSet<SlotMap>,
}

impl Semilattice for SlottedData {
    type G = SlotMap;

    fn act(g: &Self::G, s: &Self) -> Self {
        let slots = s.slots.iter().map(|x| g.get(*x)).collect();
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

            let mut d = HashMap::new();
            // d :: slots(n) -> SHAPE

            let mut slots1: Vec<Slot> = uf.get_leader_semilattice(i1).slots.iter().copied().collect();
            slots1.sort();
            let it1 = slots1.into_iter().map(|x| g1.get(x));

            let mut slots2: Vec<Slot> = uf.get_leader_semilattice(i2).slots.iter().copied().collect();
            slots2.sort();
            let it2 = slots2.into_iter().map(|x| g2.get(x));

            let it = it1.chain(it2);

            for s in it {
                if !d.contains_key(&s) {
                    d.insert(s, d.len());
                }
            }
            let d = complete(d);
            let m1 = SlotMap::compose(&d, &g1);
            let m1 = canon((m1, i1), uf);

            let m2 = SlotMap::compose(&d, &g2);
            let m2 = canon((m2, i2), uf);

            (d.inverse(), Either::L(cb((m1, i1), (m2, i2))))
        };
        match n {
            SlottedLang::Lam(x1, x2) => f(x1, x2, SlottedLang::Lam),
            SlottedLang::App(x1, x2) => f(x1, x2, SlottedLang::App),
            SlottedLang::Var(x) => {
                if *x == 0 { (SlotMap::identity(), Either::L(n.clone())) }
                else {
                    let g = SlotMap::mk([(*x, 0), (0, *x)].into_iter());
                    (g, Either::L(SlottedLang::Var(0)))
                }
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
}

fn complete(mut d: HashMap<Slot, Slot>) -> SlotMap {
    let keys: HashSet<Slot> = d.keys().copied().collect();
    let values: HashSet<Slot> = d.values().copied().collect();

    let k2 = &keys - &values;
    let v2 = &values - &keys;

    let mut k2: Vec<Slot> = k2.into_iter().collect();
    let mut v2: Vec<Slot> = v2.into_iter().collect();

    assert_eq!(k2.len(), v2.len());
    k2.sort();
    v2.sort();

    for (k, v) in k2.into_iter().zip(v2.into_iter()) {
        d.insert(v, k);
    }
    SlotMap::mk(d.into_iter())
}

fn canon((m, x): (SlotMap, Id), uf: &Unionfind<SlottedData>) -> SlotMap {
    let slots = &uf.get_leader_semilattice(x).slots;
    let m2 = m.iter().filter(|(a, b)| slots.contains(a)).collect();
    complete(m2)
}
/// E-Matching:

#[derive(Debug)]
struct SlottedMatcher;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum SymSlotMapPiece {
    GVar(GVar, /*true means inverted*/ bool),
    Concrete(SlotMap),
}

fn inverse_piece(x: &SymSlotMapPiece) -> SymSlotMapPiece {
    match x {
        SymSlotMapPiece::GVar(v, b) => SymSlotMapPiece::GVar(*v, !*b),
        SymSlotMapPiece::Concrete(m) => SymSlotMapPiece::Concrete(m.inverse()),
    }
}

// this list is composed.
type SymSlotMap = Vec<SymSlotMapPiece>;

impl Matcher<Slotted> for SlottedMatcher {
    type SymG = SymSlotMap;

    fn compose(l: &Self::SymG, r: &Self::SymG) -> Self::SymG {
        l.iter().cloned().chain(r.iter().cloned()).collect()
    }

    fn inverse(x: &Self::SymG) -> Self::SymG {
        x.iter().rev().map(inverse_piece).collect()
    }

    fn from_gvar(v: GVar) -> Self::SymG {
        vec![SymSlotMapPiece::GVar(v, false)]
    }

    fn from_g(m: &SlotMap) -> Self::SymG {
        vec![SymSlotMapPiece::Concrete(m.clone())]
    }

    fn expand(node: &SlottedLang, mut fresh_gvar: impl FnMut() -> GVar) -> (/*up*/Self::SymG, /*children*/Box<[Self::SymG]>) {
        match node {
            SlottedLang::Lam(..)|SlottedLang::App(..) => {
                let v = fresh_gvar();
                (vec![SymSlotMapPiece::GVar(v, false)], vec![vec![SymSlotMapPiece::GVar(v, true)]; 2].into())
            },
            SlottedLang::Var(..)|SlottedLang::Sym(..) => (Vec::new(), Box::new([])),
        }
    }

    fn solve<'eg>(mut state: State<'eg, Slotted, Self>) -> Option<Subst<Slotted>> {
        default_s(&mut state);
        push_down(&mut state);
        simplify_all(&mut state);
        default_unconstrained(&mut state);
        simplify_all(&mut state);
        dbg!(&state);
        finalize(state)
    }
}

fn subst(v: GVar, val: SymSlotMap, state: &mut State<'_, Slotted, SlottedMatcher>) {
    // println!("gvar {v} -> {val:?}");
    state.gs_constraints.remove(&v);

    let mut syms: Vec<&mut SymSlotMap> = Vec::new();
    for c in state.g_constraints.iter_mut() { syms.push(c); }
    for (_, c) in state.subst.iter_mut() { syms.push(&mut c.0); }

    for c in syms {
        let c2 = std::mem::take(c);
        for x in c2 {
            let x =
                if let SymSlotMapPiece::GVar(v2, b) = x && v2 == v {
                    if b {
                        SlottedMatcher::inverse(&val)
                    } else {
                        val.clone()
                    }
                } else {
                    vec![x]
                };
            c.extend(x);
        }
    }
}

fn push_down(state: &mut State<'_, Slotted, SlottedMatcher>) {
    'l: loop {
        for (j, constraint) in state.g_constraints.iter_mut().enumerate() {
            for (i, a) in constraint.iter().enumerate() {
                match a {
                    SymSlotMapPiece::GVar(v, false) if !state.gs_constraints.contains_key(&v) => {
                        let a: SymSlotMap = constraint[0..i].iter().cloned().collect();
                        let b: SymSlotMap = constraint[(i+1)..].iter().cloned().collect();

                        // if a and b contain v, we can't do this transformation.
                        if a.contains(&SymSlotMapPiece::GVar(*v, false)) { continue }
                        if a.contains(&SymSlotMapPiece::GVar(*v, true)) { continue }
                        if b.contains(&SymSlotMapPiece::GVar(*v, false)) { continue }
                        if b.contains(&SymSlotMapPiece::GVar(*v, true)) { continue }

                        // a*v*b = identity -> v = a⁻¹*b⁻¹
                        let val = SlottedMatcher::compose(&SlottedMatcher::inverse(&a), &SlottedMatcher::inverse(&b));
                        subst(*v, val, state);
                        state.g_constraints.remove(j);
                        continue 'l;
                    },
                    _ => {},
                }
            }
        }
        break
    }
}

fn default_s(state: &mut State<'_, Slotted, SlottedMatcher>) {
    for (v, _) in std::mem::take(&mut state.gs_constraints) {
        subst(v, Vec::new(), state);
    }
}

fn syms_mut<'a>(state: &'a mut State<'_, Slotted, SlottedMatcher>) -> Vec<&'a mut SymSlotMap> {
    let mut out = Vec::new();
    out.extend(state.g_constraints.iter_mut());
    out.extend(state.subst.iter_mut().map(|(_, (g, _))| g));
    out
}

fn simplify_all(state: &mut State<'_, Slotted, SlottedMatcher>) {
    for g in syms_mut(state) {
        simplify_sym(g);
    }
}

fn simplify_sym(sym: &mut SymSlotMap) {
    'l: loop {
        sym.retain(|x| *x != SymSlotMapPiece::Concrete(SlotMap::identity()));
        if sym.is_empty() { return }
        for i in 0..sym.len()-1 {
            let a = &sym[i];
            let b = &sym[i+1];
            match (a, b) {
                (SymSlotMapPiece::Concrete(ma), SymSlotMapPiece::Concrete(mb)) => {
                    sym[i] = SymSlotMapPiece::Concrete(SlotMap::compose(&ma, &mb));
                    sym.remove(i+1);
                    continue 'l;
                },
                (SymSlotMapPiece::GVar(v1, b1), SymSlotMapPiece::GVar(v2, b2)) if v1 == v2 && b1 != b2 => {
                    sym.remove(i);
                    sym.remove(i);
                    continue 'l;
                },
                _ => {},
            }
        }
        break
    }
}

fn default_unconstrained(state: &mut State<'_, Slotted, SlottedMatcher>) {
    'l: loop {
        for (_, (g, _)) in &state.subst {
            for x in g {
                let SymSlotMapPiece::GVar(v, _) = x else { continue };
                if !is_unconstrained(*v, state) { continue }
                subst(*v, Vec::new(), state);
                continue 'l;
            }
        }
        break
    }
}

fn is_unconstrained(v: GVar, state: &State<'_, Slotted, SlottedMatcher>) -> bool {
    for x in &state.g_constraints {
        for x in x {
            if let SymSlotMapPiece::GVar(v2, _) = x && *v2 == v { return false }
        }
    }
    true
}

fn finalize_sym(sym: SymSlotMap) -> SlotMap {
    if sym.is_empty() { return SlotMap::identity() }

    let [SymSlotMapPiece::Concrete(m)] = &sym[..] else { panic!() };
    return m.clone()
}

fn finalize(state: State<'_, Slotted, SlottedMatcher>) -> Option<Subst<Slotted>> {
    Some(state.subst.into_iter().map(|(x, (m, id))| (x, (finalize_sym(m), id))).collect())
}

///--- TESTS ---///

fn app(x: (SlotMap, Id), y: (SlotMap, Id), eg: &mut EGraph<Slotted>) -> (SlotMap, Id) { eg.add(&SlottedLang::App(x, y)) }
fn var(x: Slot, eg: &mut EGraph<Slotted>) -> (SlotMap, Id) { eg.add(&SlottedLang::Var(x)) }
fn lam(x: Slot, b: (SlotMap, Id), eg: &mut EGraph<Slotted>) -> (SlotMap, Id) { let x = var(x, eg); eg.add(&SlottedLang::Lam(x, b)) }
fn sym(s: &str, eg: &mut EGraph<Slotted>) -> (SlotMap, Id) { eg.add(&SlottedLang::Sym(Symbol::new(s))) }

type Pat = Pattern<Slotted>;
fn nil() -> (SlotMap, Id) { (SlotMap::identity(), Id(0)) }
fn app_p(x: Pat, y: Pat) -> Pat { Pattern::Node(SlottedLang::App(nil(), nil()), Box::new([x, y])) }
fn var_p(x: Slot) -> Pat { Pattern::Node(SlottedLang::Var(x), Box::new([])) }
fn lam_p(x: Slot, b: Pat) -> Pat { let x = var_p(x); Pattern::Node(SlottedLang::Lam(nil(), nil()), Box::new([x, b])) }
fn sym_p(s: &str) -> Pat { Pattern::Node(SlottedLang::Sym(Symbol::new(s)), Box::new([])) }
fn pvar(s: &str) -> Pat { Pattern::PVar(Symbol::new(s)) }

#[test]
fn alpha() {
    let mut eg = &mut EGraph::new();

    let v3 = var(3, eg);
    let v4 = var(4, eg);

    let l3v3 = lam(3, v3, eg);
    let l4v4 = lam(4, v4, eg);

    assert!(eg.is_equal(l3v3, l4v4));
}

#[test]
fn test2() {
    let mut eg = &mut EGraph::new();

    let c = sym("c", eg);

    let l2c = lam(2, c.clone(), eg);
    let l3c = lam(3, c.clone(), eg);

    dbg!(&l2c);
    dbg!(&l3c);

    assert!(eg.is_equal(l2c, l3c));
}

#[test]
fn test3() {
    let mut eg = &mut EGraph::new();

    let v3 = var(3, eg);
    let v4 = var(4, eg);

    let v3v4 = app(v3.clone(), v4.clone(), eg);
    let v4v3 = app(v4.clone(), v3.clone(), eg);

    let l3v3v4 = lam(3, v3v4, eg);
    let l4v4v3 = lam(4, v4v3, eg);

    let l4l3v3v4 = lam(4, l3v3v4, eg);
    let l3l4v4v3 = lam(3, l4v4v3, eg);

    assert!(eg.is_equal(l4l3v3v4, l3l4v4v3));
}

#[test]
fn test4() {
    let mut eg = &mut EGraph::new();

    let v3 = var(3, eg);
    let v4 = var(4, eg);

    let v5 = var(5, eg);
    let v6 = var(6, eg);

    let v3v4 = app(v3.clone(), v4.clone(), eg);
    let v4v3 = app(v4.clone(), v3.clone(), eg);

    let l3v3v4 = lam(3, v3v4, eg);
    let l4v4v3 = lam(4, v4v3, eg);

    assert!(!eg.is_equal(l3v3v4.clone(), l4v4v3.clone()));

    eg.union(v5, v6);

    assert!(eg.is_equal(l3v3v4, l4v4v3));
}

#[test]
fn slotted_matching1() {
    let mut eg = &mut EGraph::new();

    let v2 = var(2, eg);
    let l2 = app(v2.clone(), v2, eg);

    // TODO necessary so far.
    eg.rebuild_nodes();

    let pat = app_p(var_p(3), pvar("a"));

    let matches = ematch::<Slotted, SlottedMatcher>(&pat, eg);
    assert_eq!(matches.len(), 1);
}

#[test]
fn slotted_matching2() {
    let mut eg = &mut EGraph::new();

    let v2 = var(2, eg);
    let l2 = app(v2.clone(), v2, eg);

    // TODO necessary so far.
    eg.rebuild_nodes();

    let pat = app_p(pvar("a"), pvar("a"));

    let matches = ematch::<Slotted, SlottedMatcher>(&pat, eg);
    assert_eq!(matches.len(), 1);
}
