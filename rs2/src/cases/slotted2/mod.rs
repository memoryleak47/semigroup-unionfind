use crate::*;

mod parse;
pub use parse::parse;

mod ematch;
pub use ematch::*;

type Slot = usize;

/// SlotMap ///

#[derive(Clone, Hash, PartialEq, Eq)]
struct SlotMap {
    v: Vec<(Slot, Slot)>
}

impl SlotMap {
    pub fn mk(it: impl Iterator<Item=(Slot, Slot)>) -> SlotMap {
        let mut v: Vec<(Slot, Slot)> = it.collect();
        v.sort_by_key(|(x, _)| *x);
        SlotMap { v }
    }

    pub fn keys(&self) -> impl Iterator<Item=Slot> { self.v.iter().map(|(k, _)| *k) }
    pub fn vals(&self) -> impl Iterator<Item=Slot> { self.v.iter().map(|(_, v)| *v) }

    pub fn vals_mut(&mut self) -> impl Iterator<Item=&mut Slot> { self.v.iter_mut().map(|(_, v)| v) }

    pub fn get(&self, x: Slot) -> Option<Slot> {
        self.iter().find(|(a, _)| *a == x).map(|(_, b)| b)
    }

    pub fn iter(&self) -> impl Iterator<Item=(Slot,Slot)> {
        self.v.iter().copied()
    }
}

impl Group for SlotMap {
    // l*(r*_)
    fn compose(l: &SlotMap, r: &SlotMap) -> SlotMap {
        SlotMap::mk(r.iter().filter_map(|(x, y)| l.get(y).map(|y| (x, y))))
    }

    fn inverse(&self) -> SlotMap {
        SlotMap::mk(self.iter().map(|(x, y)| (y, x)))
    }

    fn identity() -> SlotMap {
        SlotMap::mk(std::iter::empty())
    }
}

impl Debug for SlotMap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        let mut it = self.iter();
        if let Some((x, y)) = it.next() {
            write!(f, "${x} -> ${y}")?;
            for (x, y) in it {
                write!(f, ", ${x} -> ${y}")?;
            }
        }
        write!(f, "]")
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
        let slots = s.slots.iter().filter_map(|x| g.get(*x)).collect();
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

    fn local_identity(&self) -> SlotMap { SlotMap::mk(self.slots.iter().map(|s| (*s, *s))) }
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
    d.group.insert(d.local_identity());
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
    Lam(Slot, (SlotMap, Id)),
    App((SlotMap, Id), (SlotMap, Id)),
    Var(Slot),
    Let((SlotMap, Id), Slot, (SlotMap, Id)),
    Number(u32),
    Symbol(Symbol),
}

/// Slotted ///

#[derive(Debug)]
struct Slotted;

fn canon_shape(it: impl Iterator<Item=Slot>) -> SlotMap {
    let mut d = HashMap::new();

    // d :: slots(n) -> SHAPE
    for s in it {
        if !d.contains_key(&s) {
            d.insert(s, d.len());
        }
    }
    SlotMap::mk(d.into_iter())
}

#[track_caller]
fn check(n: &SlottedLang) {
    if let SlottedLang::Let(t, v, _) = n {
        assert!(t.0.vals().any(|x| x != *v));
    }
}

impl Analysis for Slotted {
    type G = SlotMap;
    type S = SlottedData;
    type L = SlottedLang;

    fn canon(n: &Self::L, uf: &Unionfind<Self::S>) -> (Self::G, Either<Self::L, Id>) {
        check(n);
        match n {
            SlottedLang::Lam(x1, x2) => {
                let (g2, i2) = uf.find(x2.clone());

                let it1 = std::iter::once(*x1);

                let mut slots2: Vec<Slot> = uf.get_leader_semilattice(i2).slots.iter().copied().collect();
                slots2.sort();
                let it2 = slots2.into_iter().flat_map(|x| g2.get(x));

                let it = it1.chain(it2);
                let d = canon_shape(it);

                let m2 = SlotMap::compose(&d, &g2);
                (d.inverse(), Either::L(SlottedLang::Lam(0, (m2, i2))))
            },
            SlottedLang::App(x1, x2) => {
                let (g1, i1) = uf.find(x1.clone());
                let (g2, i2) = uf.find(x2.clone());

                let mut slots1: Vec<Slot> = uf.get_leader_semilattice(i1).slots.iter().copied().collect();
                slots1.sort();
                let it1 = slots1.into_iter().flat_map(|x| g1.get(x));

                let mut slots2: Vec<Slot> = uf.get_leader_semilattice(i2).slots.iter().copied().collect();
                slots2.sort();
                let it2 = slots2.into_iter().flat_map(|x| g2.get(x));

                let it = it1.chain(it2);
                let d = canon_shape(it);

                let m1 = SlotMap::compose(&d, &g1);
                let m2 = SlotMap::compose(&d, &g2);
                (d.inverse(), Either::L(SlottedLang::App((m1, i1), (m2, i2))))
            },
            SlottedLang::Var(x) => {
                let g = SlotMap::mk([(0, *x)].into_iter());
                (g, Either::L(SlottedLang::Var(0)))
            },
            SlottedLang::Let(t, v, b) => {
                let t = uf.find(t.clone());
                let b = uf.find(b.clone());

                dbg!(&n);
                assert!(t.0.vals().all(|a| a != *v), "If this panics, we'll have to refresh v before canonizing this e-node");

                let mut slots_t: Vec<Slot> = uf.get_leader_semilattice(t.1).slots.iter().copied().collect();
                slots_t.sort();
                let it1 = slots_t.into_iter().flat_map(|x| t.0.get(x));

                let it2 = std::iter::once(*v);

                let mut slots_b: Vec<Slot> = uf.get_leader_semilattice(b.1).slots.iter().copied().collect();
                slots_b.sort();
                let it3 = slots_b.into_iter().flat_map(|x| b.0.get(x));

                let it = it1.chain(it2).chain(it3);
                let d = canon_shape(it);

                let mt = SlotMap::compose(&d, &t.0);
                let mb = SlotMap::compose(&d, &b.0);
                let vv = d.get(*v).unwrap();
                (d.inverse(), Either::L(SlottedLang::Let((mt, t.1), vv, (mb, b.1))))
            },
            SlottedLang::Number(_)|SlottedLang::Symbol(_) => (SlotMap::mk(std::iter::empty()), Either::L(n.clone())),
        }
    }

    fn mk(n: &Self::L, _id: Id, uf: &Unionfind<Self::S>) -> Self::S {
        let slots = match n {
            SlottedLang::Lam(x1, x2) => &uf.get_semilattice(x2).slots - &std::iter::once(*x1).collect::<HashSet<_>>(),
            SlottedLang::App(x1, x2) => &uf.get_semilattice(x1).slots | &uf.get_semilattice(x2).slots,
            SlottedLang::Var(x) => std::iter::once(*x).collect(),
            SlottedLang::Let(t, v, b) => &uf.get_semilattice(t).slots | &(&uf.get_semilattice(b).slots - &std::iter::once(*v).collect::<HashSet<_>>()),
            SlottedLang::Number(_)|SlottedLang::Symbol(_) => std::iter::empty().collect(),
        };
        let mut group = HashSet::new();
        group.insert(SlotMap::mk(slots.iter().map(|s| (*s, *s))));
        SlottedData { slots, group }
    }

    fn children_mut(n: &mut Self::L) -> Box<[&mut (SlotMap, Id)]> {
        match n {
            SlottedLang::Lam(_, x2) => Box::new([x2]),
            SlottedLang::App(x1, x2)|SlottedLang::Let(x1, _, x2) => Box::new([x1, x2]),
            SlottedLang::Var(_)|SlottedLang::Number(_)|SlottedLang::Symbol(_) => Box::new([]),
        }
    }

    fn prettyprint(n: &Self::L, children: Box<[String]>) -> String {
        match n {
            SlottedLang::Lam(v, _) => format!("(lam ${v} {})", &children[0]),
            SlottedLang::App(..) => format!("(app {} {})", &children[0], &children[1]),
            SlottedLang::Var(x) => format!("(var ${x})"),
            SlottedLang::Let(_, v, _) => format!("(let {} ${v} {})", &children[0], &children[1]),
            SlottedLang::Number(s) => s.to_string(),
            SlottedLang::Symbol(s) => s.to_string(),
        }
    }

    fn matches(n1: &SlottedLang, n2: &SlottedLang) -> bool {
        match (n1, n2) {
            (SlottedLang::Lam(..),SlottedLang::Lam(..)) => true,
            (SlottedLang::App(..),SlottedLang::App(..)) => true,
            (SlottedLang::Var(..),SlottedLang::Var(..)) => true,
            (SlottedLang::Number(n1),SlottedLang::Number(n2)) => n1 == n2,
            (SlottedLang::Symbol(s1),SlottedLang::Symbol(s2)) => s1 == s2,
            _ => false,
        }
    }

    fn ematch(eg: &EGraph<Self>, id: Id, pat: &Pattern<Self>) -> Vec<Subst<Self>> {
        let st = State::default();
        let default = SlotMap::mk(eg.get_leader_semilattice(id).slots.iter().map(|s| (*s, *s)));

        // shouldn't I use the relation here?
        ematch_impl((default, id), pat, st, eg).into_iter().map(final_subst).collect()
    }
}

macro_rules! rw {
    ($name:expr; $lhs:expr => $rhs:expr) => {
        (parse($lhs), pattern_applier(parse($rhs)))
    };
    ($name:expr; $lhs:expr => $rhs:expr, if ! $cond:expr) => {
        (parse($lhs), cond_pattern_applier(parse($rhs), |lhs, subst, eg| !$cond(lhs, subst, eg)))
    };
    ($name:expr; $lhs:expr => $rhs:expr, if $cond:expr) => {
        (parse($lhs), cond_pattern_applier(parse($rhs), $cond))
    };
}

fn rules() -> Vec<Rule<Slotted>> {
    vec![
        rw!("eta"; "(lam $0 (app ?f (var $0)))" => "?f", if !slot_free_in("0", "f")),
        rw!("beta"; "(app (lam $0 ?body) ?e)" => "(let ?e $0 ?body)"),
        rw!("let-intro"; "(app (lam $0 ?body) ?e)" => "(let ?e $0 ?body)"),
        rw!("let-unused"; "(let ?t $0 ?b)" => "?b", if !slot_free_in("0", "b")),
        rw!("let-var-same"; "(let ?e $0 (var $0))" => "?e"),
        rw!("let-app";"(let ?e $0 (app ?a ?b))"=>"(app (let ?e $0 ?a) (let ?e $0 ?b))", if or(slot_free_in("0", "a"), slot_free_in("0", "b"))),
        rw!("let-lam-diff"; "(let ?e $0 (lam $1 ?body))"=>"(lam $1 (let ?e $0 ?body))", if slot_free_in("0", "body")),
        rw!("map-fusion"; "(app (app map ?f) (app (app map ?g) ?arg))" => "(app (app map (lam $0 (app ?f (app ?g (var $0))))) ?arg)"),
        rw!("map-fission"; "(app map (lam $0 (app ?f ?gx)))" => "(lam $2 (app (app map ?f) (app (app map (lam $0 ?gx)) (var $2))))", if !slot_free_in("0", "f"))
    ]
}

pub fn slot_free_in(slot: &str, var: &str) -> impl Cond {
    let s: Slot = slot.parse::<usize>().unwrap();
    let var = Symbol::from(var);
    move |_, subst, _| subst[&var].0.vals().all(|x| x != s)
}

pub fn or(x: impl Cond, y: impl Cond) -> impl Cond {
    move |lhs, subst, eg| x(lhs, subst, eg) || y(lhs, subst, eg)
}

pub trait Cond: Fn(&(SlotMap, Id), &Subst<Slotted>, &EGraph<Slotted>) -> bool + 'static {}
impl<T> Cond for T where T: Fn(&(SlotMap, Id), &Subst<Slotted>, &EGraph<Slotted>) -> bool + 'static {}

#[test]
fn parse_rules() {
    rules();
}

fn eqsat_test(t1: &str, t2: &str) {
    let t1 = parse(t1);
    let t2 = parse(t2);

    let mut eg = EGraph::new();
    let c1 = add_expr(&t1, &mut eg);
    let rules = rules();
    let hook = Box::new(move |eg: &mut EGraph<Slotted>| -> Result<(), StopReason> {
        let c1 = c1.clone();
        let Some(c2) = eg.lookup_term(&t2) else { return Ok(()) };
        if eg.is_equal(c1, c2) { return Err(StopReason::Other("done!".to_string())) }
        Ok(())
    });
    dbg!(eg.hashcons.len());
    let stop_reason = eqsat(&mut eg, &rules, Box::new([hook]), Duration::from_secs(60), usize::MAX, 10);
    dbg!(eg.hashcons.len());
    dbg!(&stop_reason);
    assert_eq!(stop_reason, StopReason::Other("done!".to_string()));
}

pub fn run() {
    let t1 = "(lam $61 (lam $62 (lam $63 (lam $64 (app map (app map (lam $1 (app (var $64) (app (var $63) (app (var $62) (app (var $61) (var $1))))))))))))";
    let t2 = "(lam $61 (lam $62 (lam $63 (lam $64 (lam $4 (app (app map (app map (lam $2 (app (var $64) (app (var $63) (var $2)))))) (app (app map (app map (lam $3 (app (var $62) (app (var $61) (var $3)))))) (var $4))))))))";
    eqsat_test(t1, t2);
}
