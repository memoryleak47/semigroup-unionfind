use crate::*;

type Slot = usize;

/// SlotMap ///

// invariant: bijective & total (every missing key is the identity).
// Thus the key & value sets are equal, we call them the support.
// Every identity pairs are missing in v. v is sorted by keys.
#[derive(Clone, Hash, PartialEq, Eq)]
struct SlotMap {
    v: Vec<(Slot, Slot)>
}

impl SlotMap {
    pub fn mk(it: impl Iterator<Item=(Slot, Slot)>) -> SlotMap {
        let mut v: Vec<(Slot, Slot)> = it.collect();

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

#[derive(PartialEq, Eq)]
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

#[derive(Hash, PartialEq, Eq, Clone)]
enum SlottedLang {
    Lam(Slot, (SlotMap, Id)),
    App((SlotMap, Id), (SlotMap, Id)),
    Var(Slot),
    Sym(Symbol),
}

/// Slotted ///

struct Slotted;

impl Analysis for Slotted {
    type G = SlotMap;
    type S = SlottedData;
    type L = SlottedLang;

    fn canon(n: &Self::L, uf: &Unionfind<Self::S>) -> (Self::G, Self::L) {
        match n {
            SlottedLang::Lam(x, b) => {
                // TODO fix.
                let (g, b) = uf.find(b.clone());
                let mut d = HashMap::new();
                d.insert(*x, 0);

                let mut slots: Vec<Slot> = uf.get_semilattice(&(SlotMap::identity(), b)).slots.into_iter().collect();
                slots.sort();
                for s in slots {
                    let s = g.get(s);
                    if !d.contains_key(&s) {
                        d.insert(s, d.len());
                    }
                }
                let g = complete(d);
                let ginv = g.inverse();
                (g, SlottedLang::Lam(0, (ginv, b)))
            },
            SlottedLang::App(x1, x2) => todo!(),
            SlottedLang::Var(x) => {
                if *x == 0 { (SlotMap::identity(), n.clone()) }
                else {
                    let g = SlotMap::mk([(*x, 0), (0, *x)].into_iter());
                    (g, SlottedLang::Var(0))
                }
            },
            SlottedLang::Sym(_) => (SlotMap::identity(), n.clone()),
        }
    }

    fn mk(n: &Self::L, uf: &Unionfind<Self::S>) -> Self::S {
        let slots = match n {
            SlottedLang::Lam(x, b) => {
                let mut slots = uf.get_semilattice(b).slots;
                slots.remove(&x);
                slots
            },
            SlottedLang::App(x1, x2) => {
                &uf.get_semilattice(x1).slots | &uf.get_semilattice(x2).slots
            },
            SlottedLang::Var(x) => std::iter::once(*x).collect(),
            SlottedLang::Sym(_) => std::iter::empty().collect(),
        };
        let mut group = HashSet::new();
        group.insert(SlotMap::identity());
        SlottedData { slots, group }
    }
}

fn complete(d: HashMap<Slot, Slot>) -> SlotMap {
    todo!()
}
