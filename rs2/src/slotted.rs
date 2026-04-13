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
        SlotMap::mk(self.v.iter().copied().map(|(x, y)| (y, x)))
    }
}

/// SlottedData ///

struct SlottedData {
    group: HashSet<SlotMap>,
    slots: HashSet<Slot>,
}

impl Semilattice for SlottedData {
    type G = SlotMap;

    fn act(g: &Self::G, s: &Self) -> Self { todo!() }

    fn merge(&mut self, _: Self) -> Self { todo!() }

    fn insert_self_edge(&mut self, g: Self::G) -> Self { todo!() }
    fn contains_self_edge(&self, g: &Self::G) -> bool { todo!() }
}

/// SlottedLang ///

#[derive(Hash, PartialEq, Eq)]
enum SlottedLang {
    Lam(Slot, (SlotMap, Id)),
    App((SlotMap, Id), (SlotMap, Id)),
    Var(Slot),
    Sym(String), // TODO intern
}

/// Slotted ///

struct Slotted;

impl Analysis for Slotted {
    type G = SlotMap;
    type S = SlottedData;
    type L = SlottedLang;

    fn canon(n: &Self::L, uf: &Unionfind<Self::S>) -> (Self::G, Self::L) { todo!() }
    fn mk(n: &Self::L) -> Self::S { todo!() }
}
