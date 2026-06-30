use crate::*;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Offset(i64);

impl Offset {
    pub fn apply(&self, x: i64) -> i64 {
        x + self.0
    }
}

impl Group for Offset {
    fn identity() -> Offset {
        Offset(0)
    }

    fn compose(l: &Offset, r: &Offset) -> Offset {
        Offset(l.0 + r.0)
    }

    fn inverse(&self) -> Offset {
        Offset(-self.0)
    }
}

struct ConstProp(Option<i64>);

impl Semilattice for ConstProp {
    type G = Offset;

    fn act(g: &Self::G, s: &Self) -> Self {
        match s {
            ConstProp(Some(x)) => ConstProp(Some(g.apply(*x))),
            ConstProp(None) => ConstProp(None),
        }
    }

    fn merge(&mut self, other: Self) -> bool {
        let ConstProp(Some(o)) = other else { return false };

        match *self {
            ConstProp(None) => {
                *self = ConstProp(Some(o));
                true
            },
            ConstProp(Some(x)) => {
                assert_eq!(x, o);
                false
            },
        }
    }

    fn insert_self_edge(&mut self, g: Self::G) {
        assert!(g == Offset(0));
    }

    fn contains_self_edge(&self, g: &Self::G) -> bool {
        *g == Offset(0)
    }
}

type OffsetId = (Offset, Id);

#[derive(Hash, PartialEq, Eq, Clone, Copy)]
enum OffsetLang {
    Add([OffsetId; 2]),
    Const(i64),

    // Symbol + App are able to express anything.
    Symbol(Symbol),
    App([OffsetId; 2]),
}

struct OffsetAnalysis;

impl Analysis for OffsetAnalysis {
    type G = Offset;
    type S = ConstProp;
    type L = OffsetLang;

    fn canon(n: &Self::L, uf: &Unionfind<Self::S>) -> (Self::G, Either<Self::L, Id>) {
        match n {
            OffsetLang::Add([x, y]) => {
                let (Offset(ox), x) = uf.find(*x);
                let (Offset(oy), y) = uf.find(*y);
                let o = ox+oy;

                let cx = uf.get_id_semilattice(x).0;
                let cy = uf.get_id_semilattice(y).0;
                match (cx, cy) {
                    (Some(cx), Some(cy)) => (Offset(o+cx+cy), Either::L(OffsetLang::Const(0))),
                    (None, Some(cy)) => (Offset(o+cy), Either::R(x)),
                    (Some(cx), None) => (Offset(o+cx), Either::R(y)),
                    (None, None) => (Offset(o), Either::L(OffsetLang::Add([(Offset(0), x), (Offset(0), y)]))),
                }
            },
            OffsetLang::App([x, y]) => (Offset::identity(), Either::L(OffsetLang::App([uf.find(*x), uf.find(*y)]))),
            OffsetLang::Const(c) => (Offset(*c), Either::L(OffsetLang::Const(0))),
            OffsetLang::Symbol(s) => (Offset::identity(), Either::L(OffsetLang::Symbol(*s))),
        }
    }

    fn mk(n: &Self::L, id: Id, uf: &Unionfind<Self::S>) -> Self::S {
        match n {
            OffsetLang::Add([x, y]) => {
                let Some(x) = uf.get_semilattice(x).0 else { return ConstProp(None) };
                let Some(y) = uf.get_semilattice(y).0 else { return ConstProp(None) };
                ConstProp(Some(x+y))
            },
            OffsetLang::App(_) => ConstProp(None),
            OffsetLang::Const(c) => ConstProp(Some(*c)),
            OffsetLang::Symbol(_) => ConstProp(None),
        }
    }
}

/// E-Matching:

use std::collections::BTreeMap;

type PVar = String;
type MVar = usize; // like a PVar, just for G elements.

enum Pattern {
    PVar(PVar),

    Add([Box<Pattern>; 2]),
    Const(i64),
    Symbol(Symbol),
    App([Box<Pattern>; 2]),
}

#[derive(Hash, PartialEq, Eq, Clone)]
enum PolyOffsetLang {
    Add([PolyOffsetId; 2]),
    Const(i64),

    // Symbol + App are able to express anything.
    Symbol(Symbol),
    App([PolyOffsetId; 2]),
}

fn ematch(x: Id, pat: &Pattern, eg: &EGraph<OffsetAnalysis>) -> Vec<Subst> {
    let g = PolyOffset::mvar(0);
    let subst = HashMap::new();

    let mut mvar_count = 1;
    ematch_impl((g, x), pat, eg, subst, &mut mvar_count)
}

fn polify((g, y): &OffsetId) -> PolyOffsetId {
    (PolyOffset::from_offset(*g), *y)
}

fn enode_to_poly(n: &OffsetLang) -> PolyOffsetLang {
    use OffsetLang::*;
    match n {
        Add([l, r]) => PolyOffsetLang::Add([polify(l), polify(r)]),
        Const(c) => PolyOffsetLang::Const(*c),
        Symbol(s) => PolyOffsetLang::Symbol(*s),
        App([l, r]) => PolyOffsetLang::App([polify(l), polify(r)]),
    }
}

fn enodes_of((g, x): (PolyOffset, Id), eg: &EGraph<OffsetAnalysis>, mvar_count: &mut usize) -> Vec<(PolyOffset, PolyOffsetLang)> {
    let mut out = Vec::new();
    for (n, (g2, i)) in eg.hashcons.iter() {
        let n = enode_to_poly(n);
        let g2 = PolyOffset::from_offset(*g2);
        if *i == x {
            // out = g*x
            // n = g2*x -> g2⁻¹*n = x
            // out = g*g2⁻¹*n
            out.push((g.compose(&g2.inverse()), n.clone()));
        }
    }

    if let Some((gzero, zero)) = eg.lookup(&OffsetLang::Const(0)) {
        let o1 = PolyOffset::mvar(*mvar_count); *mvar_count += 1;
        let o2 = PolyOffset::mvar(*mvar_count); *mvar_count += 1;
        let sum = o1.compose(&o2);

        let new_x: PolyOffsetId = (o1.compose(&g), x);
        let new_zero: PolyOffsetId = (o2.compose(&PolyOffset::from_offset(gzero)), zero);
        out.push((sum.inverse(), PolyOffsetLang::Add([new_x.clone(), new_zero.clone()])));
        out.push((sum.inverse(), PolyOffsetLang::Add([new_zero.clone(), new_x.clone()])));
    }

    out
}

fn ematch_impl((g, x): (PolyOffset, Id), pat: &Pattern, eg: &EGraph<OffsetAnalysis>, subst: Subst, mvar_count: &mut usize) -> Vec<Subst> {
    // ways how this can work:

    // let's say we have a bunch of e-nodes n with x = g'*n.

    // 1. pat is a pvar.
    // 2. g = g' for some node n which also matches the top-level pat-node of pat.
    // 3. top-level node of the pattern is Add, and we invent a fresh mvar offset node for it (either on the left or the right).
    let mut out = Vec::new();

    match pat {
        // 1.
        Pattern::PVar(v) => {
            let mut subst = subst;
            if let Some((g2, x2)) = subst.insert(v.to_string(), (g.clone(), x)) {
                if x != x2 { return Vec::new() }
                return constrain(subst, g, g2).into_iter().collect()
            } else {
                return vec![subst]
            }
        }

        // 2.
        Pattern::Symbol(s) => {
            for (g2, n) in enodes_of((g.clone(), x), eg, mvar_count) {
                if PolyOffsetLang::Symbol(*s) == n {
                    out.extend(constrain(subst.clone(), g.clone(), g2));
                }
            }
        },

        Pattern::Const(c) => {
            // goal: g*x = c
            for (g2, n) in enodes_of((g.clone(), x), eg, mvar_count) {
                // g2*n = g*x
                // new goal: g2*n = c
                if let PolyOffsetLang::Const(c2) = n {
                    // new goal: g2*c2 = c
                    out.extend(constrain(subst.clone(), g2.compose(&PolyOffset::from_const(c2)), PolyOffset::from_const(*c)));
                }
            }
        },

        Pattern::App([l, r]) => {
            for (g2, n) in enodes_of((g.clone(), x), eg, mvar_count) {
                if let PolyOffsetLang::App([li, ri]) = n {
                    let mut acc = ematch_impl(li, l, eg, subst.clone(), mvar_count);
                    out.extend(acc.into_iter().map(|subst|
                        ematch_impl(ri.clone(), r, eg, subst, mvar_count)
                    ).flatten());
                }
            }
        },

        // 3. (and 2)
        Pattern::Add([l, r]) => {
            for (g2, n) in enodes_of((g.clone(), x), eg, mvar_count) {
                if let PolyOffsetLang::Add([li, ri]) = n {
                    let mut acc = ematch_impl(li, l, eg, subst.clone(), mvar_count);
                    out.extend(acc.into_iter().map(|subst|
                        ematch_impl(ri.clone(), r, eg, subst, mvar_count)
                    ).flatten());
                }
            }
        }
    }
    out
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct PolyOffset {
    const_offset: i64,
    vars: BTreeMap<MVar, i64>,
}

type PolyOffsetId = (PolyOffset, Id);

impl PolyOffset {
    pub fn mvar(v: MVar) -> PolyOffset {
        PolyOffset {
            const_offset: 0,
            vars: [(v, 1)].into_iter().collect(),
        }
    }

    pub fn var_idx(&self, m: MVar) -> i64 {
        self.vars.get(&m).copied().unwrap_or(0)
    }

    pub fn from_offset(o: Offset) -> PolyOffset {
        PolyOffset::from_const(o.0)
    }

    pub fn from_const(o: i64) -> PolyOffset {
        PolyOffset {
            const_offset: o,
            vars: BTreeMap::new(),
        }
    }

    pub fn neutral() -> PolyOffset {
        PolyOffset {
            const_offset: 0,
            vars: BTreeMap::new(),
        }
    }

    pub fn inverse(&self) -> PolyOffset {
        self.scale(-1)
    }

    pub fn scale(&self, x: i64) -> PolyOffset {
        PolyOffset {
            const_offset: self.const_offset * x,
            vars: self.vars.iter().map(|(v, n)| (*v, n * x)).collect(),
        }
    }

    pub fn substitute(&self, x: MVar, val: PolyOffset) -> PolyOffset {
        let mut new = self.clone();
        let Some(coef) = new.vars.remove(&x) else { return new };
        new = new.compose(&val.scale(coef));
        new
    }

    pub fn compose(&self, other: &PolyOffset) -> PolyOffset {
        let mut vars = BTreeMap::new();
        for &v in self.vars.keys().chain(other.vars.keys()) {
            let val = self.var_idx(v) + other.var_idx(v);
            if val != 0 {
                vars.insert(v, val);
            }
        }

        PolyOffset {
            const_offset: self.const_offset + other.const_offset,
            vars,
        }
    }
}

type Subst = HashMap<PVar, (PolyOffset, Id)>;

fn constrain(mut subst: Subst, lhs: PolyOffset, rhs: PolyOffset) -> Option<Subst> {
    let mut e = lhs.compose(&rhs.inverse());
    if e == PolyOffset::neutral() { return Some(subst) }
    let Some(&v) = e.vars.keys().next() else { return None };
    let coef = e.vars.remove(&v).unwrap();
    let rest = e.scale(-coef);

    for (_, (xx, _)) in subst.iter_mut() {
        *xx = xx.substitute(v, rest.clone());
    }
    Some(subst)
}

fn subst_to_string(subst: &Subst) -> String {
    let mut s = String::from('{');
    for (var, (o, id)) in subst.iter() {
        s.push_str(&format!("{var} = {} + id{}, ", poly_offset_to_string(o), id.0))
    }
    s.push('}');
    s
}

fn poly_offset_to_string(o: &PolyOffset) -> String {
    let mut s = if o.const_offset != 0 { o.const_offset.to_string() } else { String::new() };
    for (v, coef) in &o.vars {
        if *coef != 1 {
            s.push_str(&format!("+{coef}*M{v}"));
        } else {
            s.push_str(&format!("+M{v}"));
        }
    }
    s
}

#[test]
fn test_offset_ematching() {
    let mut eg = EGraph::new();

    eg.add(&OffsetLang::Const(42));

    let a = eg.add(&OffsetLang::Symbol(Symbol::from("a")));

    let pat = Pattern::Add([
        Box::new(Pattern::PVar(String::from("?x"))),
        Box::new(Pattern::PVar(String::from("?y"))),
    ]);
    for c in eg.classes() {
        for x in ematch(c, &pat, &eg) {
            eprintln!("{}", subst_to_string(&x));
        }
    }
}
