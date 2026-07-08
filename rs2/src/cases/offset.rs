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

    fn implied_nodes(x: Id, eg: &EGraph<Self>) -> Box<[(Self::G, Self::L)]> {
        let Some(zero) = eg.lookup(&OffsetLang::Const(0)) else { return Box::new([]) };
        let x = (Offset(0), x);

        let node1 = (Offset(0), OffsetLang::Add([x, zero]));
        let node2 = (Offset(0), OffsetLang::Add([zero, x]));
        if node1 == node2 {
            Box::new([node1])
        } else {
            Box::new([node1, node2])
        }
    }

    fn children_mut(node: &mut OffsetLang) -> Box<[&mut OffsetId]> {
        match node {
            OffsetLang::Add([l, r]) => Box::new([l, r]),
            OffsetLang::Const(_) => Box::new([]),
            OffsetLang::Symbol(_) => Box::new([]),
            OffsetLang::App([l, r]) => Box::new([l, r]),
        }
    }
}

/// E-Matching:

use std::collections::BTreeMap;

struct OffsetMatcher;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct SymOffset {
    const_offset: i64,
    vars: BTreeMap<GVar, i64>,
}

impl Matcher<OffsetAnalysis> for OffsetMatcher {
    type SymG = SymOffset;

    fn compose(l: &Self::SymG, r: &Self::SymG) -> Self::SymG {
        let mut vars = BTreeMap::new();
        for &v in l.vars.keys().chain(r.vars.keys()) {
            let val = l.var_idx(v) + r.var_idx(v);
            if val != 0 {
                vars.insert(v, val);
            }
        }

        SymOffset {
            const_offset: l.const_offset + r.const_offset,
            vars,
        }
    }

    fn inverse(x: &Self::SymG) -> Self::SymG {
        x.scale(-1)
    }

    fn from_gvar(v: GVar) -> Self::SymG {
        SymOffset {
            const_offset: 0,
            vars: [(v, 1)].into_iter().collect(),
        }
    }

    fn from_g(&Offset(o): &Offset) -> Self::SymG {
        SymOffset {
            const_offset: o,
            vars: BTreeMap::new(),
        }
    }

    fn expand(node: &OffsetLang, mut fresh_gvar: impl FnMut() -> GVar) -> (/*up*/Self::SymG, /*children*/Box<[Self::SymG]>) {
        if let OffsetLang::Add(_) = node {
            let o1 = OffsetMatcher::from_gvar(fresh_gvar());
            let o2 = OffsetMatcher::from_gvar(fresh_gvar());
            (OffsetMatcher::compose(&o1, &o2), Box::new([OffsetMatcher::inverse(&o1), OffsetMatcher::inverse(&o2)]))
        } else {
            let arity = OffsetAnalysis::children_mut(&mut node.clone()).len();
            (SymOffset::zero(), vec![SymOffset::zero(); arity].into_boxed_slice())
        }
    }

    fn solve<'eg>(mut state: State<'eg, OffsetAnalysis, Self>) -> Option<Subst<OffsetAnalysis>> {
        let mut assignment: Assignment = BTreeMap::new();
        for (x, s) in &state.gs_constraints {
            if let ConstProp(Some(o)) = s {
                assignment.insert(*x, OffsetMatcher::from_g(&Offset(*o)));
            }
        }

        for d in &state.g_constraints {
            let d = d.substitute(&assignment);
            assignment = constrain(d, assignment)?;
        }

        Some(state.subst.into_iter().map(|(pvar, (symoff, i))| {
            let symoff = symoff.substitute(&assignment);
            let val = Offset(symoff.const_offset); // all vars we instantiate by zero.
            (pvar, (val, i))
        }).collect())
    }
}

type Assignment = BTreeMap<GVar, SymOffset>;

impl SymOffset {
    fn zero() -> SymOffset {
        SymOffset {
            const_offset: 0,
            vars: BTreeMap::new(),
        }
    }

    fn scale(&self, x: i64) -> SymOffset {
        SymOffset {
            const_offset: self.const_offset * x,
            vars: self.vars.iter().map(|(v, n)| (*v, n * x)).filter(|(v, n)| *n != 0).collect(),
        }
    }

    fn var_idx(&self, m: GVar) -> i64 {
        self.vars.get(&m).copied().unwrap_or(0)
    }

    fn substitute(&self, assignment: &Assignment) -> SymOffset {
        let mut new = self.clone();
        for (v, val) in assignment {
            let coef = new.vars.remove(&v).unwrap_or(0);
            new = OffsetMatcher::compose(&new, &val.scale(coef));
        }
        new
    }
}

fn constrain(mut e: SymOffset, mut assignment: Assignment) -> Option<Assignment> {
    if e == SymOffset::zero() { return Some(assignment) }

    let Some(&v) = e.vars.keys().next() else { return None };
    let coef = e.vars.remove(&v).unwrap();
    let rest = e.scale(-coef);

    assignment.insert(v, rest.clone());
    let assign_clone = assignment.clone();

    for (_, xx) in assignment.iter_mut() {
        *xx = xx.substitute(&assign_clone);
    }
    Some(assignment)
}

fn mk_pvar(x: &str) -> Pattern<OffsetLang> { Pattern::PVar(Symbol::new(x)) }
fn mk_const(x: i64) -> Pattern<OffsetLang> { Pattern::Node(OffsetLang::Const(x), Box::new([])) }
fn mk_symbol(x: &str) -> Pattern<OffsetLang> { Pattern::Node(OffsetLang::Symbol(Symbol::new(x)), Box::new([])) }

fn mk_add(x: Pattern<OffsetLang>, y: Pattern<OffsetLang>) -> Pattern<OffsetLang> {
    let nil = (Offset(0), Id(0));
    Pattern::Node(
        OffsetLang::Add([nil, nil]),
        Box::new([x, y]),
    )
}

fn mk_app(x: Pattern<OffsetLang>, y: Pattern<OffsetLang>) -> Pattern<OffsetLang> {
    let nil = (Offset(0), Id(0));
    Pattern::Node(
        OffsetLang::App([nil, nil]),
        Box::new([x, y]),
    )
}

#[test]
fn test_offset_ematching() {
    let mut eg: EGraph<OffsetAnalysis> = EGraph::new();

    add_expr(&mk_const(42), &mut eg);

    let (Offset(0), b) = add_expr(&mk_symbol("b"), &mut eg) else { panic!() };
    dbg!(b);

    let e = mk_app(mk_symbol("a"), mk_symbol("b"));
    let a = add_expr(&e, &mut eg);

    let pat = mk_app(mk_symbol("a"), mk_add(mk_pvar("?x"), mk_const(17)));
    let matches = ematch::<OffsetAnalysis, OffsetMatcher>(&pat, &eg);
    for x in &matches {
        dbg!(x);
    }
    assert_eq!(matches.len(), 1);
    let m = matches[0].clone();
    assert_eq!(m[&Symbol::from("?x")], (Offset(-17), b));
}
