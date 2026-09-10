use crate::*;

use std::collections::BTreeMap;

type Pat = Pattern<OffsetAnalysis>;

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

#[derive(Clone, Debug)]
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

    fn ematch(eg: &EGraph<Self>, id: Id, pattern: &Pattern<Self>) -> Vec<Subst<Self>> {
        skeleton_ematch(eg, id, pattern).into_iter().flat_map(|(_, skel)| {
            let mut out_subst = HashMap::new();
            let mut constraints = Vec::new();
            let in_g = SymOffset::from_gvar(0);
            record_constraints(in_g, &skel, pattern, &mut constraints, &mut out_subst);
            let gsubst = solve(constraints)?;
            let out: Subst<Self> = out_subst.into_iter().map(|(k, (sym, id))| (k, (resolve(sym, &gsubst), id))).collect();
            Some(out)
        }).collect::<Vec<Subst<Self>>>()
    }

    fn prettyprint(n: &Self::L, children: Box<[String]>) -> String {
        match n {
            OffsetLang::Add(_) => format!("(+ {} {})", &children[0], &children[1]),
            OffsetLang::Const(a) => format!("{a}"),
            OffsetLang::Symbol(s) => s.to_string(),
            OffsetLang::App(_) => format!("(app {} {})", &children[0], &children[1]),
        }
    }

    fn matches(n1: &Self::L, n2: &Self::L) -> bool {
        match (n1, n2) {
            (OffsetLang::App(_),OffsetLang::App(_)) => true,
            (OffsetLang::Add(_),OffsetLang::Add(_)) => true,
            (OffsetLang::Const(_),OffsetLang::Const(_)) => true,
            (OffsetLang::Symbol(s1),OffsetLang::Symbol(s2)) => s1 == s2,
            _ => false,
        }
    }
}

// Skel::Node(N::G, N::L, Box<[(N::G, N::S, Skel<N>)]>),
// gvars are pointers to this  |===================|
// casted to usize, where the N::L is an add node.
// A positive value of a GVar means how much gets propagated upwards in the skel.
type GVar = usize;

#[derive(Clone)]
struct SymOffset {
    const_offset: i64,
    coeffs: BTreeMap<GVar, i64>,
}

fn record_constraints(in_g: SymOffset, skel: &Skel<OffsetAnalysis>, pat: &Pattern<OffsetAnalysis>, constraints: &mut Vec<SymOffset>, subst: &mut HashMap<PVar, (SymOffset, Id)>) {
    match (skel, pat) {
        (Skel::PVar(id), Pattern::PVar(v)) => {
            if let Some((old_g, old_id)) = subst.insert(*v, (in_g.clone(), *id)) {
                assert_eq!(*id, old_id);
                constraints.push(old_g.scale(-1).add(&in_g));
            }
        },
        (Skel::Node(skel_g, skel_node, skel_children), Pattern::Node(pat_node, pat_children)) => {
            let in_g = in_g.add(&SymOffset::from_const(skel_g.0));

            if let (OffsetLang::Const(c1), OffsetLang::Const(c2)) = (skel_node, pat_node) {
                constraints.push(in_g.add(&SymOffset::from_const(c1 - c2)));
                return
            }

            let mut constr = in_g;
            for (triple, p) in skel_children.iter().zip(pat_children.iter()) {
                let (o, _, s) = triple;
                let gg = if matches!(skel_node, OffsetLang::Add(..)) {
                    let gvar = triple as *const _ as usize;
                    let gvar = SymOffset::from_gvar(gvar);
                    constr = constr.add(&gvar);
                    gvar
                } else { SymOffset::zero() };
                record_constraints(gg, s, p, constraints, subst);
            }
            constraints.push(constr);
        },
        _ => {},
    }
}

fn solve(constraints: Vec<SymOffset>) -> Option<HashMap<GVar, SymOffset>> {
    let mut gsubst: HashMap<GVar, SymOffset> = HashMap::new();
    for c in constraints {
        let mut c = simplify(c, &gsubst);
        if let Some((var, coef)) = c.coeffs.pop_last() {
            c = c.scale(-coef); // TODO shouldn't it be -1/coef effectively?
            gsubst.insert(var, c);
        } else if c.const_offset != 0 { return None }
    }
    Some(gsubst)
}

impl SymOffset {
    pub fn zero() -> SymOffset {
        Self::from_const(0)
    }

    pub fn from_const(c: i64) -> SymOffset {
        SymOffset {
            const_offset: c,
            coeffs: Default::default(),
        }
    }

    pub fn from_gvar(g: GVar) -> SymOffset {
        SymOffset {
            const_offset: 0,
            coeffs: std::iter::once((g, 1)).collect(),
        }
    }

    pub fn scale(&self, factor: i64) -> SymOffset {
        let mut out = self.clone();
        if factor == 0 {
            out.const_offset = 0;
            out.coeffs.clear();
        } else {
            out.const_offset *= factor;
            out.coeffs.iter_mut().for_each(|(_, c)| *c *= factor);
        }
        out
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut out = self.clone();
        out.const_offset += other.const_offset;
        for (var, coef) in &other.coeffs {
            let entry = out.coeffs.entry(*var).or_default();
            *entry += coef;
            if *entry == 0 {
                out.coeffs.remove(var);
            }
        }
        out
    }
}

fn simplify(mut sym: SymOffset, gsubst: &HashMap<GVar, SymOffset>) -> SymOffset {
    for (var, val) in gsubst {
        let coef = sym.coeffs.remove(&var).unwrap_or(0);
        sym = sym.add(&val.scale(coef));
    }
    sym
}

fn resolve(s: SymOffset, gsubst: &HashMap<GVar, SymOffset>) -> Offset {
    Offset(simplify(s, &gsubst).const_offset)
}

fn mk_pvar(x: &str) -> Pat { Pattern::PVar(Symbol::new(x)) }
fn mk_const(x: i64) -> Pat { Pattern::Node(OffsetLang::Const(x), Box::new([])) }
fn mk_symbol(x: &str) -> Pat { Pattern::Node(OffsetLang::Symbol(Symbol::new(x)), Box::new([])) }

fn mk_add(x: Pat, y: Pat) -> Pat {
    let nil = (Offset(0), Id(0));
    Pattern::Node(
        OffsetLang::Add([nil, nil]),
        Box::new([x, y]),
    )
}

fn mk_app(x: Pat, y: Pat) -> Pat {
    let nil = (Offset(0), Id(0));
    Pattern::Node(
        OffsetLang::App([nil, nil]),
        Box::new([x, y]),
    )
}

#[test]
// (app a b) matches (app a (add ?x 17)) via ?x = -17 + b
fn test_offset_ematching1() {
    let mut eg: EGraph<OffsetAnalysis> = EGraph::new();

    add_expr(&mk_const(42), &mut eg);

    let (Offset(0), b) = add_expr(&mk_symbol("b"), &mut eg) else { panic!() };
    dbg!(b);

    let e = mk_app(mk_symbol("a"), mk_symbol("b"));
    let a = add_expr(&e, &mut eg);

    let pat = mk_app(mk_symbol("a"), mk_add(mk_pvar("?x"), mk_const(17)));
    eg.rebuild_nodes();
    let matches = OffsetAnalysis::ematch(&eg, a.1, &pat);
    for x in &matches {
        dbg!(x);
    }
    assert_eq!(matches.len(), 1);
    let m = matches[0].clone();
    assert_eq!(m[&Symbol::from("?x")], (Offset(-17), b));
}

#[test]
// (app (a-5) (a+5)) does not match (app ?x ?x)
fn test_offset_ematching2() {
    let mut eg: EGraph<OffsetAnalysis> = EGraph::new();

    add_expr(&mk_const(0), &mut eg);

    let ex = mk_app(
           mk_add(mk_symbol("a"), mk_const(-5)),
           mk_add(mk_symbol("a"), mk_const( 5))
       );
    let a = add_expr(&ex, &mut eg);

    let pat = mk_app(mk_pvar("?x"), mk_pvar("?x"));
    eg.rebuild_nodes();

    let matches = ematch_all::<OffsetAnalysis>(&eg, &pat);
    for x in &matches {
        dbg!(x);
    }
    assert!(matches.is_empty());
}
