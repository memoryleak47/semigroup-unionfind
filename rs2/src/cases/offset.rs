use crate::*;

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
        let t = skeleton_ematch(eg, id, pattern);
        dbg!(t);

        todo!()
    }
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
fn test_offset_ematching() {
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
