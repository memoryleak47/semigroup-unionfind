use super::*;

pub struct OffsetAnalysis;

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
