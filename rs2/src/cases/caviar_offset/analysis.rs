use super::*;

pub struct CaviarAnalysis;

impl Analysis for CaviarAnalysis {
    type G = Offset;
    type S = Option<i64>;
    type L = CaviarLang;

    fn canon(n: &Self::L, uf: &Unionfind<Self::S>) -> (Self::G, Either<Self::L, Id>) {
        use CaviarLang::*;
        match n {
            Add([x, y]) => {
                let (Offset(ox), x) = uf.find(*x);
                let (Offset(oy), y) = uf.find(*y);
                let o = ox+oy;

                let cx = uf.get_id_semilattice(x);
                let cy = uf.get_id_semilattice(y);
                match (cx, cy) {
                    (Some(cx), Some(cy)) => (Offset(o+cx+cy), Either::L(Constant(0))),
                    (None, Some(cy)) => (Offset(o+cy), Either::R(x)),
                    (Some(cx), None) => (Offset(o+cx), Either::R(y)),
                    (None, None) => (Offset(o), Either::L(Add([(Offset(0), x), (Offset(0), y)]))),
                }
            },
            Sub([x, y]) => (Offset::identity(), Either::L(Sub([uf.find(*x), uf.find(*y)]))),
            Mul([x, y]) => (Offset::identity(), Either::L(Mul([uf.find(*x), uf.find(*y)]))),
            Div([x, y]) => (Offset::identity(), Either::L(Div([uf.find(*x), uf.find(*y)]))),
            Mod([x, y]) => (Offset::identity(), Either::L(Mod([uf.find(*x), uf.find(*y)]))),
            Max([x, y]) => (Offset::identity(), Either::L(Max([uf.find(*x), uf.find(*y)]))),
            Min([x, y]) => (Offset::identity(), Either::L(Min([uf.find(*x), uf.find(*y)]))),
            Lt([x, y]) => (Offset::identity(), Either::L(Lt([uf.find(*x), uf.find(*y)]))),
            Gt([x, y]) => (Offset::identity(), Either::L(Gt([uf.find(*x), uf.find(*y)]))),
            Not(x) => (Offset::identity(), Either::L(Not(uf.find(*x)))),
            Let([x, y]) => (Offset::identity(), Either::L(Let([uf.find(*x), uf.find(*y)]))),
            Get([x, y]) => (Offset::identity(), Either::L(Get([uf.find(*x), uf.find(*y)]))),
            Eq([x, y]) => (Offset::identity(), Either::L(Eq([uf.find(*x), uf.find(*y)]))),
            IEq([x, y]) => (Offset::identity(), Either::L(IEq([uf.find(*x), uf.find(*y)]))),
            Or([x, y]) => (Offset::identity(), Either::L(Or([uf.find(*x), uf.find(*y)]))),
            And([x, y]) => (Offset::identity(), Either::L(And([uf.find(*x), uf.find(*y)]))),
            Constant(c) => (Offset(*c), Either::L(Constant(0))),
            Symbol(s) => (Offset::identity(), Either::L(Symbol(*s))),
        }
    }

    fn mk(n: &Self::L, id: Id, uf: &Unionfind<Self::S>) -> Self::S {
        use CaviarLang::*;
        let get = |x| uf.get_semilattice(x);
        let i2b = |x| x != 0;
        let b2i = |x| x as i64;
        Some(match n {
            Add([x, y]) => get(x)? + get(y)?,
            Sub([x, y]) => get(x)? - get(y)?,
            Mul([x, y]) => get(x)? * get(y)?,
            Div([x, y]) => {
                let yy = get(y)?;
                if yy != 0 { get(x)? / yy } else { return None }
            },
            Mod([x, y]) => get(x)? % get(y)?,
            Max([x, y]) => get(x)?.max(get(y)?),
            Min([x, y]) => get(x)?.min(get(y)?),
            Lt([x, y]) => b2i(get(x)? < get(y)?),
            Gt([x, y]) => b2i(get(x)? > get(y)?),
            Not(x) => b2i(!i2b(get(x)?)),
            Let([x, y]) => b2i(get(x)? <= get(y)?),
            Get([x, y]) => b2i(get(x)? >= get(y)?),
            Eq([x, y]) => b2i(get(x)? == get(y)?),
            IEq([x, y]) => b2i(get(x)? != get(y)?),
            Or([x, y]) => b2i(i2b(get(x)?) || i2b(get(y)?)),
            And([x, y]) => b2i(i2b(get(x)?) && i2b(get(y)?)),
            
            Constant(c) => *c,
            Symbol(_) => return None,
        })
    }

    fn implied_nodes(x: Id, eg: &EGraph<Self>) -> Box<[(Self::G, Self::L)]> {
        let Some(zero) = eg.lookup(&CaviarLang::Constant(0)) else { return Box::new([]) };
        let x = (Offset(0), x);

        let node1 = (Offset(0), CaviarLang::Add([x, zero]));
        let node2 = (Offset(0), CaviarLang::Add([zero, x]));
        if node1 == node2 {
            Box::new([node1])
        } else {
            Box::new([node1, node2])
        }
    }

    fn children_mut(node: &mut CaviarLang) -> Box<[&mut OffsetId]> {
        use CaviarLang::*;
        match node {
            Add([l, r]) => Box::new([l, r]),
            Sub([l, r]) => Box::new([l, r]),
            Mul([l, r]) => Box::new([l, r]),
            Div([l, r]) => Box::new([l, r]),
            Mod([l, r]) => Box::new([l, r]),
            Max([l, r]) => Box::new([l, r]),
            Min([l, r]) => Box::new([l, r]),
            Lt([l, r]) => Box::new([l, r]),
            Gt([l, r]) => Box::new([l, r]),
            Not(x) => Box::new([x]),
            Let([l, r]) => Box::new([l, r]),
            Get([l, r]) => Box::new([l, r]),
            Eq([l, r]) => Box::new([l, r]),
            IEq([l, r]) => Box::new([l, r]),
            Or([l, r]) => Box::new([l, r]),
            And([l, r]) => Box::new([l, r]),
            Constant(_) => Box::new([]),
            Symbol(_) => Box::new([]),
        }
    }

    fn prettyprint(n: &CaviarLang, c: Box<[String]>) -> String {
        use CaviarLang::*;
        match n {
            Add([_, _]) => format!("(+ {} {})", &c[0], &c[1]),
            Sub([_, _]) => format!("(- {} {})", &c[0], &c[1]),
            Mul([l, r]) => format!("(* {} {})", &c[0], &c[1]),
            Div([l, r]) => format!("(/ {} {})", &c[0], &c[1]),
            Mod([l, r]) => format!("(% {} {})", &c[0], &c[1]),
            Max([l, r]) => format!("(max {} {})", &c[0], &c[1]),
            Min([l, r]) => format!("(min {} {})", &c[0], &c[1]),
            Lt([l, r]) => format!("(< {} {})", &c[0], &c[1]),
            Gt([l, r]) => format!("(> {} {})", &c[0], &c[1]),
            Not(x) => format!("(! {})", &c[0]),
            Let([l, r]) => format!("(<= {} {})", &c[0], &c[1]),
            Get([l, r]) => format!("(>= {} {})", &c[0], &c[1]),
            Eq([l, r]) => format!("(== {} {})", &c[0], &c[1]),
            IEq([l, r]) => format!("(!= {} {})", &c[0], &c[1]),
            Or([l, r]) => format!("(|| {} {})", &c[0], &c[1]),
            And([l, r]) => format!("(&& {} {})", &c[0], &c[1]),
            Constant(c) => c.to_string(),
            Symbol(x) => x.to_string(),
        }
    }
}
