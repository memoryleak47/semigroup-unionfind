use egg::*;
use ordered_float::OrderedFloat;

type F64 = OrderedFloat<f64>;
fn f(x: f64) -> F64 { OrderedFloat(x) }

#[derive(Debug)]
struct ConstProp(Option<F64>);

define_language! {
    enum LinearLang {
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        Const(F64),
        Symbol(Symbol),
    }
}

struct LinearAnalysis;

impl Analysis<LinearLang> for LinearAnalysis {
    type Data = ConstProp;

    fn make(eg: &mut EGraph<LinearLang, LinearAnalysis>, n: &LinearLang, i: Id) -> ConstProp {
        use LinearLang::*;
        match n {
            Add([x, y]) => {
                let Some(x) = eg[*x].data.0 else { return ConstProp(None) };
                let Some(y) = eg[*y].data.0 else { return ConstProp(None) };
                ConstProp(Some(x+y))
            },
            Mul([x, y]) => {
                let Some(x) = eg[*x].data.0 else { return ConstProp(None) };
                let Some(y) = eg[*y].data.0 else { return ConstProp(None) };
                ConstProp(Some(x*y))
            },
            Const(f) => ConstProp(Some(*f)),
            Symbol(_) => ConstProp(None),
        }
    }

    fn merge(&mut self, l: &mut ConstProp, r: ConstProp) -> DidMerge {
        match (l.0, r.0) {
            (None, None) => DidMerge(false, false),
            (Some(_), None) => DidMerge(false, true),
            (None, Some(r)) => { l.0 = Some(r); DidMerge(true, false) },
            (Some(l), Some(r)) => { assert_eq!(l, r); DidMerge(false, false) },
        }
    }

    fn modify(egraph: &mut EGraph<LinearLang, LinearAnalysis>, id: Id) {
        if let Some(c) = egraph[id].data.0 {
            let added = egraph.add(LinearLang::Const(c));
            egraph.union(id, added);

            // I think we lose to much info by pruning in this example.
            // egraph[id].nodes.retain(|n| n.is_leaf());
        }

    }
}

fn is_close(x: F64, y: F64) -> bool { (x - y).abs() <= 1e-10 }

fn main_mini() {
    let s = |i| LinearLang::Symbol(Symbol::new(format!("x{i}")));
    let mut eg: EGraph<LinearLang, LinearAnalysis> = EGraph::new(LinearAnalysis);

    let one = eg.add(LinearLang::Const(f(1.)));

    let s0 = eg.add(s(0));
    let s1 = eg.add(s(1));

    let s0_1 = eg.add(LinearLang::Add([s0, one]));
    let s1_1 = eg.add(LinearLang::Add([s1, one]));
    eg.union(s0_1, s1_1);

    let runner = Runner::<LinearLang, LinearAnalysis, ()>::new(LinearAnalysis).with_egraph(eg).run(&rules());
    dbg!(&runner.stop_reason);
    let eg = runner.egraph;

    dbg!(eg.find(s0));
    dbg!(eg.find(s1));
}

fn main() {
    let s = |i| LinearLang::Symbol(Symbol::new(format!("x{i}")));
    let mut eg: EGraph<LinearLang, LinearAnalysis> = EGraph::new(LinearAnalysis);

    let seven = eg.add(LinearLang::Const(f(7.)));
    let four = eg.add(LinearLang::Const(f(4.)));
    let five = eg.add(LinearLang::Const(f(5.)));

    for i in 0..1000 {
        let si = eg.add(s(i));
        let sip = eg.add(s(i+1));

        let si7 = eg.add(LinearLang::Add([si, seven]));
        let sip4 = eg.add(LinearLang::Add([sip, four]));
        eg.union(si7, sip4);
    }

    let s0 = eg.add(s(0));
    let s0_5 = eg.add(LinearLang::Mul([five, s0]));
    let s1000 = eg.add(s(1000));
    eg.union(s0_5, s1000);

    let runner = Runner::<LinearLang, LinearAnalysis, ()>::new(LinearAnalysis).with_egraph(eg).run(&rules());
    dbg!(&runner.stop_reason);
    let eg = runner.egraph;

    let result = eg[s1000].data.0.unwrap();
    assert!(is_close(result, f(3750.)));
}

fn rules() -> Vec<Rewrite<LinearLang, LinearAnalysis>> {
    vec![
        rewrite!("+-comm"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rewrite!("*-comm"; "(* ?a ?b)" => "(* ?b ?a)"),

        rewrite!("+-assoc1"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rewrite!("+-assoc2"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),

        rewrite!("*-assoc1"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rewrite!("*-assoc2"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),

        rewrite!("distr1"; "(* (+ ?a ?b) ?f)" => "(+ (* ?a ?f) (* ?b ?f))"),
        rewrite!("distr2"; "(+ (* ?a ?f) (* ?b ?f))" => "(* (+ ?a ?b) ?f)"),

        // Is this actually the best rule to solve equations of the form `x+1 = y+4` to `x = y+3`?
        rewrite!("expand"; "?a" => "(+ ?a (+ (* -1 ?a) ?a))"),
        rewrite!("cancel"; "(+ ?a (* -1 ?a))" => "0"),

        rewrite!("0-add"; "(+ ?a 0)" => "?a"),
        rewrite!("0-mul"; "(* ?a 0)" => "0"),
        rewrite!("1-mul"; "(* ?a 1)" => "?a"),
    ]
}
