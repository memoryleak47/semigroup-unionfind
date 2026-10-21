use egg::*;

type L = SymbolLang;

pub fn rules() -> Vec<Rewrite<L, ()>> {
    vec![
        rewrite!("add-neg"; "(add (neg ?a) ?a)" => "?a"),
        rewrite!("add-zero"; "(add ?a zero)" => "?a"),
        rewrite!("add-comm"; "(add ?a ?b)" => "(add ?b ?a)"),
        rewrite!("add-assoc1"; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))"),
        rewrite!("add-assoc2";  "(add ?a (add ?b ?c))" => "(add (add ?a ?b) ?c)"),
    ]
}

fn main() {
    let t: RecExpr<L> ="(add (neg a1) (add (neg a0) (add (add zero a0) a1)))".parse().unwrap();

    let t2: RecExpr<L> = "zero".parse().unwrap();
    let rules = rules();

    let runner: Runner<L, ()> = Runner::new(()).with_explanations_enabled().with_expr(&t).with_scheduler(SimpleScheduler).with_iter_limit(5).run(&rules);
    dbg!(&runner.egraph.total_size());
    dbg!(&runner.stop_reason);
    assert_eq!(runner.egraph.lookup_expr(&t).unwrap(), runner.egraph.lookup_expr(&t2).unwrap());
}
