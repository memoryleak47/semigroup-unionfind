use egg::*;

type TrivialLang = SymbolLang;

fn zero() -> RecExpr<TrivialLang> {
    "zero".parse().unwrap()
}

const PROOFS: bool = true;
pub fn proofs_main() {
    let mut t1 = String::from("zero");
    for i in 0..3 {
        t1 = format!("(add {t1} a{i})");
    }
    for i in 0..3 {
        t1 = format!("(add (neg a{i}) {t1})");
    }

    let t1 = t1.parse().unwrap();
    let t2 = zero();
    let runner = Runner::<_, _, ()>::new(());
    let runner = if PROOFS { runner.with_explanations_enabled() } else { runner.with_explanations_disabled() };
    let runner = runner.with_expr(&t1).with_expr(&t2).with_iter_limit(5).run(&rules());
    dbg!(runner.egraph.total_size());
    dbg!(runner.iterations.len());
    dbg!(&runner.stop_reason);
}

fn rules() -> Vec<Rewrite<TrivialLang, ()>> {
    vec![
        rewrite!("add-neg"; "(add (neg ?a) ?a)" => "zero"),
        rewrite!("add-zero"; "(add ?a zero)" => "?a"),
        rewrite!("add-comm"; "(add ?a ?b)" => "(add ?b ?a)"),
        rewrite!("add-assoc1"; "(add (add ?a ?b) ?c)" => "(add ?a (add ?b ?c))"),
        rewrite!("add-assoc2"; "(add ?a (add ?b ?c))" => "(add (add ?a ?b) ?c)"),
    ]
}
