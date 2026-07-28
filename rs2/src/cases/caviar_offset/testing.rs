use super::*;

type Pat = Pattern<OffsetAnalysis>;

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
