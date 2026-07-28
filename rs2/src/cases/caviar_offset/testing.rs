use super::*;

fn mk_pvar(x: &str) -> Pat { Pattern::PVar(Symbol::new(x)) }
fn mk_const(x: i64) -> Pat { Pattern::Node(CaviarLang::Const(x), Box::new([])) }
fn mk_symbol(x: &str) -> Pat { Pattern::Node(CaviarLang::Symbol(Symbol::new(x)), Box::new([])) }

fn mk_add(x: Pat, y: Pat) -> Pat {
    let nil = (Offset(0), Id(0));
    Pattern::Node(
        CaviarLang::Add([nil, nil]),
        Box::new([x, y]),
    )
}

fn mk_app(x: Pat, y: Pat) -> Pat {
    let nil = (Offset(0), Id(0));
    Pattern::Node(
        CaviarLang::App([nil, nil]),
        Box::new([x, y]),
    )
}
