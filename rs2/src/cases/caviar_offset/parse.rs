use super::*;

#[derive(Clone)]
enum Thing<'a> {
    Unparsed(&'a str),
    Parsed(Pat),
}

pub fn parse(s: &str) -> Pat {
    use Thing::*;
    use CaviarLang::*;

    let nil = (Offset(0), Id(0));
    let s = s.replace("(", " ( ").replace(")", " ) ");
    let mut things: Vec<Thing<'_>> = s.split(" ").map(|x| x.trim()).filter(|x| x.len() > 0).map(Thing::Unparsed).collect();
    for i in (0..things.len()).rev() {
        match &things[i..] {
            [Unparsed("("), Unparsed(op), Parsed(p1), Parsed(p2), Unparsed(")"), rst@..] => {
                let node_ty = match *op {
                    "+" => Add,
                    "-" => Sub,
                    "*" => Mul,
                    "/" => Div,
                    "%" => Mod,
                    "max" => Max,
                    "min" => Min,
                    "<" => Lt,
                    ">" => Gt,
                    "!" => panic!("binary `!` doesn't exist"),
                    "<=" => Let,
                    ">=" => Get,
                    "==" => Eq,
                    "!=" => IEq,
                    "||" => Or,
                    "&&" => And,
                    op => panic!("unknown operand {op}"),
                };
                let p = Thing::Parsed(Pat::Node(node_ty([nil, nil]), Box::new([p1.clone(), p2.clone()])));
                let rst: Box<[Thing<'_>]> = rst.iter().cloned().collect();
                things.truncate(i);
                things.push(p);
                things.extend(rst);
            }
            [Unparsed("("), Unparsed("!"), Parsed(p1), Unparsed(")"), rst@..] => {
                let p = Thing::Parsed(Pat::Node(CaviarLang::Not(nil), Box::new([p1.clone()])));
                let rst: Box<[Thing<'_>]> = rst.iter().cloned().collect();
                things.truncate(i);
                things.push(p);
                things.extend(rst);
            },
            [Unparsed(x), ..] => {
                if x.starts_with("?") {
                    things[i] = Thing::Parsed(Pat::PVar(crate::Symbol::new(x)));
                } else if let Ok(n) = x.parse::<i64>() {
                    things[i] = Thing::Parsed(Pat::Node(CaviarLang::Constant(n), Box::new([])));
                } else if x.chars().next().unwrap().is_alphabetic() && *x != "max" && *x != "min" {
                    things[i] = Thing::Parsed(Pat::Node(CaviarLang::Symbol(crate::Symbol::new(x)), Box::new([])));
                }
            },
            _ => {},
        }
    }
    assert_eq!(things.len(), 1);
    let Parsed(x) = things.into_iter().next().unwrap() else { panic!() };
    x
}
