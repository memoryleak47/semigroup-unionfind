use super::*;

type Pat = Pattern<Slotted>;

#[derive(Clone, Debug)]
enum Thing<'a> {
    Unparsed(&'a str),
    Parsed(Pat),
    Slot(Slot),
}

pub fn parse(s: &str) -> Pat {
    use Thing::*;
    use SlottedLang::*;

    let nil = (SlotMap::mk(std::iter::empty()), Id(0));
    let s = s.replace("(", " ( ").replace(")", " ) ");
    let mut things: Vec<Thing<'_>> = s.split(" ").map(|x| x.trim()).filter(|x| x.len() > 0).map(Thing::Unparsed).collect();
    for i in (0..things.len()).rev() {
        match &things[i..] {
            [Unparsed("("), Unparsed("app"), Parsed(p1), Parsed(p2), Unparsed(")"), rst@..] => {
                let p = Thing::Parsed(Pat::Node(SlottedLang::App(nil.clone(), nil.clone()), Box::new([p1.clone(), p2.clone()])));
                let rst: Box<[Thing<'_>]> = rst.iter().cloned().collect();
                things.truncate(i);
                things.push(p);
                things.extend(rst);
            }
            [Unparsed("("), Unparsed("lam"), Slot(v), Parsed(p2), Unparsed(")"), rst@..] => {
                let p = Thing::Parsed(Pat::Node(SlottedLang::Lam(*v, nil.clone()), Box::new([p2.clone()])));
                let rst: Box<[Thing<'_>]> = rst.iter().cloned().collect();
                things.truncate(i);
                things.push(p);
                things.extend(rst);
            }
            [Unparsed("("), Unparsed("var"), Slot(v), Unparsed(")"), rst@..] => {
                let p = Thing::Parsed(Pat::Node(SlottedLang::Var(*v), Box::new([])));
                let rst: Box<[Thing<'_>]> = rst.iter().cloned().collect();
                things.truncate(i);
                things.push(p);
                things.extend(rst);
            }
            [Unparsed("("), Unparsed("let"), Parsed(p1), Slot(v), Parsed(p2), Unparsed(")"), rst@..] => {
                let p = Thing::Parsed(Pat::Node(SlottedLang::Let(nil.clone(), *v, nil.clone()), Box::new([p1.clone(), p2.clone()])));
                let rst: Box<[Thing<'_>]> = rst.iter().cloned().collect();
                things.truncate(i);
                things.push(p);
                things.extend(rst);
            }
            [Unparsed("("), Parsed(p), Unparsed(")"), rst@..] => {
                let p = Parsed(p.clone());
                let rst: Box<[Thing<'_>]> = rst.iter().cloned().collect();
                things.truncate(i);
                things.push(p);
                things.extend(rst);
            },
            [Unparsed(x), ..] => {
                if x.starts_with("?") {
                    things[i] = Thing::Parsed(Pat::PVar(crate::Symbol::new(x)));
                } else if x.starts_with("$") {
                    things[i] = Thing::Slot(x[1..].parse::<usize>().unwrap());
                } else if let Ok(n) = x.parse::<u32>() {
                    things[i] = Thing::Parsed(Pat::Node(SlottedLang::Number(n), Box::new([])));
                } else if x.chars().next().unwrap().is_alphabetic() && *x != "app" && *x != "lam" && *x != "let" && *x != "var" {
                    things[i] = Thing::Parsed(Pat::Node(SlottedLang::Symbol(crate::Symbol::new(x)), Box::new([])));
                }
            },
            _ => {},
        }
    }
    if things.len() != 1 {
        panic!("Failed to parse with remaining state {things:?}");
    }
    let Parsed(x) = things.into_iter().next().unwrap() else { panic!() };
    x
}
