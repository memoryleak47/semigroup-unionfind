use super::*;

#[derive(Clone, Debug)]
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
                } else if let Ok(n) = x.parse::<i64>() {
                    things[i] = Thing::Parsed(Pat::Node(CaviarLang::Constant(n), Box::new([])));
                } else if x.chars().next().unwrap().is_alphabetic() && *x != "max" && *x != "min" {
                    things[i] = Thing::Parsed(Pat::Node(CaviarLang::Symbol(crate::Symbol::new(x)), Box::new([])));
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

use serde_json::Value;
use std::fs::File;
use std::io::BufReader;
use std::error::Error;

pub fn parse_expressions(filename: &str) -> Vec<(Pat, Pat)> {
    let file = File::open(filename).unwrap();
    let reader = BufReader::new(file);
    let val: Value = serde_json::from_reader(reader).unwrap();

    let mut out = Vec::new();
    for x in val.as_array().unwrap() {
        // TODO: use x["rules"] aswell.
        let x = &x["expression"];
        let start = x["start"].as_str().unwrap();
        let end = x["end"].as_str().unwrap();

        let start = parse(start);
        let end = parse(end);

        out.push((start, end));
    }
    out
}
