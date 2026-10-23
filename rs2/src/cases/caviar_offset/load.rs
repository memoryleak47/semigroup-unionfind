use super::*;

fn split_nodes(s: &str) -> Vec<CaviarLang> {
    let s = s.trim();
    assert!(s.starts_with("["));
    assert!(s.ends_with("]"));
    let s = &s[..s.len()-1][1..];

    let mut out = Vec::new();
    let mut buffer = String::new();
    let mut parencount = 0;

    for (i, x) in s.chars().enumerate() {
        if x == ',' && parencount == 0 {
            out.push(parse_node(&buffer));
            buffer = String::new();
        } else {
            buffer.push(x);
            if x == '(' { parencount += 1; }
            if x == ')' { parencount -= 1; }
        }
    }
    out.push(parse_node(&buffer));
    out
}

fn parse_node(node: &str) -> CaviarLang {
    let node = node.trim();

    if node.starts_with("Symbol") {
        let content = node.split("\"").nth(1).unwrap();
        return CaviarLang::Symbol(content.into())
    }
    if node.starts_with("Constant") {
        let i1 = node.find("(").unwrap();
        let i2 = node.find(")").unwrap();
        let c = node[i1+1..i2].parse::<i64>().unwrap();
        return CaviarLang::Constant(c)
    }
    if node.starts_with("Not") {
        let i = &node[..node.len()-1][4..];
        let i = i.trim().parse::<usize>().unwrap();
        return CaviarLang::Not((Offset(0), Id(i)))
    }

    let i1 = node.find("[").unwrap();
    let i2 = node.find(",").unwrap();
    let i3 = node.find("]").unwrap();
    let op = match node[..i1-1].trim() {
        "Add" => CaviarLang::Add,
        "Mul" => CaviarLang::Mul,
        "Min" => CaviarLang::Min,
        "Max" => CaviarLang::Max,
        "Div" => CaviarLang::Div,
        "Sub" => CaviarLang::Sub,
        "Lt" => CaviarLang::Lt,
        "IEq" => CaviarLang::IEq,
        "Or" => CaviarLang::Or,
        "And" => CaviarLang::And,
        "Let" => CaviarLang::Let,
        "Eq" => CaviarLang::Eq,
        "Mod" => CaviarLang::Mod,
        op => panic!("{op}"),
    };
    let first = node[i1+1..i2].trim().parse::<usize>().unwrap();
    let second = node[i2+1..i3].trim().parse::<usize>().unwrap();
    op([(Offset(0), Id(first)), (Offset(0), Id(second))])
}

pub fn load(s: &str) -> EGraph<CaviarAnalysis> {
    let mut eg = EGraph::new();

    let s = std::fs::read_to_string(s).unwrap();

    for line in s.split("\n") {
        if line.is_empty() { continue }
        let first = line.split(":").next().unwrap();
        let class = first.trim().parse::<usize>().unwrap();
        while eg.uf.next_id().0 < class {
            eg.uf.makeset(None);
        }
    }
    let mut og_nodecount = 0;

    for line in s.split("\n") {
        if line.is_empty() { continue }
        let first = line.split(":").next().unwrap();
        let class = first.trim().parse::<usize>().unwrap();
        let class = (Offset(0), Id(class));

        let nodes_str = &line[first.len()+1..];
        for node in split_nodes(nodes_str) {
            og_nodecount += 1;
            let j = eg.add(&node);
            eg.union(class, j);
        }
    }
    dbg!(og_nodecount);

    eg.rebuild();
    eg
}

#[test]
fn load_caviar() {
    let eg = load("caviar-egraph-dump");
    dbg!(eg.hashcons.len());
}
