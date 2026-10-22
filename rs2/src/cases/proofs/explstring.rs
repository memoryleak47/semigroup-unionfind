use super::*;

type EGraph = crate::EGraph<ProofAnalysis>;
type Pattern = crate::Pattern<ProofAnalysis>;
type Term = crate::Term<ProofAnalysis>;

pub fn explstring(eg: &EGraph, lhs: &Term, rhs: &Term, p: &Proof, rules: &Rules) -> String {
    let lhs_id = eg.lookup_term(lhs).unwrap();
    let rhs_id = eg.lookup_term(rhs).unwrap();

    let proof = eg.get_g_between(lhs_id, rhs_id).unwrap();

    let mut mvar_counter = 0;
    let mut umap = UnifyMap::default();

    let mut e = eval(proof, &mut mvar_counter, &mut umap, rules);

    unify(e.first(), &lhs, &mut umap);
    unify(&e.last, &rhs, &mut umap);

    for t in e.all_terms() {
        *t = umap_canon(t, &umap);
    }

    for t in e.all_terms() {
        default_instantiate(t);
    }

    stringify(&e)
}

struct Expl {
    vec: Vec<(Pattern, ExplStep)>,
    last: Pattern,
}

impl Expl {
    pub fn first(&self) -> &Pattern {
        self.vec.first().map(|(x, _)| x).unwrap_or_else(|| &self.last)
    }

    pub fn all_terms(&mut self) -> impl Iterator<Item=&mut Pattern> {
        self.vec.iter_mut().map(|(x, _)| x).chain(std::iter::once(&mut self.last))
    }
}

#[derive(Clone)]
struct ExplStep {
    rule: Symbol,
    forward: bool,
    pos: Vec<usize>,
}

type UnifyMap = HashMap<Symbol, Pattern>;

fn umap_canon(t: &Pattern, umap: &UnifyMap) -> Pattern {
    match t {
        Pattern::PVar(p) => match umap.get(p) {
            Some(t) => umap_canon(t, umap),
            None => Pattern::PVar(*p),
        }
        Pattern::Node(n, children) => {
            Pattern::Node(n.clone(),
                children.iter().map(|x| umap_canon(x, umap)).collect()
            )
        },
        Pattern::G(..) => unreachable!(),
    }
}

fn contains_var(p: &Pattern, v: Symbol) -> bool {
    match p {
        Pattern::PVar(v2) => v == *v2,
        Pattern::Node(_, children) => children.iter().any(|c| contains_var(c, v)),
        Pattern::G(..) => unreachable!(),
    }
}

// will panic if it can't unify.
fn unify(l: &Pattern, r: &Pattern, umap: &mut UnifyMap) {
    let l = umap_canon(l, umap);
    let r = umap_canon(r, umap);
    match (l, r) {
        (Pattern::PVar(p1), Pattern::PVar(p2)) if p1 == p2 => {},
        (Pattern::PVar(p), t)|(t, Pattern::PVar(p)) => {
            assert!(!contains_var(&t, p));

            umap.insert(p, t.clone());
            *umap = umap.iter().map(|(k, v)| (*k, umap_canon(v, umap))).collect();
        },
        (Pattern::Node(n1, cs1), Pattern::Node(n2, cs2)) => {
            assert_eq!(n1.f, n2.f);
            for (c1, c2) in cs1.iter().zip(cs2.iter()) {
                unify(c1, c2, umap);
            }
        },
        (Pattern::G(..),_)|(_,Pattern::G(..)) => unreachable!(),
    }
}

fn eval_trans(e2: Expl, e1: Expl, umap: &mut UnifyMap) -> Expl {
    let ll = umap_canon(&e1.last, umap);
    let rr = umap_canon(e2.first(), umap);

    unify(&ll, &rr, umap);

    Expl {
        vec: e1.vec.iter().cloned().chain(e2.vec.iter().cloned()).collect(),
        last: e2.last.clone(),
    }
}

fn eval(p: Proof, mvar_counter: &mut usize, umap: &mut UnifyMap, rules: &Rules) -> Expl {
    match raw_get(p) {
        ProofObj::Refl => Expl {
            vec: Vec::new(),
            last: Pattern::PVar(fresh_mvar(mvar_counter)),
        },
        ProofObj::Sym(p) => {
            let e = eval(p, mvar_counter, umap, rules);
            let n = e.vec.len();
            Expl {
                vec: (0..n).rev().map(|i| {
                    let node = if i == n-1 { &e.last } else { &e.vec[i+1].0 }.clone();
                    let mut edge = e.vec[i].1.clone();
                    edge.forward = !edge.forward;
                    (node, edge)
                }).collect(),
                last: e.first().clone(),
            }
        },
        ProofObj::Trans(p2, p1) => {
            let e1 = eval(p1, mvar_counter, umap, rules);
            let e2 = eval(p2, mvar_counter, umap, rules);
            eval_trans(e2, e1, umap)
        },
        ProofObj::Congr(si, children) => {
            let mut cs = Vec::new();
            for (i, c) in children.iter().enumerate() {
                let inner = eval(*c, mvar_counter, umap, rules);
                let wrapped = wrap(inner, mvar_counter, i, children.len(), si);
                cs.push(wrapped);
            }
            let mut total = cs.pop().unwrap();
            for x in cs.into_iter().rev() {
                total = eval_trans(x, total, umap);
            }
            total
        },
        ProofObj::Rule(rule_name) => {
            let (name, lhs, rhs) = rules.iter().find(|(n, _, _)| *n == rule_name).unwrap();
            let step = ExplStep { rule: *name, forward: true, pos: Vec::new() };

            let mut lhs = lhs.clone();
            let mut rhs = rhs.clone();

            let mut map = HashMap::new();
            refresh_mvars(&mut lhs, mvar_counter, &mut map);
            refresh_mvars(&mut rhs, mvar_counter, &mut map);

            Expl {
                vec: vec![(lhs, step)],
                last: rhs,
            }
        },
    }
}

fn wrap(mut e: Expl, mvar_counter: &mut usize, i: usize, arity: usize, si: Symbol) -> Expl {
    let l: Box<[Pattern]> = (0..arity).map(|_| Pattern::PVar(fresh_mvar(mvar_counter))).collect();
    for p in e.vec.iter_mut().map(|(_, step)| &mut step.pos) {
        p.push(i);
    }
    for t in e.all_terms() {
        let nil = (mk_refl(), Id(0));
        let node = ProofLang { f: si, args: vec![nil; arity].into() };
        let mut children = l.clone();
        children[i] = t.clone();
        *t = Term::Node(node, children);
    }
    e
}

fn fresh_mvar(mvar_counter: &mut usize) -> Symbol {
    let x = *mvar_counter;
    *mvar_counter += 1;
    Symbol::from(format!("fresh{x}"))
}

fn refresh_mvars(t: &mut Pattern, mvar_counter: &mut usize, map: &mut HashMap<Symbol, Symbol>) {
    match t {
        Pattern::PVar(v) => {
            let vv = if let Some(vv) = map.get(v) { *vv } else {
                let vv = fresh_mvar(mvar_counter);
                map.insert(*v, vv);
                vv
            };
            *t = Pattern::PVar(vv);
        },
        Pattern::Node(n, children) => {
            for c in children {
                refresh_mvars(c, mvar_counter, map);
            }
        },
        Pattern::G(..) => unreachable!(),
    }
}

fn default_instantiate(p: &mut Pattern) {
    match p {
        Pattern::PVar(v) => {
            let node = ProofLang { f: Symbol::new("top"), args: Box::new([]) };
            *p = Pattern::Node(node, Box::new([]));
        },
        Pattern::Node(_, children) => {
            for c in children {
                default_instantiate(c);
            }
        },
        Pattern::G(..) => unreachable!(),
    }
}

fn stringify(e: &Expl) -> String {
    let mut out = String::new();

    out.push_str(&stringify_term(e.first(), None));
    out.push('\n');

    for i in 0..e.vec.len() {
        let s = e.vec[i].1.clone();
        let t = if i == e.vec.len()-1 { &e.last } else { &e.vec[i+1].0 };
        out.push_str(&stringify_term(t, Some(s)));
        out.push('\n');
    }

    out
}

fn stringify_term(t: &Pattern, step: Option<ExplStep>) -> String {
    if let Some(step_) = &step {
        if step_.pos.is_empty() {
            let subterm = stringify_term(t, None);
            let dir = if step_.forward { "=>" } else { "<=" };
            let name = step_.rule;
            return format!("(Rewrite{dir} {name} {subterm})")
        }
    }

    match t {
        Pattern::Node(n, children) => {
            let op = n.f;
            let child_strings: Vec<String> = children.iter().enumerate().map(|(j, x)| {
                if let Some(step_) = &step {
                    if Some(j) == step_.pos.last().copied() {
                        let mut step2 = step_.clone();
                        step2.pos.pop();
                        return stringify_term(x, Some(step2))
                    }
                }
                return stringify_term(x, None)
            }).collect();

            if child_strings.is_empty() {
                op.to_string()
            } else {
                format!("({} {})", op, child_strings.join(" "))
            }
        },
        Pattern::PVar(v) => format!("?{v}"),
        Pattern::G(..) => unreachable!(),
    }
}
