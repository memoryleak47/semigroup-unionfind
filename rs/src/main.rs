trait Grp: Copy + Eq {
    fn inverse(self) -> Self;
    fn compose(_: Self, _: Self) -> Self;
}

trait Lat<G: Grp>: Copy + Eq {
    fn act(_: G, _: Self) -> Self;
    fn mk(_: G) -> Self;
    fn join(_: Self, _: Self) -> Self;
}

type Id = usize;

struct Class<G: Grp, L: Lat<G>> {
    lat: Option<L>,

    // self = gid * leader
    gid: (Option<G>, Id),
}

struct GUF<G: Grp, L: Lat<G>> {
    classes: Vec<Class<G, L>>,
}

impl<G: Grp, L: Lat<G>> GUF<G, L> {
    fn new() -> Self {
        GUF { classes: Vec::new() }
    }

    fn alloc(&mut self) -> Id {
        let new_id = self.classes.len();
        self.classes.push(Class {
            lat: None,
            gid: (None, new_id),
        });
        new_id
    }

    fn union(&mut self, a1: Id, a2: Id) {
        let (g1, x1) = self.find(a1);
        let (g2, x2) = self.find(a2);

        // g1 * x1 = g2 * x2
        // x1 = g1⁻¹ * g2 * x2
        //      \_______/
        //          g
        let g = opt_compose(opt_inverse(g1), g2);

        //
        // x1 = g * x2
        //

        if x1 != x2 {
            let l1 = self.classes[x1].lat;
            self.classes[x1] = Class {
                lat: None,
                gid: (g, x2),
            };

            let l2 = self.classes[x2].lat;

            let l2 = opt_join(l2, opt_act(g, l1));

            self.classes[x2].lat = l2;
        } else {
            let l = self.classes[x1].lat;
            self.classes[x1].lat = opt_join(l, opt_mk(g));
        }
    }

    fn offset(&mut self, (g, id): (G, Id)) -> Id {
        let (g, id) = self.find_gid((Some(g), id));

        // new_id = g * id
        // -> id = g⁻¹ * new_id
        // -> id = g⁻¹ * g * id

        // offseting from `id` creates a new self-edge for `id`.
        let gig = opt_compose(opt_inverse(g), g);
        let l = self.classes[id].lat;
        let l = opt_join(l, opt_mk(gig));
        self.classes[id].lat = l;

        let new_id = self.classes.len();
        self.classes.push(Class {
            lat: None,
            gid: (g, id),
        });
        new_id
    }

    fn get_lattice(&self, x: Id) -> Option<L> {
        let (g, id) = self.find(x);
        opt_act(g, self.classes[id].lat)
    }

    // private implementation detail.
    fn find(&self, id: Id) -> (Option<G>, Id) {
        self.find_gid(self.classes[id].gid)
    }

    // private implementation detail.
    fn find_gid(&self, (mut g, mut id): (Option<G>, Id)) -> (Option<G>, Id) {
        loop {
            let (g2, id2) = self.classes[id].gid;
            if id == id2 { return (g, id); }
            (g, id) = (opt_compose(g, g2), id2);
        }
    }
}

fn opt_inverse<G: Grp>(g: Option<G>) -> Option<G> {
    g.map(G::inverse)
}

fn opt_compose<G: Grp>(g1: Option<G>, g2: Option<G>) -> Option<G> {
    Some(G::compose(g1?, g2?))
}

fn opt_join<G: Grp, L: Lat<G>>(l1: Option<L>, l2: Option<L>) -> Option<L> {
    Some(L::join(l1?, l2?))
}

fn opt_mk<G: Grp, L: Lat<G>>(g: Option<G>) -> Option<L> {
    Some(L::mk(g?))
}

fn opt_act<G: Grp, L: Lat<G>>(g: Option<G>, l: Option<L>) -> Option<L> {
    Some(L::act(g?, l?))
}

fn main() {}


