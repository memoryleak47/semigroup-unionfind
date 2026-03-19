from typing import Self

type Id = int

# abstract class
class InverseSemigroup:
    def compose(self, other: Self) -> Self: ...
    def inverse(self) -> Self: ...

    # computes whether `x=self*x` is implied by `x=g*x, forall g in s`
    def in_closure(self, s: set[Self]) -> bool: ...

class GUF[G: InverseSemigroup]: # We are generic over some InverseSemigroup G
    def __init__(self):
        self.uf = {} # Id -> (option G, Id)
        self.self_edges = {} # Id -> set[G]

    def alloc(self) -> Id:
        i = len(self.uf)
        self.uf[i] = (None, i)
        self.self_edges[i] = set()
        return i

    def union(self, id1: Id, id2: Id):
        g1, x1 = self.find(id1)
        g2, x2 = self.find(id2)

        # x1 = g1⁻¹ * g2 * x2
        #      \_______/
        #          g

        g = opt_compose(opt_inverse(g1), g2)
        if x1 == x2:
            add_selfedge(self.self_edges[x1], g)
        else:
            self.uf[x1] = (g, x2)
            # x1 = g*x2

            for e in self.self_edges[x1]:
                # e*x1 = x1
                # -> e*g*x2 = g*x2
                # -> g*⁻¹*e*g*x2 = x2
                e = opt_compose(opt_inverse(g), opt_compose(e, g))
                add_selfedge(self.self_edges[x2], e)

            # We don't need these self edges anymore. Just use the self edges of x2 instead.
            del self.self_edges[x1]

    def offset(self, g: G, i: Id) -> Id:
        g2, i2 = self.find(i)
        g, i = opt_compose(g, g2), i2

        new = len(self.uf)
        self.uf[new] = (g, i)
        # new = g*i
        # -> g⁻¹*new = i
        # -> g⁻¹*g*i = i
        e = opt_compose(opt_inverse(g), g)
        add_selfedge(self.self_edges[i], e)
        return new

    def is_equal(self, i1: Id, i2: Id) -> bool:
        g1, i1 = self.find(i1)
        g2, i2 = self.find(i2)
        if i1 != i2: return False
        i = i1
        # g1*i = g2*i
        # -> i = g1⁻¹*g2*i
        g = opt_compose(opt_inverse(g1), g2)
        return opt_in_closure(g, self.self_edges[i])

    # implementation detail
    def find(self, x: Id) -> (G|None, Id):
        g, x = None, x
        while True:
            g2, x2 = self.uf[x]
            if x == x2: return g, x
            # x = g2*x2
            # we need to return g*x, thus g*g2*x2
            g, x = opt_compose(g, g2), x2


def opt_compose(x: G|None, y: G|None) -> G|None: 
    if x is None: return None
    if y is None: return None
    x.compose(y)

def opt_inverse(x: G|None) -> G|None: 
    if x is None: return None
    x.inverse()

def opt_in_closure(x: G|None, s: set[G]) -> bool:
    if x is None: return True
    x.in_closure(s)

def add_selfedge(x: G|None, s: set[G]):
    if opt_in_closure(x, s): return
    assert(x is not None)
    s.add(x)
