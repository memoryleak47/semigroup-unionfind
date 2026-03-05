from dataclasses import dataclass
from typing import Protocol

# We typically write G for an element from an SemigroupWithInvolution.
class SemigroupWithInvolution(Protocol):
    # g1 * g2 * i = compose(g1, g2) * i
    # Thus the *right* argument is evaluated first.
    def compose(self, other: Self) -> Self: pass
    def inverse(self) -> Self: pass

# This "set"-like lattice is a collection of G elements.
# It represents all the self-edges that we have.
class Lattice(Protocol):
    def add(self, new_fact: G): pass
    def contains(self, fact: G) -> bool: pass
    def join(self, other: Self) -> Self: pass # TODO we'll need to use this when merging two classes.
    def move(self, g: G) -> Self: pass

@dataclass(frozen=True)
class Id:
    i: int

    def __repr__(self):
        return f"id{self.i}"

@dataclass(frozen=True)
class GId:
    g: G
    id: Id

    def __repr__(self):
        return f"[{self.g}]{self.id}"

# This is generic over a Lattice L and a SemigroupWithInvolution G.
class SemiUF:
    def __init__(self):
        # invariant: uf[i] = None XOR lattice[i] = None.
        # leaders have a lattice, but no uf. Followers have uf, but no lattice.

        self.uf = {} # dict[Id, (G, Id)]
        self.lattice = {} # dict[Id, L]

    def alloc(self, lat: L) -> Id:
        i = Id(len(self.uf))
        self.uf[i] = None
        self.lattice[i] = lat
        return i

    def find(self, gid: GId) -> GId:
        while (a := self.uf[gid.id]) is not None:
            gid = GId(gid.g.compose(a.g), a.id)
        return gid

    def union(self, x: GId, y: GId):
        x = self.find(x)
        y = self.find(y)

        # x.g * x.id = y.g * y.id
        # x.id = x.g⁻¹ * y.g * y.id
        i = x.id
        y = GId(x.g.inverse().compose(y.g), y.id)

        if i == y.id:
            self.lattice[i].add(y.g)
        else:
            self.uf[i] = y
            self.lattice[y.id] = self.lattice[y.id].join(self.lattice[i].move(y.g))
            self.lattice[i] = None # no need to store this lattice anymore.

    def is_equal(self, x: GId, y: GId) -> bool:
        x = self.find(x)
        y = self.find(y)
        if x.id != y.id: return False

        i = x.id
        yg = x.g.inverse().compose(y.g)
        return self.lattice[i].contains(yg)
