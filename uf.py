from dataclasses import dataclass
from typing import Protocol

class SemigroupWithInvolution(Protocol):
    def __mul__(self, other: Self) -> Self: pass
    def inverse(self) -> Self: pass

@dataclass(frozen=True)
class Id:
    i: int

    def __rmul__(self, g: G):
        return GId(g2, self)

# equivalent to `g * id`
@dataclass(frozen=True)
class GId:
    g: G
    id: Id

    def __rmul__(self, g2: G):
        return GId(g2 * self.g, self.id)

# This is generic over the SemigroupWithInvolution G
class SemiUF:
    def __init__(self):
        self.uf = {} # dict[Id, (G, Id)]
        self.local_data = {} # dict[Id, ?]

    def alloc(self) -> Id:
        i = Id(len(self.uf))
        self.uf[i] = None
        return i

    def find(self, gid: GId) -> GId:
        while self.uf[gid.id] is not None:
            gid = gid.g + self.uf[gid.id]
        return gid

    def handle_self_edge(self, i: Id, g: G):
        pass

    def union(self, x: GId, y: GId):
        x = self.find(x)
        y = self.find(y)

        i = x.id
        y = -x.g + y

        if i == y.id:
            self.handle_self_edge(i, y.g)
        else:
            self.uf[i] = y
