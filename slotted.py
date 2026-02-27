from uf import *

type Slot = int

@dataclass(frozen=True)
class Renaming:
    m: tuple[(Slot, Slot)]

    def mk(it) -> Renaming:
        l = sorted(list(it), key=lambda x: x[0])
        return Renaming(tuple(l))

    def __mul__(self, other: Renaming) -> Renaming:
        if not isinstance(other, Renaming):
            return NotImplemented

        m = []
        for (s1, s2) in self.m:
            if s2 in other.m:
                s3 = other.m[s2]
                m.append((s1, s3))
        return Renaming.mk(m)

    def inverse(self) -> Renaming:
        Renaming.mk([(v, k) for (k, v) in self.m])

class SlottedUF(SemiUF):
    def __init__(self):
        super(self).__init__()

    def alloc_slotted(self, identity: Renaming):
        x = self.alloc()

    def handle_self_edge(self, other):
        pass
