from uf import *

type Slot = int

@dataclass(frozen=True)
class Renaming:
    m: tuple[(Slot, Slot)]

    def __post_init__(self):
        assert(isinstance(self.m, tuple))
        for k, v in self.m:
            assert(isinstance(k, int))
            assert(isinstance(v, int))
        assert(tuple(sorted(self.m, key=lambda x: x[0])) == self.m)

    def mk(it) -> Renaming:
        l = sorted(list(it), key=lambda x: x[0])
        return Renaming(tuple(l))

    def get(self, s: Slot) -> Slot|Option:
        for (k, v) in self.m:
            if k == s:
                return v

    def compose(self, other: Renaming) -> Renaming:
        m = []
        for (s1, s2) in other.m:
            s3 = self.get(s2)
            if s3 is not None:
                m.append((s1, s3))
        return Renaming.mk(m)

    def inverse(self) -> Renaming:
        return Renaming.mk([(v, k) for (k, v) in self.m])

    def __repr__(self):
        return "[" + ", ".join(f"{k}->{v}" for (k, v) in self.m) + "]"

# Lattice
class SlottedLattice:
    def __init__(self, slots: set(Slot)):
        self.identity = Renaming.mk((x, x) for x in slots)
        self.group = {self.identity}

    def add(self, g: Renaming):
        self.identity = self.identity.compose(g.compose(g.inverse()))
        self.group = set(self.identity.compose(perm) for perm in self.group)

        while True:
            n = len(self.group)
            for g1 in list(self.group):
                for g2 in list(self.group):
                    self.group.add(g1.compose(g2))
            if len(self.group) == n: break

    def contains(self, x: G):
        x = self.identity.compose(x)
        return x in self.group

suf = SemiUF()
a = suf.alloc(SlottedLattice({0, 1}))
b = suf.alloc(SlottedLattice({2, 3}))

aa = GId(Renaming.mk([(0, 10), (1, 11)]), a)
bb = GId(Renaming.mk([(3, 10), (2, 11)]), b)

suf.union(aa, bb)
assert(suf.is_equal(aa, bb))
