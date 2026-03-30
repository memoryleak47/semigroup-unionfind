from dataclasses import dataclass

type Id = int
type Slot = int
SLOT_COUNT = 5 # We only support slots in range 0-4 to keep things computable

class GroupUF:
    def __init__(self):
        self.leader = {} # Id -> (G, Id)
        self.self_edges = {} # Id -> set[G]

    def alloc(self) -> Id:
        i = len(self.leader)
        self.leader[i] = None
        self.self_edges[i] = {identity}
        return i

    def offset(self, g: G, x: Id):
        y = self.alloc()
        self.leader[y] = (g, x)
        return y

    # assumes i is a leader
    def add_self_edge(self, i: Id, g: G):
        if not g in self.self_edges[i]:
            self.self_edges[i].add(g)

        # complete self-edges
        s = self.self_edges[i].copy()
        while True:
            s2 = s.copy()
            for x in s:
                for y in s:
                    s2.add(x.compose(y))
            if len(s) == len(s2): break
            s = s2
        self.self_edges[i] = s

    def union(self, x: Id, y: Id):
        g2, x2 = self.find(x)
        h2, y2 = self.find(y)
        # g2*x2 = h2*y2
        # h2⁻¹*g2*x2 = y2
        res_g = h2.inverse().compose(g2)

        if x2 == y2:
            self.add_self_edge(x2, res_g)
        else:
            self.leader[y2] = (res_g, x2)
            for g in self.self_edges[y2]:
                # y2 = g*y2
                # res_g*x2 = g*res_g*x2
                # x2 = res_g⁻¹*g*res_g*x2
                new_g = res_g.inverse().compose(g).compose(res_g)
                self.add_self_edge(x2, new_g)
            self.self_edges[y2] = None

    def find(self, x: Id) -> (G, Id):
        g = identity
        while self.leader[x] is not None:
            g2, y = self.leader[x]
            g, x = g.compose(g2), y
        return g, x

    def dump(self):
        print("---------------")
        print("LEADERS:")
        for x, y in suf.leader.items():
            if y is not None:
                print(f"id{x} -> ({y[0].data}, id{y[1]})")
        print()
        print("SELF-EDGES:")
        for x, y in suf.self_edges.items():
            if y is None: continue
            print(f"id{x} self-edges:")
            for a in y:
                print(f"  {a.data}")
            print()
        print("---------------")
        
@dataclass(frozen=True)
class Renaming:
    data: tuple[Slot] # always has length SLOT_COUNT

    def __post_init__(self):
        assert(type(self.data) == tuple)
        assert(len(self.data) == SLOT_COUNT)
        assert(len(set(self.data)) == SLOT_COUNT)
        for x in self.data:
            assert(x < SLOT_COUNT)

    def __getitem__(self, x: Slot) -> Slot:
        return self.data[x]

    def inverse(self) -> Renaming:
        l = list(range(SLOT_COUNT))
        for x, y in enumerate(self.data):
            l[y] = x
        return Renaming(tuple(l))

    # returns `self*other`
    def compose(self, other: Renaming) -> Renaming:
        l = []
        for y in other.data:
            l.append(self[y])
        return Renaming(tuple(l))

suf = GroupUF()

def alloc_with_slots(slots: set[Slot]) -> Id:
    x = suf.alloc()
    other_slots = list(set(range(SLOT_COUNT)) - slots)
    if len(other_slots) >= 2:
        flip = list(range(SLOT_COUNT))
        flip[other_slots[0]] = other_slots[1]
        flip[other_slots[1]] = other_slots[0]
        flip = Renaming(tuple(flip))
        suf.add_self_edge(x, flip)

        shift = list(range(SLOT_COUNT))
        for i, s in enumerate(other_slots):
            j = (i + 1) % len(other_slots)
            shift[s] = other_slots[j]
        shift = Renaming(tuple(shift))
        suf.add_self_edge(x, shift)
    return x

# Group identity element
identity = Renaming(tuple(range(SLOT_COUNT)))

# problem case:

a = alloc_with_slots({0, 1, 2})
b = alloc_with_slots({2, 3})

suf.dump()
suf.union(a, b)
suf.dump()
