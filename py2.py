# This is pseudocode.

type Id = int

# semigroup
trait G:
    def compose(G, G) -> G
    def inverse(G) -> G

    # You can extend anything to get a neutral element, if you don't already have one.
    def neutral() -> G

# Lattice
trait L:
    def mk(G) -> L

    def join(L, L) -> L
    def move(L, G) -> L

class GUF:
    def __init__(self):
        self.uf = {} # Id -> (G, Id)
        self.lattices = {} # Id -> L

    def alloc(self) -> (G, Id):
        i = len(self.uf)
        g = G.neutral()
        self.uf[i] = (g, i)
        self.lattices[i] = L.mk(g)
        return (g, i)

    def find(self, gid: (G, Id)):
        g, x = gid
        while True:
            g2, x2 = self.uf[x]
            if x == x2: return g, x
            # x = g2*x2
            # we need to return g*x, thus g*g2*x2
            g, x = G.compose(g, g2), x2

    def union(self, gid1: (G, Id), gid2: (G, Id)):
        g1, x1 = self.find(gid1)
        g2, x2 = self.find(gid2)

        # x1 = g1⁻¹ * g2 * x2
        #      \_______/
        #          g

        g = G.compose(g1.inverse(), g2)
        if x1 == x2:
            self.lattice[x1] = self.lattice[x1].join(L.mk(g))
        else:
            self.uf[x1] = (g, x2)

            # add other lattice
            self.lattice[x2] = self.lattice[x2].join(self.lattice[x1].move(g))

            # x1 = g * x2
            # -> x2 = g⁻¹ * x1
            # -> x2 = g⁻¹ * g * x2

            # add new self-edge
            self.lattice[x2] = self.lattice[x2].join(L.mk(G.compose(g.inverse(), g)))

    def get_lattice(self, gid: (G, Id)) -> L:
        g, x = self.find(gid)
        return self.lattices[x].move(g)
