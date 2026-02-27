from uf import *
from dataclasses import dataclass

# <a, b> := \x. a + b*x
@dataclass(frozen=True)
class ArithG:
    a: float
    b: float

    def compose(self, r: ArithG) -> ArithG:
        sa, sb = self.a, self.b
        ra, rb = r.a, r.b
        # <sa, sb> ° <ra, rb> (x)
        # = <sa, sb> ° (ra + rb*x)
        # = sa + sb*(ra + rb*x)
        # = <sa+sb*ra, rb*sb>
        return ArithG(sa+sb*ra, rb*sb)

    def inverse(self) -> ArithG:
        sa, sb = self.a, self.b
        assert(sb != 0.0)
        # Goal: <sa, sb> ° <ra, rb> = \x. x
        # <-> <sa+sb*ra, rb*sb> = <0, 1>
        # sa+sb*ra = 0
        # rb*sb = 1
        rb = 1.0/sb
        ra = -sa/sb
        return ArithG(ra, rb)

    def __repr__(self):
        return f"<{self.a}, {self.b}>"

class ArithL:
    def __init__(self):
        self.elem = None

    def add(self, g: ArithG):
        a, b = g.a, g.b

        if b == 1.0:
            assert(a == 0.0)
            return

        # x = a + b*x
        # 0 = a + b*x - x
        # 0 = a + (b-1)*x
        # -a/(b-1) = x
        # a/(1-b) = x
        solution = a / (1.0 - b)
        if self.elem is None:
            self.elem = solution
        else:
            assert(self.elem == solution)

    def contains(self, g: ArithG):
        if self.elem is not None:
            return self.elem == g.a + self.elem * g.b

        return g == ArithG(0.0, 1.0)

suf = SemiUF()
a = suf.alloc(ArithL())
b = suf.alloc(ArithL())
suf.union(GId(ArithG(3, 1), a), GId(ArithG(0, 1), b))
suf.union(GId(ArithG(0, 2), a), GId(ArithG(0, 1), b))
