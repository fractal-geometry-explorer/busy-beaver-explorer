"""Exact numbers  sum_i c_i 2^(e_i)  with rational c_i and (huge) integer exponents e_i."""
from fractions import Fraction
import math


class Sym:
    __slots__ = ('t',)

    def __init__(self, t=None):
        self.t = {}
        for e, c in (t or {}).items():
            if c:
                self.t[e] = Fraction(c)
        self.norm()

    def norm(self):
        # move powers of two out of the coefficients, merge equal exponents
        t2 = {}
        for e, c in self.t.items():
            if c == 0:
                continue
            num, den = c.numerator, c.denominator
            while num % 2 == 0:
                num //= 2; e += 1
            while den % 2 == 0:
                den //= 2; e -= 1
            t2[e] = t2.get(e, 0) + Fraction(num, den)
        self.t = {e: c for e, c in t2.items() if c}
        if any(self.t.get(e) and self.t[e].numerator % 2 == 0 for e in self.t):
            self.norm()

    @staticmethod
    def of(x):
        return x if isinstance(x, Sym) else Sym({0: x})

    @staticmethod
    def pow2(e, c=1):
        return Sym({e: c})

    def __add__(self, o):
        o = Sym.of(o); t = dict(self.t)
        for e, c in o.t.items():
            t[e] = t.get(e, 0) + c
        return Sym(t)
    __radd__ = __add__

    def __neg__(self):
        return Sym({e: -c for e, c in self.t.items()})

    def __sub__(self, o):
        return self + (-Sym.of(o))

    def __rsub__(self, o):
        return Sym.of(o) - self

    def __mul__(self, o):
        if isinstance(o, Sym):
            t = {}
            for e1, c1 in self.t.items():
                for e2, c2 in o.t.items():
                    t[e1 + e2] = t.get(e1 + e2, 0) + c1 * c2
            return Sym(t)
        return Sym({e: c * o for e, c in self.t.items()})
    __rmul__ = __mul__

    def concrete(self, maxbits=10 ** 7):
        if all(e <= maxbits for e in self.t):
            v = sum((c * (Fraction(2) ** e) for e, c in self.t.items()), Fraction(0))
            assert v.denominator == 1, v
            return v.numerator
        return None

    def lead(self):
        e = max(self.t); return e, self.t[e]

    def log10(self):
        e, c = self.lead()
        return e * math.log10(2) + math.log10(abs(c))

    def __repr__(self):
        terms = sorted(self.t.items(), reverse=True)
        def ex(e):
            s = str(e); return s if len(s) < 30 else s[:12] + '..(%dd)' % len(s)
        return ' + '.join('%s*2^%s' % (c, ex(e)) for e, c in terms)


def as_num(x):
    """an int if it is small enough, else the Sym"""
    if isinstance(x, Sym):
        v = x.concrete()
        return v if v is not None else x
    return x
