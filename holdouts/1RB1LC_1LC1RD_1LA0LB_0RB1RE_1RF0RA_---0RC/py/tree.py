"""tree.py: collapse a fitted frame map into a decision tree of Lean-style patterns (each var: exact k or >= s)."""
from fractions import Fraction
import itertools
from functools import lru_cache

class Tree:
    def __init__(s, fit):
        s.f = fit; s.T = fit.T
        assert fit.MOD == 1
    def pats_in(s, n, region):
        opts = []
        for kind, v in region:
            if kind == 'eq': opts.append([v])
            else: opts.append(list(range(v, s.T)) + [('big', 0)])
        return list(itertools.product(*opts))
    def general(s, region):
        return tuple(v if kind == 'eq' else ('big', 0) for kind, v in region)
    @staticmethod
    def restrict(fml, pat):
        """affine formula (c0, {i: c}) with the vars fixed in pat substituted."""
        c0, co = fml; c0 = Fraction(c0); co2 = {}
        for i, c in co.items():
            if isinstance(pat[i], tuple): co2[i] = Fraction(c)
            else: c0 += c * pat[i]
        return (c0, {i: c for i, c in co2.items() if c})
    @staticmethod
    def norm(fml):
        c0, co = fml; return (Fraction(c0), {i: Fraction(c) for i, c in co.items() if c})
    def uniform(s, n, region):
        g = s.f.cases.get((n, s.general(region)))
        if g is None: return None
        for p in s.pats_in(n, region):
            c = s.f.cases.get((n, p))
            if c is None or c[0] != g[0]: return None
            for a, b in zip(list(c[1]) + [c[2]], list(g[1]) + [g[2]]):
                if s.norm(a) != s.restrict(b, p): return None
        return g
    def build(s, n, region):
        g = s.uniform(n, region)
        if g is not None: return [(region, g)]
        best = None
        for i, (kind, v) in enumerate(region):
            if kind != 'ge' or v >= s.T: continue
            r1 = list(region); r1[i] = ('eq', v); r2 = list(region); r2[i] = ('ge', v + 1)
            leaves = s.build(n, tuple(r1)) + s.build(n, tuple(r2))
            if best is None or len(leaves) < len(best): best = leaves
        assert best is not None, (n, region)
        return best
    def all(s):
        out = {}
        for n in s.f.F.frames:
            k = len(s.f.vars_of(n)); out[n] = s.build(n, tuple([('ge', 0)] * k))
        return out
