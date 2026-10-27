"""Integer-arithmetic version of the exact 2-adic route tree (routetree.py / ewroutes.py): positions are affine forms
in (m, E) with integer numerators over a fixed 2^D, concrete values are integers scaled by 2^D, the coset of (m, E)
is kept with integer data.  Same rules and branching as conc.Model + tree4.TModel; output is checked against
routetree.py at small cuts.
usage: fasttree.py cut_bits [part nparts]   -> ../fasttree_routes{cut}[_part].jsonl (G W W W prefixes) and
                                               ../fasttree_ew{cut}[_part].jsonl (G W W W W prefixes)"""
import sys, json, collections
from fractions import Fraction as F

import os
D = int(os.environ.get("FT_D", "400")); SC = 1 << D
PREC = [0]

class P:
    __slots__ = ('f', 'v')
    def __init__(self, f, v): self.f = f; self.v = v
    def add(self, c):        # c an integer number of cells
        return P((self.f[0], self.f[1], self.f[2] + c * SC), self.v + c * SC)
    def plus(self, o): return P((self.f[0] + o.f[0], self.f[1] + o.f[1], self.f[2] + o.f[2]), self.v + o.v)
    def minus(self, o): return P((self.f[0] - o.f[0], self.f[1] - o.f[1], self.f[2] - o.f[2]), self.v - o.v)
    def half(self):
        f = self.f
        if f[0] & 1 or f[1] & 1 or f[2] & 1 or self.v & 1:
            PREC[0] += 1; raise AssertionError("precision")
        return P((f[0] >> 1, f[1] >> 1, f[2] >> 1), self.v >> 1)

def const(c): return P((0, 0, c * SC), c * SC)

class Branch(Exception): pass

class Coset:
    """(m, E) = x0 + B y, y in Z^2 (columns of B), bits = log2 of the index."""
    __slots__ = ('x0', 'B', 'bits')
    def __init__(self, x0, B, bits=0): self.x0 = list(x0); self.B = [r[:] for r in B]; self.bits = bits
    def copy(self): return Coset(self.x0, self.B, self.bits)
    def evalf(self, f):
        a0 = f[2] + f[0] * self.x0[0] + f[1] * self.x0[1]
        g0 = f[0] * self.B[0][0] + f[1] * self.B[1][0]
        g1 = f[0] * self.B[0][1] + f[1] * self.B[1][1]
        assert a0 % SC == 0 and g0 % SC == 0 and g1 % SC == 0, "non-integral form on coset"
        return a0 // SC, (g0 // SC, g1 // SC)
    def decided(self, f):
        f0, g = self.evalf(f)
        if all((x >> 1) & 1 == 0 for x in g): return f0 % 4
        return None
    def impose(self, f, res):
        f0, g = self.evalf(f)
        assert f0 % 2 == 0 and all(x % 2 == 0 for x in g), "odd distance on coset"
        h = [x // 2 for x in g]; t = ((res - f0) // 2) % 2
        odd = [k for k in range(2) if h[k] % 2]
        if not odd: return (f0 // 2) % 2 == res // 2
        i = odd[0]
        for r in range(2): self.x0[r] += t * self.B[r][i]
        for k in range(2):
            if k != i:
                for r in range(2): self.B[r][k] -= h[k] * self.B[r][i]
        for r in range(2): self.B[r][i] *= 2
        self.bits += 1
        return True

class M:
    __slots__ = ('T', 'Ps', 'A', 'W', 'halted', 'bad', 'outcomes', 'coset', 'forced', 'fi', 'rd')
    def clone(self):
        n = M.__new__(M)
        n.T = self.T[:]; n.Ps = self.Ps[:]; n.A = self.A[:]; n.W = self.W; n.halted = self.halted; n.bad = self.bad
        n.outcomes = self.outcomes[:]; n.coset = None; n.forced = None; n.fi = 0; n.rd = self.rd
        return n
    def add(self, t, p):
        for i in range(len(self.T)):
            if not self.A[i]: self.T[i] = t; self.Ps[i] = p; self.A[i] = True; return i
        self.T.append(t); self.Ps.append(p); self.A.append(True); return len(self.T) - 1
    def first_right(self, x):
        b = -1; bv = None
        for i in range(len(self.T)):
            if self.A[i]:
                v = self.Ps[i].v
                if v > x.v and (b < 0 or v < bv): b = i; bv = v
        return b
    def last_mark(self):
        b = -1; bv = None
        for i in range(len(self.T)):
            if self.A[i]:
                v = self.Ps[i].v
                if b < 0 or v > bv: b = i; bv = v
        return b
    def packet_back(self, x):
        b = -1; bv = None
        for i in range(len(self.T)):
            if self.A[i] and self.T[i] != 'M':
                v = self.Ps[i].v
                if v < x.v and (b < 0 or v > bv): b = i; bv = v
        if b < 0: return -1
        if self.T[b] == 'B': self.halted = True; return -1
        if self.T[b] == 'G': self.Ps[b] = self.Ps[b].add(2); return b
        q = self.Ps[b]; self.T[b] = 'M'; self.Ps[b] = q.add(-1); return self.add('G', q.add(1))
    def shift_from(self, x):
        k = self.first_right(x)
        if k < 0:
            self.W = self.W.add(2); self.add('M', self.W.add(-2)); return self.packet_back(self.W.add(-2))
        t = self.T[k]
        if t == 'M': self.T[k] = 'G'; return k
        if t == 'W': self.T[k] = 'B'; return self.packet_back(self.Ps[k])
        if t == 'B': self.T[k] = 'W'; self.Ps[k] = self.Ps[k].add(2); return self.packet_back(self.Ps[k])
        self.bad = 2; return -1
    def test_outcome(self, d):
        dec = self.coset.decided(d.f)
        if dec is not None: return dec
        if self.fi < len(self.forced):
            res = self.forced[self.fi]; self.fi += 1
            self.coset.impose(d.f, res); return res
        raise Branch()
    def do_round(self):
        self.rd += 1
        gap = -1
        for i in range(len(self.T)):
            if self.A[i] and self.T[i] == 'G' and self.Ps[i].v == SC: gap = i
        while gap >= 0 and not self.halted and not self.bad:
            g = self.Ps[gap]; m = self.first_right(g)
            if m < 0:
                self.A[gap] = False; self.W = self.W.add(3); self.add('M', self.W.add(-2))
                gap = self.packet_back(self.W.add(-2)); continue
            t = self.T[m]
            if t == 'M':
                d = self.Ps[m].minus(g).add(-3)
                if d.v < 0: self.bad = 3; return
                res = self.test_outcome(d)
                self.outcomes.append(res)
                if res == 0:
                    h = d.half(); self.Ps[m] = g.plus(h).add(-1); self.Ps[gap] = g.plus(h).add(1)
                else:
                    self.A[gap] = False; self.T[m] = 'W'; self.Ps[m] = g.plus(d.half()).add(3)
                    gap = self.packet_back(self.Ps[m])
            elif t == 'W':
                x = self.Ps[m]; self.A[gap] = False; self.A[m] = False; gap = self.shift_from(x)
            elif t == 'B':
                self.T[m] = 'W'; self.Ps[m] = self.Ps[m].add(-1); gap = self.shift_from(self.Ps[m])
            else: self.bad = 4; return
        extra = 2
        for i in range(len(self.T)):
            if self.A[i] and self.T[i] == 'M' and self.Ps[i].v == 0: self.T[i] = 'W'; self.Ps[i] = const(1); extra = 4
        for i in range(len(self.T)):
            if self.A[i]: self.Ps[i] = self.Ps[i].add(extra)
        self.W = self.W.add(extra); self.add('G', const(1))
    def marks(self):
        idx = sorted([i for i in range(len(self.T)) if self.A[i]], key=lambda i: self.Ps[i].v)
        return [(self.T[i], self.Ps[i]) for i in idx]
    def shape(self): return ''.join(t for t, p in self.marks())

def start(ratio, scale=2 ** 120):
    E = scale; mv = int(E * ratio) // 2 * 2
    m = M.__new__(M); m.T = []; m.Ps = []; m.A = []; m.halted = False; m.bad = 0; m.outcomes = []; m.rd = 0
    m.coset = None; m.forced = None; m.fi = 0
    m.W = P((0, SC, 0), (E + 1) * SC)
    m.add('G', const(1)); m.add('M', P((SC, 0, 0), mv * SC)); m.add('M', m.W.add(-2))
    return m

def explore(ratio, cut_bits, max_rounds=200, part=0, nparts=1, split_bits=10):
    m0 = start(ratio); c0 = Coset([0, 1], [[2, 0], [0, 2]])
    stack = [(m0, c0, [], 0, ())]
    routes = collections.defaultdict(F); ew = collections.defaultdict(F); lost = F(0); splitc = 0
    while stack:
        ms, cs, forced, rd, hist = stack.pop()
        m = ms.clone(); c = cs.copy(); m.coset = c; m.forced = forced; m.fi = 0
        try:
            m.do_round()
        except Branch:
            nb = cs.bits + len(forced) + 1
            if nb > cut_bits: lost += F(1, 2 ** (cs.bits + len(forced))); continue
            for o in (2, 0):
                if nparts > 1 and nb == split_bits:
                    splitc += 1
                    if splitc % nparts != part: continue
                stack.append((ms, cs, forced + [o], rd, hist))
            continue
        except AssertionError:
            continue
        if m.halted or m.bad: continue
        sh = m.shape(); mk = m.marks(); h2 = hist + (sh,)
        if sh == 'GM' and mk[1][1].v == m.W.v - 2 * SC: continue
        if sh == 'GMM' and mk[2][1].v == m.W.v - 2 * SC: continue
        if sh == 'GWWW': routes[(h2, tuple(m.outcomes))] += F(1, 2 ** c.bits)
        if sh == 'GWWWW': ew[(h2, tuple(m.outcomes))] += F(1, 2 ** c.bits)
        if rd + 1 >= max_rounds: lost += F(1, 2 ** c.bits); continue
        stack.append((m, c, [], rd + 1, h2))
    return routes, ew, lost

if __name__ == '__main__':
    cut = int(sys.argv[1]); part = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    nparts = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    routes, ew, lost = explore(0.5, cut, part=part, nparts=nparts)
    suf = f"_{part}of{nparts}" if nparts > 1 else ""
    with open(f'../fasttree_routes{cut}{suf}.jsonl', 'w') as f:
        for (h, o), p in sorted(routes.items(), key=lambda x: -x[1]):
            f.write(json.dumps({'ratio': 0.5, 'measure': float(p), 'shapes': list(h), 'outs': list(o)}) + '\n')
    with open(f'../fasttree_ew{cut}{suf}.jsonl', 'w') as f:
        for (h, o), p in sorted(ew.items(), key=lambda x: -x[1]):
            f.write(json.dumps({'ratio': 0.5, 'measure': float(p), 'shapes': list(h), 'outs': list(o)}) + '\n')
    print(f"cut {cut} part {part}/{nparts}: {len(routes)} G W W W prefixes (measure {float(sum(routes.values())):.4e}), "
          f"{len(ew)} G W W W W prefixes (measure {float(sum(ew.values())):.3e}), lost {float(lost):.3e}, precision failures {PREC[0]}", flush=True)
