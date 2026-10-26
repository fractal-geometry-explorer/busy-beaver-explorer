"""Concolic run of the mark model: every position is an affine form in some unknowns (with rational coefficients)
plus a concrete value.  Order tests use the concrete value (positions are far apart); each d mod 4 test is recorded
as a congruence on its form.  Output: the path (branch sequence), the congruences, and the final forms."""
from fractions import Fraction as F

class Pos:
    __slots__ = ('f', 'v')
    def __init__(self, f, v): self.f = tuple(f); self.v = v
    def __add__(self, c):
        if isinstance(c, Pos): return Pos([a + b for a, b in zip(self.f, c.f)], self.v + c.v)
        f = list(self.f); f[-1] += c; return Pos(f, self.v + c)
    def __sub__(self, c):
        if isinstance(c, Pos): return Pos([a - b for a, b in zip(self.f, c.f)], self.v - c.v)
        return self + (-c)
    def half(self):
        if isinstance(self.v, int):
            assert self.v % 2 == 0
            return Pos([a / 2 for a in self.f], self.v // 2)
        return Pos([a / 2 for a in self.f], self.v / 2)

class Model:
    def __init__(self, nvar):
        self.nvar = nvar; self.T = []; self.P = []; self.A = []
        self.halted = False; self.bad = 0; self.cong = []; self.path = []; self.endd = []; self.rd = 0
        self.force = None; self.outcomes = []
    def const(self, c): return Pos([F(0)] * self.nvar + [F(c)], c)
    def var(self, i, val): f = [F(0)] * (self.nvar + 1); f[i] = F(1); return Pos(f, val)
    def add(self, t, p):
        for i in range(len(self.T)):
            if not self.A[i]: self.T[i] = t; self.P[i] = p; self.A[i] = True; return i
        self.T.append(t); self.P.append(p); self.A.append(True); return len(self.T) - 1
    def first_right(self, x):
        b = -1
        for i in range(len(self.T)):
            if self.A[i] and self.P[i].v > x.v and (b < 0 or self.P[i].v < self.P[b].v): b = i
        return b
    def last_mark(self):
        b = -1
        for i in range(len(self.T)):
            if self.A[i] and (b < 0 or self.P[i].v > self.P[b].v): b = i
        return b
    def packet_back(self, x):
        b = -1
        for i in range(len(self.T)):
            if self.A[i] and self.P[i].v < x.v and self.T[i] != 'M' and (b < 0 or self.P[i].v > self.P[b].v): b = i
        if b < 0: return -1
        if self.T[b] == 'B': self.halted = True; return -1
        if self.T[b] == 'G': self.P[b] = self.P[b] + 2; self.path.append('pg'); return b
        q = self.P[b]; self.T[b] = 'M'; self.P[b] = q - 1; self.path.append('pw'); return self.add('G', q + 1)
    def shift_from(self, x):
        k = self.first_right(x)
        if k < 0:
            self.W = self.W + 2; self.add('M', self.W - 2); self.path.append('s0'); return self.packet_back(self.W - 2)
        t = self.T[k]
        if t == 'M': self.T[k] = 'G'; self.path.append('sM'); return k
        if t == 'W': self.T[k] = 'B'; self.path.append('sW'); return self.packet_back(self.P[k])
        if t == 'B': self.T[k] = 'W'; self.P[k] = self.P[k] + 2; self.path.append('sB'); return self.packet_back(self.P[k])
        self.bad = 2; return -1
    def do_round(self):
        self.rd += 1
        gap = -1
        for i in range(len(self.T)):
            if self.A[i] and self.T[i] == 'G' and self.P[i].v == 1: gap = i
        while gap >= 0 and not self.halted and not self.bad:
            g = self.P[gap]; m = self.first_right(g)
            if m < 0:
                self.A[gap] = False; self.W = self.W + 3; self.add('M', self.W - 2); self.path.append('g0')
                gap = self.packet_back(self.W - 2); continue
            t = self.T[m]
            if t == 'M':
                d = self.P[m] - g - 3
                if self.force is None:
                    if d.v < 0 or d.v % 2: self.bad = 3; return
                    res = d.v % 4
                else:
                    if d.v < 0 or not self.force: self.bad = 3; return
                    res = self.force.pop(0)
                self.outcomes.append(res)
                last = (m == self.last_mark())
                if last: self.endd.append((self.rd, d))
                self.cong.append((d, res, 4))
                if res == 0:
                    h = d.half(); self.P[m] = g + h - 1; self.P[gap] = g + h + 1; self.path.append('h' + ('E' if last else ''))
                else:
                    self.A[gap] = False; self.T[m] = 'W'; self.P[m] = g + d.half() + 3; self.path.append('m' + ('E' if last else ''))
                    gap = self.packet_back(self.P[m])
            elif t == 'W':
                x = self.P[m]; self.A[gap] = False; self.A[m] = False; self.path.append('w'); gap = self.shift_from(x)
            elif t == 'B':
                self.T[m] = 'W'; self.P[m] = self.P[m] - 1; self.path.append('b'); gap = self.shift_from(self.P[m])
            else: self.bad = 4; return
        extra = 2
        for i in range(len(self.T)):
            if self.A[i] and self.T[i] == 'M' and self.P[i].v == 0: self.T[i] = 'W'; self.P[i] = self.const(1); extra = 4
        for i in range(len(self.T)):
            if self.A[i]: self.P[i] = self.P[i] + extra
        self.W = self.W + extra; self.add('G', self.const(1)); self.path.append('|')
    def marks(self):
        idx = sorted([i for i in range(len(self.T)) if self.A[i]], key=lambda i: self.P[i].v)
        return [(self.T[i], self.P[i]) for i in idx]
    def shape(self): return ''.join(t for t, p in self.marks())

def fmt(p, names):
    s = []
    for a, nmv in zip(p.f[:-1], names):
        if a: s.append(f"{a}*{nmv}" if a != 1 else nmv)
    c = p.f[-1]
    if c or not s: s.append(str(c))
    return ' + '.join(s).replace('+ -', '- ')
