#!/usr/bin/env python3
"""rsim: an exact macro simulator with recursively proved cycle rules (Python big integers).

The tape is two stacks of runs (block of K cells, count), exactly as in c/msim.c, and one basic macro step is the
macro step of msim.c (the machine run on a window of two blocks until the head leaves it; a run is crossed at once
when the crossing is in a steady state).  On top of that, cycles are jumped:

* the signature of a configuration is (state, direction, the block symbols of all runs on both sides), the counts
  left out;
* when a signature comes back after the same number of actions as the last time, the actions between its last two
  occurrences (basic macro steps and applications of rules proved before) are replayed symbolically from the older
  configuration, with every count that changed (or is large) replaced by a variable.  The replay asserts lower
  bounds on the variables whenever a decision depends on a count (a count is at least 2 before one copy is taken
  from it, a rule's minimums hold before it is applied).  If the replay ends in the same signature with every
  variable changed by a constant and every other count unchanged, that is a proof of the one-cycle rule for every
  value of the variables above the minimums: the rule then is applied k times at once (k from the decreasing
  variables), the step count being the exact sum of the cycle's step polynomial;
* rules are used as steps of later replays (so rules of rules are proved), applied symbolically when the number of
  repetitions is either a concrete number or (count - min + 1) of a single variable that drops by 1 per cycle.

Nothing is guessed: a rule is used only after its symbolic proof, and only while its minimums hold, so the run is
the machine's run, with exact step counts; a halting transition inside a replay makes the proof fail, so a halt can
never be jumped over (it would be met by a basic step).

usage (library): see run_rsim.py.
"""
from fractions import Fraction
from math import comb
import sys

INF = None


# ---------------------------------------------------------------- linear forms and polynomials
class Lin:
    """c + sum a[v] x_v  (a: dict var -> nonzero int)"""
    __slots__ = ('c', 'a')

    def __init__(self, c, a):
        self.c = c
        self.a = a

    def __repr__(self):
        return '%d%s' % (self.c, ''.join(' %+d*x%d' % (k, v) for v, k in sorted(self.a.items())))


def ladd(x, y):
    if isinstance(x, int):
        if isinstance(y, int):
            return x + y
        return Lin(y.c + x, y.a)
    if isinstance(y, int):
        return Lin(x.c + y, x.a)
    a = dict(x.a)
    for v, k in y.a.items():
        n = a.get(v, 0) + k
        if n:
            a[v] = n
        else:
            del a[v]
    if not a:
        return x.c + y.c
    return Lin(x.c + y.c, a)


def lmul(x, k):
    if isinstance(x, int):
        return x * k
    if k == 0:
        return 0
    return Lin(x.c * k, {v: a * k for v, a in x.a.items()})


def leq(x, y):
    if isinstance(x, int) or x is None:
        return isinstance(y, int) and x == y if x is not None else y is None
    if isinstance(y, int) or y is None:
        return False
    return x.c == y.c and x.a == y.a


class Poly:
    """dict monomial -> Fraction; monomial = tuple of (var, exp) sorted; var -1 is the summation index j."""
    __slots__ = ('t',)

    def __init__(self, t=None):
        self.t = t if t is not None else {}

    @staticmethod
    def const(c):
        return Poly({(): Fraction(c)} if c else {})

    @staticmethod
    def of(x):
        if isinstance(x, int):
            return Poly.const(x)
        if isinstance(x, Poly):
            return x
        t = {((v, 1),): Fraction(a) for v, a in x.a.items()}
        if x.c:
            t[()] = Fraction(x.c)
        return Poly(t)

    def add(self, o, s=1):
        t = dict(self.t)
        for m, c in o.t.items():
            n = t.get(m, 0) + s * c
            if n:
                t[m] = n
            else:
                t.pop(m, None)
        return Poly(t)

    def scale(self, k):
        if k == 0:
            return Poly()
        return Poly({m: c * k for m, c in self.t.items()})

    def mul(self, o):
        t = {}
        for m1, c1 in self.t.items():
            for m2, c2 in o.t.items():
                d = dict(m1)
                for v, e in m2:
                    d[v] = d.get(v, 0) + e
                m = tuple(sorted(d.items()))
                n = t.get(m, 0) + c1 * c2
                if n:
                    t[m] = n
                else:
                    t.pop(m, None)
        return Poly(t)

    def is_const(self):
        return all(m == () for m in self.t)

    def value(self, env):
        s = Fraction(0)
        for m, c in self.t.items():
            p = c
            for v, e in m:
                p *= env[v] ** e
            s += p
        return s

    def degree(self):
        return max((sum(e for _, e in m) for m in self.t), default=0)


# Faulhaber: S_p(k) = sum_{j=0}^{k-1} j^p as a list of Fraction coefficients of k^0..k^(p+1)
def _bernoulli(n):
    B = [Fraction(0)] * (n + 1)
    B[0] = Fraction(1)
    for m in range(1, n + 1):
        B[m] = -sum(comb(m + 1, i) * B[i] for i in range(m)) / (m + 1)
    return B          # B[1] = -1/2


_B = _bernoulli(40)
_S = {}


def faulhaber(p):
    r = _S.get(p)
    if r is None:
        co = [Fraction(0)] * (p + 2)
        for i in range(p + 1):
            co[p + 1 - i] += Fraction(comb(p + 1, i)) * _B[i] / (p + 1)
        r = _S[p] = co
    return r


def sum_poly(P, es, ds, k):
    """sum_{j=0}^{k-1} P(es + j*ds): P a Poly in rule variables 0..n-1, es values (int or Lin), ds ints, k int or Lin.
    Returns a Poly in the proof variables (a constant Poly when everything is concrete)."""
    # substitution: v -> es[v] + ds[v] * j     (j = var -1)
    sub = {}
    for v in range(len(es)):
        p = Poly.of(es[v])
        if ds[v]:
            p = p.add(Poly({((-1, 1),): Fraction(ds[v])}))
        sub[v] = p
    pw = {}

    def power(v, e):
        key = (v, e)
        r = pw.get(key)
        if r is None:
            r = sub[v] if e == 1 else power(v, e - 1).mul(sub[v])
            pw[key] = r
        return r
    Q = Poly()
    for m, c in P.t.items():
        term = Poly.const(1).scale(c)
        for v, e in m:
            term = term.mul(power(v, e))
        Q = Q.add(term)
    # collect by powers of j
    byj = {}
    for m, c in Q.t.items():
        e = 0
        rest = []
        for v, x in m:
            if v == -1:
                e = x
            else:
                rest.append((v, x))
        byj.setdefault(e, {})
        rm = tuple(rest)
        byj[e][rm] = byj[e].get(rm, 0) + c
    kp = Poly.of(k)
    kpow = [Poly.const(1)]
    total = Poly()
    for e, coef in byj.items():
        Fs = faulhaber(e)
        while len(kpow) < len(Fs):
            kpow.append(kpow[-1].mul(kp))
        Sk = Poly()
        for i, f in enumerate(Fs):
            if f:
                Sk = Sk.add(kpow[i].scale(f))
        total = total.add(Poly({m: c for m, c in coef.items() if c}).mul(Sk))
    return total


def sum_concrete(P, xs, ds, k):
    """the same, everything concrete: returns an int"""
    # Fast path: P(x + j d) evaluated as a polynomial in j with integer-ish coefficients.
    # Expand monomial by monomial using binomial expansion.
    coef = {}      # power of j -> Fraction
    for m, c in P.t.items():
        poly = [Fraction(c)]   # coefficients in j
        for v, e in m:
            x, d = xs[v], ds[v]
            # (x + d j)^e
            b = [comb(e, i) * x ** (e - i) * d ** i for i in range(e + 1)]
            newp = [0] * (len(poly) + e)
            for i, a in enumerate(poly):
                if a:
                    for i2, bb in enumerate(b):
                        if bb:
                            newp[i + i2] += a * bb
            poly = newp
        for i, a in enumerate(poly):
            if a:
                coef[i] = coef.get(i, 0) + a
    tot = Fraction(0)
    for e, a in coef.items():
        Fs = faulhaber(e)
        s = Fraction(0)
        kp = 1
        for f in Fs:
            if f:
                s += f * kp
            kp *= k
        tot += a * s
    if tot.denominator != 1:
        raise ArithmeticError('non-integer step sum')
    return int(tot)


class ProofFail(Exception):
    pass


# ---------------------------------------------------------------- the window table (as c/msim.c)
def parse(m):
    rows = m.split('_')
    W, D, S = [], [], []
    for row in rows:
        w, d, s = [], [], []
        for b in (0, 1):
            t = row[3 * b:3 * b + 3]
            if t[2] == '-':
                w.append(0); d.append(0); s.append(-1)
            else:
                w.append(int(t[0])); d.append(1 if t[1] == 'R' else -1); s.append(ord(t[2]) - 65)
        W.append(w); D.append(d); S.append(s)
    return W, D, S


def build_table(m, K):
    W, D, S = parse(m)
    NS = len(W)
    T = {}
    for s in range(NS):
        for dr in (0, 1):
            for top in range(1 << K):
                for beh in range(1 << K):
                    lb, rb = (beh, top) if dr else (top, beh)
                    c = [(lb >> (K - 1 - i)) & 1 for i in range(K)] + [(rb >> (K - 1 - i)) & 1 for i in range(K)]
                    p = K if dr else K - 1
                    st = s
                    k = 0
                    res = None
                    while 0 <= p < 2 * K:
                        if k > 100000:
                            res = 3; break
                        y = c[p]
                        if S[st][y] < 0:
                            res = 2; break
                        c[p] = W[st][y]; p += D[st][y]; st = S[st][y]; k += 1
                    if res is None:
                        far = (p >= 2 * K) if dr else (p < 0)
                        res = 0 if far else 1
                    nl = nr = 0
                    for i in range(K):
                        nl = nl * 2 + c[i]; nr = nr * 2 + c[K + i]
                    nt, nb = (nr, nl) if dr else (nl, nr)
                    T[(s, dr, top, beh)] = (res, st, nt, nb, k)
    return T


# ---------------------------------------------------------------- the simulator
class Rule:
    __slots__ = ('sig', 'spec', 'mins', 'deltas', 'P', 'nv', 'dec', 'uses', 'level', 'id', 'seglen')

    def __init__(self, sig, spec, mins, deltas, P, level, rid, seglen):
        self.sig = sig; self.spec = spec; self.mins = mins; self.deltas = deltas; self.P = P
        self.nv = len(mins); self.dec = [v for v in range(self.nv) if deltas[v] < 0]
        self.uses = 0; self.level = level; self.id = rid; self.seglen = seglen


class RSim:
    def __init__(self, m, K=4, thresh=6, maxseg=200000, log=None, sthresh=1, cp='l', depth=6, maxfails=200):
        self.m = m
        self.K = K
        self.T = build_table(m, K)
        self.L = [(0, INF)]
        self.R = [(0, INF)]
        self.st = 0
        self.dr = 1
        self.steps = 0
        self.nbasic = 0
        self.halted = None
        self.stop = None
        self.thresh = thresh
        self.sthresh = sthresh
        self.cp = cp
        self.depth = depth
        self.maxfails = maxfails
        self.maxseg = maxseg
        self.rules = {}
        self.nrules = 0
        self.napply = 0
        self.nproofs = 0
        self.nfail = 0
        self.past = {}
        self.acts = []
        self.abase = 0
        self.fails = {}
        self.on_event = None      # callback(sim, side) when the head enters a fresh block (side 'r' or 'l')
        self.log = log
        self.maxlevel = 0

    # -------- concrete basic macro step (c/msim.c)
    def basic(self):
        st, dr = self.st, self.dr
        if dr:
            F, B = self.R, self.L
        else:
            F, B = self.L, self.R
        ft = F[-1]
        bt = B[-1]
        top, cnt = ft
        t = self.T[(st, dr, top, bt[0])]
        res, ns, nt, nb, k = t
        if res == 3:
            self.stop = 'loop'; return
        if res == 2:
            self.steps += k + 1
            self.halted = (self.steps, ns, dr)
            return
        fresh = cnt is INF
        self.steps += k
        if res == 0:
            # pop1 F, pop1 B
            if cnt is not INF:
                if cnt == 1:
                    F.pop()
                else:
                    F[-1] = (top, cnt - 1)
            bc = bt[1]
            if bc is not INF:
                if bc == 1:
                    B.pop()
                else:
                    B[-1] = (bt[0], bc - 1)
            self._push(B, nb, 1)
            self._push(B, nt, 1)
            if ns == st and not fresh and cnt >= 2:
                u = self.T[(st, dr, top, nt)]
                if u[0] == 0 and u[1] == st and u[2] == nt:
                    kk = cnt - 1
                    f2 = F[-1]
                    if f2[0] != top or f2[1] is INF or f2[1] < kk:
                        raise RuntimeError('bad run')
                    if f2[1] == kk:
                        F.pop()
                    else:
                        F[-1] = (top, f2[1] - kk)
                    # pop1 B (removes the nt just pushed)
                    b2 = B[-1]
                    if b2[1] == 1:
                        B.pop()
                    else:
                        B[-1] = (b2[0], b2[1] - 1)
                    self._push(B, u[3], kk)
                    self._push(B, u[2], 1)
                    self.steps += kk * u[4]
            self.st = ns
        else:
            if cnt is not INF:
                if cnt == 1:
                    F.pop()
                else:
                    F[-1] = (top, cnt - 1)
            bc = bt[1]
            if bc is not INF:
                if bc == 1:
                    B.pop()
                else:
                    B[-1] = (bt[0], bc - 1)
            self._push(F, nt, 1)
            self._push(F, nb, 1)
            self.st = ns
            self.dr = 1 - dr
        if fresh and self.on_event is not None:
            self.on_event(self, 'r' if F is self.R else 'l')

    @staticmethod
    def _push(S, v, c):
        t = S[-1]
        if t[0] == v and t[1] is not INF:
            S[-1] = (v, t[1] + c)
        else:
            S.append((v, c))

    def sig(self):
        th = self.sthresh
        return (self.st, self.dr, tuple(r if (r[1] is INF or r[1] < th) else (r[0], -1) for r in self.L),
                tuple(r if (r[1] is INF or r[1] < th) else (r[0], -1) for r in self.R))

    # -------- concrete rule application
    def applicable(self, rule):
        L, R = self.L, self.R
        nL = len(L)
        xs = [None] * rule.nv
        for i, sp in enumerate(rule.spec):
            c = L[i][1] if i < nL else R[i - nL][1]
            if sp[0] == 0:
                if c != sp[1]:
                    return None
            else:
                v = sp[1]
                if c is INF or c < rule.mins[v]:
                    return None
                xs[v] = c
        return xs

    def apply(self, rule, xs):
        k = None
        for v in rule.dec:
            kk = (xs[v] - rule.mins[v]) // (-rule.deltas[v]) + 1
            if k is None or kk < k:
                k = kk
        if k is None:
            self.stop = 'rule %d repeats forever' % rule.id
            return
        self.steps += sum_concrete(rule.P, xs, rule.deltas, k)
        L, R = self.L, self.R
        nL = len(L)
        for i, sp in enumerate(rule.spec):
            if sp[0] == 1:
                v = sp[1]
                nv = xs[v] + k * rule.deltas[v]
                if i < nL:
                    L[i] = (L[i][0], nv)
                else:
                    R[i - nL] = (R[i - nL][0], nv)
        self._normalize(L)
        self._normalize(R)
        rule.uses += 1
        self.napply += 1
        return k

    @staticmethod
    def _normalize(S):
        if not any(r[1] == 0 for r in S if r[1] is not INF and isinstance(r[1], int)):
            return
        out = []
        for r in S:
            if r[1] is not INF and isinstance(r[1], int) and r[1] == 0:
                continue
            if out and out[-1][0] == r[0] and out[-1][1] is not INF and r[1] is not INF:
                out[-1] = (r[0], ladd(out[-1][1], r[1]))
            else:
                out.append(r)
        S[:] = out

    # -------- main loop
    def at_checkpoint(self):
        """rules are looked for and used only when the head is about to enter a fresh block on the left (every
        cycle of the machines studied here passes there); any other choice is also exact, only slower."""
        if self.cp == 'l':
            return self.dr == 0 and self.L[-1][1] is INF
        if self.cp == 'r':
            return self.dr == 1 and self.R[-1][1] is INF
        return True

    def run(self, max_basic=None, max_steps=None, until=None):
        rules = self.rules
        past = self.past
        while self.halted is None and self.stop is None:
            if max_basic is not None and self.nbasic >= max_basic:
                return
            if max_steps is not None and self.steps >= max_steps:
                return
            if until is not None and until(self):
                return
            if self.at_checkpoint():
                sig = self.sig()
                rl = rules.get(sig)
                done = False
                if rl:
                    for r in rl:
                        xs = self.applicable(r)
                        if xs is not None:
                            self.apply(r, xs)
                            self.acts.append(r)
                            done = True
                            break
                if done:
                    continue
                n = self.abase + len(self.acts)
                olds = past.get(sig)
                if olds is None:
                    olds = past[sig] = []
                elif self.fails.get(sig, 0) < self.maxfails:
                    got = None
                    for old in reversed(olds):
                        seglen = n - old[2]
                        if seglen > self.maxseg:
                            break
                        if seglen < 2:
                            continue
                        r = self.prove(sig, old, self.acts[old[2] - self.abase:])
                        if r is not None:
                            got = r
                            break
                    if got is not None:
                        rules.setdefault(sig, []).append(got)
                        xs = self.applicable(got)
                        if xs is not None:
                            self.apply(got, xs)
                            self.acts.append(got)
                            past.pop(sig, None)
                            continue
                olds.append((tuple(self.L), tuple(self.R), n))
                if len(olds) > self.depth:
                    del olds[0]
            self.basic()
            self.nbasic += 1
            self.acts.append(None)
            if len(self.acts) > 4000000 or len(past) > 20000:
                n = self.abase + len(self.acts)
                self.acts = []
                self.abase = n
                past.clear()

    # -------- symbolic replay
    def prove(self, sig, old, seg):
        self.nproofs += 1
        oL, oR = old[0], old[1]
        L, R = self.L, self.R
        nv = 0
        mins = []
        SL, SR, spec = [], [], []
        for src, cur, dst in ((oL, L, SL), (oR, R, SR)):
            for i, (s, c) in enumerate(src):
                cn = cur[i][1]
                if c is not INF and (c != cn or c >= self.thresh):
                    dst.append((s, Lin(0, {nv: 1})))
                    mins.append(1)
                    spec.append((1, nv))
                    nv += 1
                else:
                    dst.append((s, c))
                    spec.append((0, c))
        ctx = _Sym(self, SL, SR, sig[0], sig[1], mins)
        level = 1
        try:
            for a in seg:
                if a is None:
                    ctx.basic()
                else:
                    ctx.apply(a)
                    level = max(level, a.level + 1)
        except ProofFail as e:
            self.nfail += 1
            self.fails[sig] = self.fails.get(sig, 0) + 1
            return None
        # check the end
        if ctx.st != sig[0] or ctx.dr != sig[1] or len(ctx.L) != len(oL) or len(ctx.R) != len(oR):
            self.fails[sig] = self.fails.get(sig, 0) + 1
            return None
        deltas = [0] * nv
        allc = ctx.L + ctx.R
        allo = list(oL) + list(oR)
        for i, sp in enumerate(spec):
            s, c = allc[i]
            if s != allo[i][0]:
                self.fails[sig] = self.fails.get(sig, 0) + 1
                return None
            if sp[0] == 0:
                if not leq(c, sp[1]):
                    self.fails[sig] = self.fails.get(sig, 0) + 1
                    return None
            else:
                v = sp[1]
                if isinstance(c, int) or c is INF or len(c.a) != 1 or c.a.get(v) != 1:
                    self.fails[sig] = self.fails.get(sig, 0) + 1
                    return None
                deltas[v] = c.c
        if all(d >= 0 for d in deltas):
            # a rule that repeats forever: only accept it after an independent check (reported, not used)
            self.fails[sig] = self.fails.get(sig, 0) + 1
            if self.log:
                self.log('non-decreasing rule found at steps %d (not used)' % self.steps)
            return None
        self.nrules += 1
        r = Rule(sig, spec, mins, deltas, ctx.Pfull, level, self.nrules, len(seg))
        self.maxlevel = max(self.maxlevel, level)
        return r

    def tape_str(self):
        K = self.K

        def w(s):
            return format(s, '0%db' % K)
        parts = []
        for s, c in self.L:
            if c is INF:
                continue
            parts.append(w(s) + ('^%d' % c if c != 1 else ''))
        mid = ' %s%s |' % ('ABCDEFGH'[self.st], '>' if self.dr else '<')
        rp = []
        for s, c in reversed(self.R):
            if c is INF:
                continue
            rp.append(w(s) + ('^%d' % c if c != 1 else ''))
        return ' '.join(parts) + mid + (' ' + ' '.join(rp) if rp else '')


class _Sym:
    """symbolic replay context"""

    def __init__(self, sim, L, R, st, dr, mins):
        self.sim = sim
        self.T = sim.T
        self.L = L
        self.R = R
        self.st = st
        self.dr = dr
        self.mins = mins
        self.P = Poly()
        self.cst = 0          # concrete part of the steps, kept as int for speed

    def need_ge(self, e, m):
        if e is INF:
            raise ProofFail('inf')
        if isinstance(e, int):
            if e < m:
                raise ProofFail('small')
            return
        lo = e.c
        for v, a in e.a.items():
            if a < 0:
                raise ProofFail('neg')
            lo += a * self.mins[v]
        if lo >= m:
            return
        v, a = next(iter(e.a.items()))
        need = m - lo
        self.mins[v] += -(-need // a)

    def addsteps(self, x, mul=1):
        if isinstance(x, int):
            self.cst += x * mul
        else:
            self.P = self.P.add(Poly.of(x).scale(mul))

    @staticmethod
    def push(S, v, c):
        t = S[-1]
        if t[0] == v and t[1] is not INF:
            S[-1] = (v, ladd(t[1], c))
        else:
            S.append((v, c))

    def pop1(self, S):
        s, c = S[-1]
        if c is INF:
            return
        if isinstance(c, int):
            if c == 1:
                S.pop()
            else:
                S[-1] = (s, c - 1)
        else:
            self.need_ge(c, 2)
            S[-1] = (s, ladd(c, -1))

    def basic(self):
        st, dr = self.st, self.dr
        if dr:
            F, B = self.R, self.L
        else:
            F, B = self.L, self.R
        if len(F) == 0 or len(B) == 0:
            raise ProofFail('empty')
        top, cnt = F[-1]
        t = self.T[(st, dr, top, B[-1][0])]
        res, ns, nt, nb, k = t
        if res >= 2:
            raise ProofFail('halt or loop')
        fresh = cnt is INF
        self.cst += k
        if res == 0:
            self.pop1(F)
            self.pop1(B)
            self.push(B, nb, 1)
            self.push(B, nt, 1)
            if ns == st and not fresh:
                big = False
                if isinstance(cnt, int):
                    big = cnt >= 2
                else:
                    self.need_ge(cnt, 2)
                    big = True
                if big:
                    u = self.T[(st, dr, top, nt)]
                    if u[0] == 0 and u[1] == st and u[2] == nt:
                        kk = ladd(cnt, -1)
                        f2 = F[-1]
                        if f2[0] != top or f2[1] is INF:
                            raise ProofFail('bad run')
                        rest = ladd(f2[1], lmul(kk, -1))
                        if isinstance(rest, int):
                            if rest < 0:
                                raise ProofFail('neg run')
                            if rest == 0:
                                F.pop()
                            else:
                                F[-1] = (top, rest)
                        else:
                            self.need_ge(rest, 1)
                            F[-1] = (top, rest)
                        self.pop1(B)
                        self.push(B, u[3], kk)
                        self.push(B, u[2], 1)
                        self.addsteps(kk, u[4])
            self.st = ns
        else:
            self.pop1(F)
            self.pop1(B)
            self.push(F, nt, 1)
            self.push(F, nb, 1)
            self.st = ns
            self.dr = 1 - dr

    def apply(self, rule):
        sig = rule.sig
        if (self.st, self.dr) != sig[:2] or len(self.L) != len(sig[2]) or len(self.R) != len(sig[3]):
            raise ProofFail('rule shape')
        if tuple(r[0] for r in self.L) != tuple(x[0] for x in sig[2]) or tuple(r[0] for r in self.R) != tuple(x[0] for x in sig[3]):
            raise ProofFail('rule shape')
        L, R = self.L, self.R
        nL = len(L)
        es = [None] * rule.nv
        for i, sp in enumerate(rule.spec):
            c = L[i][1] if i < nL else R[i - nL][1]
            if sp[0] == 0:
                if not leq(c, sp[1]):
                    raise ProofFail('rule const')
            else:
                if c is INF:
                    raise ProofFail('rule inf')
                es[sp[1]] = c
        # number of repetitions
        conc = [v for v in rule.dec if isinstance(es[v], int)]
        symb = [v for v in rule.dec if not isinstance(es[v], int)]
        if conc:
            k = None
            for v in conc:
                if es[v] < rule.mins[v]:
                    raise ProofFail('rule min')
                kk = (es[v] - rule.mins[v]) // (-rule.deltas[v]) + 1
                if k is None or kk < k:
                    k = kk
            for v in symb:
                # the symbolic one must not be the limiting one
                self.need_ge(es[v], rule.mins[v] + (-rule.deltas[v]) * (k - 1))
        else:
            if len(symb) != 1 or rule.deltas[symb[0]] != -1:
                raise ProofFail('rule count')
            v = symb[0]
            self.need_ge(es[v], rule.mins[v])
            k = ladd(es[v], 1 - rule.mins[v])
        for v in range(rule.nv):
            if v not in rule.dec:
                self.need_ge(es[v], rule.mins[v])
        # steps
        if isinstance(k, int) and all(isinstance(e, int) for e in es):
            self.cst += sum_concrete(rule.P, es, rule.deltas, k)
        else:
            self.P = self.P.add(sum_poly(rule.P, es, rule.deltas, k))
        for i, sp in enumerate(rule.spec):
            if sp[0] == 1:
                v = sp[1]
                nvv = ladd(es[v], lmul(k, rule.deltas[v]))
                if i < nL:
                    L[i] = (L[i][0], nvv)
                else:
                    R[i - nL] = (R[i - nL][0], nvv)
        for S in (L, R):
            out = []
            for r in S:
                if r[1] is not INF and isinstance(r[1], int) and r[1] == 0:
                    continue
                if isinstance(r[1], int) and r[1] is not INF and r[1] < 0:
                    raise ProofFail('negative')
                if out and out[-1][0] == r[0] and out[-1][1] is not INF and r[1] is not INF:
                    out[-1] = (r[0], ladd(out[-1][1], r[1]))
                else:
                    out.append(r)
            S[:] = out

    @property
    def Pfull(self):
        return self.P.add(Poly.const(self.cst))


