"""rleaccel with recursive (level-2+) cycle rules, after the proof system of Shawn Ligocki's Quick_Sim.

tools/py/bbtools/rleaccel.py proves a one-cycle rule by replaying the cycle with plain macro steps, and forgets
every past shape whenever a rule is applied.  So a cycle that itself contains a jump (an inner rule applied k times,
k depending on a run length) is never proved: the outer counter is walked one inner jump at a time.

Here:
  * past shapes are kept when a rule is applied (a rule application counts as one macro step, as in Quick_Sim);
  * the symbolic replay of a cycle may apply an already proved rule to symbolic run lengths: the jump count k is
    then an expression (exactly one shrinking run, shrinking by 1 per cycle, so k = x - min + 1 is linear), the other
    lengths change by k*delta, and the steps by the sum of the inner rule's step polynomial over the k cycles
    (Faulhaber sums);
  * step counts are polynomials (exact rational coefficients, integral at integer points), so rules of rules of
    rules work the same way;
  * a rule is used concretely only when its minimums hold, exactly as before, and the step count of k cycles is the
    exact sum of its step polynomial.

usage: python3 tools/py/bbtools/rleaccel_rec.py MACHINE [K] [SECONDS]      (or --macro N for a fixed macro count)

Trust level: trusted computation (Python); tools/tests/test_rleaccel_rec.py compares tape, state and step count with
direct runs, and the same check was run on 59 holdouts at three block sizes up to 3*10^9 steps (372 comparisons, 93
of them after level-2 rules had been used, no mismatch).

Nothing is guessed: every rule is a symbolic execution of the macro machine in which each step is either a macro
step or an application of an earlier proved rule within its proved range.
"""
import sys
import os
from fractions import Fraction

try:
    from .rleaccel import Sim, Lin, ProofFail, INF
except ImportError:
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from rleaccel import Sim, Lin, ProofFail, INF  # noqa: E402

J = -1   # the summation index in polynomials


class Poly:
    """sum of coef * prod(vars); keys are sorted tuples of variable ids (J = the summation index)"""
    __slots__ = ("t",)

    def __init__(self, t=None):
        self.t = t or {}

    @staticmethod
    def of(x):
        if isinstance(x, Poly):
            return x
        if isinstance(x, (int, Fraction)):
            return Poly({(): Fraction(x)} if x else {})
        if isinstance(x, Lin):
            t = {(): Fraction(x.c)} if x.c else {}
            for v, a in x.a.items():
                if a:
                    t[(v,)] = Fraction(a)
            return Poly(t)
        raise TypeError(x)

    def __add__(self, o):
        o = Poly.of(o)
        t = dict(self.t)
        for k, c in o.t.items():
            n = t.get(k, 0) + c
            if n:
                t[k] = n
            else:
                t.pop(k, None)
        return Poly(t)

    def __mul__(self, o):
        o = Poly.of(o)
        t = {}
        for k1, c1 in self.t.items():
            for k2, c2 in o.t.items():
                k = tuple(sorted(k1 + k2))
                n = t.get(k, 0) + c1 * c2
                if n:
                    t[k] = n
                else:
                    t.pop(k, None)
        return Poly(t)

    __radd__ = __add__
    __rmul__ = __mul__

    def deg(self):
        return max((len(k) for k in self.t), default=0)

    def subst(self, m):
        """m: var -> Poly"""
        out = Poly()
        for k, c in self.t.items():
            term = Poly({(): c})
            for v in k:
                term = term * (m[v] if v in m else Poly({(v,): Fraction(1)}))
            out = out + term
        return out

    def by_power_of_J(self):
        out = {}
        for k, c in self.t.items():
            e = k.count(J)
            rest = tuple(v for v in k if v != J)
            out.setdefault(e, Poly())
            out[e] = out[e] + Poly({rest: c})
        return out

    def const(self):
        if any(k for k in self.t):
            return None
        c = self.t.get((), Fraction(0))
        return c

    def __repr__(self):
        return " + ".join("%s*%s" % (c, "*".join("x%d" % v if v >= 0 else "j" for v in k) or "1") for k, c in self.t.items()) or "0"


_faul = {}


def faulhaber(e):
    """coefficients a_i of S_e(k) = sum_{j=0}^{k-1} j^e = sum_i a_i k^i (Fractions)"""
    if e in _faul:
        return _faul[e]
    # solve by interpolation on k = 0..e+1
    pts = []
    s = 0
    for k in range(e + 2):
        pts.append((k, Fraction(s)))
        s += k ** e
    n = len(pts)
    # Lagrange -> monomial coefficients
    coef = [Fraction(0)] * n
    for i, (xi, yi) in enumerate(pts):
        num = [Fraction(1)]
        den = Fraction(1)
        for j2, (xj, _) in enumerate(pts):
            if j2 == i:
                continue
            num = [Fraction(0)] + num
            for t in range(len(num) - 1):
                num[t] -= xj * num[t + 1]
            den *= (xi - xj)
        for t in range(n):
            coef[t] += yi * num[t] / den
    _faul[e] = coef
    return coef


def sum_over_cycles(P, start, deltas, k):
    """sum_{j=0}^{k-1} P(x_v = start_v + j*deltas_v); start: v -> Poly, k: Poly (or int)"""
    m = {v: Poly.of(start[v]) + Poly({(J,): Fraction(deltas[v])}) * 1 if deltas[v] else Poly.of(start[v]) for v in start}
    Q = P.subst(m)
    k = Poly.of(k)
    total = Poly()
    kp = [Poly({(): Fraction(1)})]
    for e, coefP in sorted(Q.by_power_of_J().items()):
        a = faulhaber(e)
        S = Poly()
        for i, ai in enumerate(a):
            while len(kp) <= i:
                kp.append(kp[-1] * k)
            if ai:
                S = S + kp[i] * Poly({(): ai})
        total = total + coefP * S
    return total


class RecSim(Sim):
    """Sim with recursive rules (see the module docstring).  A rule is
    (spec, consts, mins, deltas, steps_poly, home, sigkey)."""

    def __init__(self, m, k=1, max_level=3, **kw):
        super().__init__(m, k, **kw)
        self.max_level = max_level
        self.nrec = 0           # rules whose proof used another rule
        self.levels = {}

    # ---- concrete application ----
    def apply_rule(self, rule):
        spec, consts, mins, deltas, P, home, level = rule
        L, R = self.L[-self.W:], self.R[-self.W:]
        xs = []
        for side, cur in ((0, L), (1, R)):
            sp = spec[side]
            cs = consts[side]
            if len(cur) != len(sp):
                return False
            for i in range(len(cur)):
                c = cur[i][1]
                v = sp[i]
                if v is None:
                    if c != cs[i]:
                        return False
                else:
                    if c == INF or c < mins[v]:
                        return False
                    xs.append(c)
        k = None
        for v, dl in enumerate(deltas):
            if dl < 0:
                kk = (xs[v] - mins[v]) // (-dl) + 1
                if k is None or kk < k:
                    k = kk
        if k is None:
            self.nonhalt = "cycle rule repeats forever"
            return True
        if P.deg() <= 1:
            st = P.t.get((), 0) * k
            for v, dl in enumerate(deltas):
                a = P.t.get((v,), 0)
                if a:
                    st += a * (k * xs[v] + dl * (k * (k - 1) // 2))
        else:
            st = sum_over_cycles(P, {v: xs[v] for v in range(len(xs))}, deltas, k).const()
        if isinstance(st, Fraction):
            assert st.denominator == 1, st
            st = st.numerator
        for v, dl in enumerate(deltas):
            side, i = home[v]
            (L if side == 0 else R)[i][1] = xs[v] + k * dl
        self.steps += int(st)
        self.njumps += 1
        return True

    def run(self, max_macro, stop=None):
        past = self.past
        rules = self.rules
        fails = self.fails
        while self.nmacro < max_macro and self.halted is None and self.nonhalt is None:
            self.nmacro += 1
            if self.prove:
                sig = self.sig()
                rl = rules.get(sig)
                done = False
                if rl:
                    for r in rl:
                        if self.apply_rule(r):
                            done = True
                            break
                if done:
                    continue          # past shapes are kept: an outer cycle may contain this jump
                old = past.get(sig)
                if old is not None:
                    nl = self.nmacro - old[4]
                    if (nl == old[6] and nl <= self.maxloop and fails.get(sig, 0) < 3
                            and self.proofcost <= 2 * self.nmacro + 100000):
                        self.proofcost += nl
                        try:
                            r = self.try_prove(sig, old, nl)
                            rules.setdefault(sig, []).append(r)
                            self.nrules += 1
                            if self.apply_rule(r):
                                past.clear()
                                continue
                        except ProofFail:
                            fails[sig] = fails.get(sig, 0) + 1
                past[sig] = (self.q, self.d, [r[:] for r in self.L[-self.W:]], [r[:] for r in self.R[-self.W:]],
                             self.nmacro, self.steps, self.nmacro - old[4] if old is not None else 0)
                if len(past) > 20000:
                    past.clear()
                if len(rules) > 200000:
                    rules.clear()
                    fails.clear()
            self.basic()
            if stop is not None and self.steps >= stop:
                break

    # ---- symbolic proof of one cycle (macro steps and earlier rules) ----
    def try_prove(self, sig, old, nloops):
        oq, od, oL, oR = old[:4]
        self.nproofs += 1
        nv = 0
        mins = []
        home = []
        L = []
        R = []
        curL, curR = self.L[-self.W:], self.R[-self.W:]
        for side, src, cur, dst in ((0, oL, curL, L), (1, oR, curR, R)):
            if len(src) != len(cur):
                raise ProofFail("window size")
            for i, (s, c) in enumerate(src):
                if c != INF and (c != cur[i][1] or c >= self.gen_thresh):
                    dst.append([s, Lin(0, {nv: 1})])
                    mins.append(1)
                    home.append((side, i))
                    nv += 1
                else:
                    dst.append([s, c])
        q, d = oq, od
        steps = Poly()
        mm = self.mm
        W = self.W
        level = 1

        def lower(e):
            """the least value of e under the current minimums (e int or Lin with nonnegative coefficients)"""
            if isinstance(e, int):
                return e
            lo = e.c
            for v, a in e.a.items():
                if a < 0:
                    raise ProofFail("neg coef")
                lo += a * mins[v]
            return lo

        def need_pos(e, extra):
            if isinstance(e, int):
                return e >= 1 + extra
            if lower(e) >= 1 + extra:
                return True
            if len(e.a) == 1:
                (v, a), = e.a.items()
                if a == 1:
                    mins[v] = 1 + extra - e.c
                    return True
            raise ProofFail("cannot bound")

        def addc(a, b):
            if isinstance(a, int) and isinstance(b, int):
                return a + b
            if isinstance(a, int):
                return b.add(a)
            return a.add(b)

        def push(stack, ns, cnt):
            o = stack[-1] if stack else (None, None)
            if o[0] == ns:
                if o[1] != INF:
                    o[1] = addc(o[1], cnt)
            else:
                stack.append([ns, cnt])

        def try_rule(r):
            """apply rule r to the symbolic window if it surely applies; None if it surely does not; ProofFail if
            undecided"""
            spec, consts, rmins, rdeltas, P, rhome, rlevel = r
            if rlevel >= self.max_level:
                return None
            wL, wR = L[-W:], R[-W:]
            xs = []
            for side, cur in ((0, wL), (1, wR)):
                sp = spec[side]
                cs = consts[side]
                if len(cur) != len(sp):
                    return None
                for i in range(len(cur)):
                    c = cur[i][1]
                    v = sp[i]
                    if v is None:
                        if isinstance(c, Lin):
                            if not c.a and c.c == cs[i]:
                                continue
                            return None
                        if c != cs[i]:
                            return None
                    else:
                        if c == INF:
                            return None
                        if isinstance(c, int):
                            if c < rmins[v]:
                                return None
                        elif lower(c) < rmins[v]:
                            return None     # not sure it applies: take plain macro steps instead
                        xs.append(c)
            dec = [v for v, dl in enumerate(rdeltas) if dl < 0]
            if not dec:
                return None
            if all(isinstance(x, int) for x in xs):
                k = min((xs[v] - rmins[v]) // (-rdeltas[v]) + 1 for v in dec)
            else:
                if len(dec) != 1 or rdeltas[dec[0]] != -1:
                    return None
                xb = xs[dec[0]]
                k = (xb.add(1 - rmins[dec[0]]) if isinstance(xb, Lin) else xb - rmins[dec[0]] + 1)
            # new lengths
            for v, dl in enumerate(rdeltas):
                side, i = rhome[v]
                tgt = (wL if side == 0 else wR)[i]
                if dl:
                    if isinstance(k, int):
                        tgt[1] = addc(xs[v], k * dl)
                    else:
                        base = xs[v] if isinstance(xs[v], Lin) else Lin(xs[v])
                        tgt[1] = base.add(k, dl)
                    if isinstance(tgt[1], Lin) and not tgt[1].a:
                        tgt[1] = tgt[1].c
            stp = sum_over_cycles(P, {v: Poly.of(xs[v]) for v in range(len(xs))}, rdeltas, k)
            return stp, rlevel

        n = 0
        while True:
            if n > 0 and q == oq and d == od and len(L) == len(oL) and len(R) == len(oR) and \
                    all(a[0] == b[0] for a, b in zip(L, oL)) and all(a[0] == b[0] for a, b in zip(R, oR)):
                break
            if n >= max(nloops, 1) * 4 + 50 or n > self.maxloop:
                raise ProofFail("too long")
            n += 1
            # an earlier rule, as the concrete run would try it
            sg = (q, d, tuple(r[0] for r in L[-W:]), tuple(r[0] for r in R[-W:]))
            applied = False
            for r in self.rules.get(sg, ()):
                res = try_rule(r)
                if res is not None:
                    stp, rl = res
                    steps = steps + stp
                    level = max(level, rl + 1)
                    applied = True
                    break
            if applied:
                continue
            stack, other = (R, L) if d == 1 else (L, R)
            if not stack:
                raise ProofFail("left the window")
            top = stack[-1]
            sym, cnt = top
            tr = mm.trans(q, sym, d)
            if tr[0] != "ok":
                raise ProofFail("halt in proof")
            _, ns, nq, nd, st = tr
            if nq == q and nd == d:
                if cnt == INF:
                    raise ProofFail("inf")
                stack.pop()
                steps = steps + Poly.of(cnt) * st
                push(other, ns, cnt)
                continue
            if cnt != INF:
                if isinstance(cnt, int):
                    if cnt == 1:
                        stack.pop()
                    else:
                        top[1] = cnt - 1
                else:
                    need_pos(cnt, 1)
                    top[1] = cnt.add(-1)
            push(other if nd == d else stack, ns, 1)
            q, d = nq, nd
            steps = steps + st
        deltas = [None] * nv
        spec = ([], [])
        vi = 0
        for side, fin, src in ((0, L, oL), (1, R, oR)):
            for i, (s, c) in enumerate(fin):
                if s != src[i][0]:
                    raise ProofFail("sym")
                if vi < nv and home[vi] == (side, i):
                    if isinstance(c, int) or len(c.a) != 1 or c.a.get(vi) != 1:
                        raise ProofFail("not own var")
                    deltas[vi] = c.c
                    spec[side].append(vi)
                    vi += 1
                else:
                    if (c.c if isinstance(c, Lin) and not c.a else c) != src[i][1]:
                        raise ProofFail("const changed")
                    spec[side].append(None)
        consts = ([c for _, c in oL], [c for _, c in oR])
        if level > 1:
            self.nrec += 1
        self.levels[level] = self.levels.get(level, 0) + 1
        return (spec, consts, mins, deltas, steps, home, level)



if __name__ == "__main__":
    import time
    import math
    sys.set_int_max_str_digits(0)
    m = sys.argv[1]
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    s = RecSim(m, k)
    t0 = time.time()
    if len(sys.argv) > 4 and sys.argv[3] == "--macro":
        s.run(int(float(sys.argv[4])))
    else:
        budget = float(sys.argv[3]) if len(sys.argv) > 3 else 60
        while s.halted is None and s.nonhalt is None and time.time() - t0 < budget:
            s.run(s.nmacro + 20000)
    print("macro", s.nmacro, "log10steps %.2f" % math.log10(max(s.steps, 1)), "rules", s.nrules, "levels", s.levels,
          "jumps", s.njumps, "%.0fs" % (time.time() - t0), "HALT" if s.halted else (s.nonhalt or "open"))
