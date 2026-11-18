"""A recursive rule accelerator for two-symbol machines (a halt hunter).

Like rleaccel.py, the tape is run-length coded in blocks of K cells, a run the head crosses without changing state
is crossed in one chain step, and when the same local shape comes back, one cycle is replayed symbolically with the
changed run lengths as variables.  Three things are new:

  * a replay may itself use rules proved earlier, including a translation rule applied a symbolic number of times
    (the number is read off the one count that runs it down), so proved rules nest;
  * a rule's output counts may be any affine function of its variables (x -> 2x + 3, (a, b) -> (a + b, 2)), not only
    a translation; such a rule is applied once per use, in O(1) whatever the numbers;
  * step counts are polynomials in the variables (exact rationals that evaluate to integers), so the step count of a
    halt found deep in a nested run is exact.

A rule is made only from a symbolic replay, every assumption of which is a linear inequality on the variables
recorded with the rule and checked whenever the rule is applied, so nothing is guessed.  A rule pattern is the part
of the tape the replay touched: blocks deeper on either side are untouched and can be anything.

Trust level: trusted computation (Python), tested against direct runs (tools/tests/test_recaccel.py).

usage: python3 tools/py/bbtools/recaccel.py MACHINE [K] [MAX_ACTIONS] [MAX_SECONDS]
"""
import sys
import time
from fractions import Fraction

INF = -1


# ---------------------------------------------------------------- the macro machine
def parse(m):
    rows = m.split("_")
    T = {}
    for qi, row in enumerate(rows):
        for b in (0, 1):
            t = row[3 * b:3 * b + 3]
            if t[0] == "-" or ord(t[2]) - 65 >= len(rows):
                T[(qi, b)] = None
            else:
                T[(qi, b)] = (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


class Macro:
    def __init__(self, m, k):
        self.T = parse(m)
        self.k = k
        self.memo = {}

    def trans(self, q, sym, d):
        """The head enters a k-block moving in direction d.  ('ok', newsym, q, d, steps) | ('halt', steps, cells,
        q, pos) | ('loop',)"""
        key = (q, sym, d)
        r = self.memo.get(key)
        if r is not None:
            return r
        k = self.k
        cells = [(sym >> (k - 1 - i)) & 1 for i in range(k)]
        pos = 0 if d == 1 else k - 1
        steps = 0
        seen = set()
        while True:
            st = (q, pos, tuple(cells))
            if st in seen:
                r = ("loop",)
                break
            seen.add(st)
            t = self.T[(q, cells[pos])]
            if t is None:
                r = ("halt", steps + 1, tuple(cells), q, pos)
                break
            cells[pos] = t[0]
            pos += t[1]
            q = t[2]
            steps += 1
            if pos < 0 or pos >= k:
                ns = 0
                for c in cells:
                    ns = ns * 2 + c
                r = ("ok", ns, q, 1 if pos >= k else -1, steps)
                break
        self.memo[key] = r
        return r


# ---------------------------------------------------------------- expressions
class Lin:
    """c + sum a[v] x_v, integer coefficients; used for counts."""
    __slots__ = ("c", "a")

    def __init__(self, c=0, a=None):
        self.c = c
        self.a = a if a is not None else {}

    @staticmethod
    def var(v):
        return Lin(0, {v: 1})

    def is_const(self):
        return not self.a

    def plus(self, o, mul=1):
        if isinstance(o, int):
            return Lin(self.c + o * mul, self.a)
        a = dict(self.a)
        for v, k in o.a.items():
            n = a.get(v, 0) + k * mul
            if n:
                a[v] = n
            else:
                a.pop(v, None)
        return Lin(self.c + o.c * mul, a)

    def scale(self, k):
        if k == 0:
            return Lin(0)
        return Lin(self.c * k, {v: a * k for v, a in self.a.items()})

    def ev(self, xs):
        s = self.c
        for v, a in self.a.items():
            s += a * xs[v]
        return s

    def subst(self, env):
        """env: v -> Lin or int"""
        r = Lin(self.c)
        for v, a in self.a.items():
            r = r.plus(env[v], a)
        return r

    def key(self):
        return (self.c, tuple(sorted(self.a.items())))

    def __eq__(self, o):
        return isinstance(o, Lin) and self.key() == o.key()

    def __hash__(self):
        return hash(self.key())

    def __repr__(self):
        s = [str(self.c)] if self.c or not self.a else []
        for v, a in sorted(self.a.items()):
            s.append(("%d*" % a if a != 1 else "") + "x%d" % v)
        return "+".join(s)


def norm(e):
    """Lin with no variables -> int"""
    if isinstance(e, Lin) and not e.a:
        return e.c
    return e


def as_lin(e):
    return e if isinstance(e, Lin) else Lin(e)


class Poly:
    """sum coeff * prod x_v over monomials (sorted tuples of variable ids, with repetition); Fraction coefficients.
    Used for step counts."""
    __slots__ = ("t",)

    def __init__(self, t=None):
        self.t = t if t is not None else {}

    @staticmethod
    def const(c):
        return Poly({(): Fraction(c)} if c else {})

    @staticmethod
    def lin(e):
        if isinstance(e, int):
            return Poly.const(e)
        t = {}
        if e.c:
            t[()] = Fraction(e.c)
        for v, a in e.a.items():
            t[(v,)] = Fraction(a)
        return Poly(t)

    def add(self, o, mul=1):
        t = dict(self.t)
        for m, c in o.t.items():
            n = t.get(m, 0) + c * mul
            if n:
                t[m] = n
            else:
                t.pop(m, None)
        return Poly(t)

    def mul(self, o):
        t = {}
        for m1, c1 in self.t.items():
            for m2, c2 in o.t.items():
                m = tuple(sorted(m1 + m2))
                n = t.get(m, 0) + c1 * c2
                if n:
                    t[m] = n
                else:
                    t.pop(m, None)
        return Poly(t)

    def ev(self, xs):
        s = Fraction(0)
        for m, c in self.t.items():
            p = c
            for v in m:
                p *= xs[v]
            s += p
        return s

    def subst(self, env):
        """env: v -> Poly"""
        r = Poly()
        cache = {}
        for m, c in self.t.items():
            p = Poly.const(1)
            for v in m:
                p = p.mul(env[v])
            r = r.add(p, c)
        return r

    def degree_in(self, v):
        return max((m.count(v) for m in self.t), default=0)


# sum_{i=0}^{n-1} i^k as a polynomial in n, for small k (Faulhaber via the recurrence on binomials)
_FAUL = {}


def faulhaber(k):
    """coefficients c[j] with sum_{i<n} i^k = sum_j c[j] n^j"""
    if k in _FAUL:
        return _FAUL[k]
    from math import comb
    # (n)^(k+1) = sum_{j=0}^{k} C(k+1, j) S_j(n)
    c = [Fraction(0)] * (k + 2)
    c[k + 1] = Fraction(1)
    for j in range(k):
        cj = faulhaber(j)
        for t, x in enumerate(cj):
            c[t] -= comb(k + 1, j) * x
    c = [x / (k + 1) for x in c]
    _FAUL[k] = c
    return c


IVAR = -1  # the iteration index inside a sum


def sum_over_i(P, n):
    """P: Poly that may contain IVAR; returns sum_{i=0}^{n-1} P as Poly, n a Poly (no IVAR)"""
    groups = {}
    for m, c in P.t.items():
        k = m.count(IVAR)
        rest = tuple(v for v in m if v != IVAR)
        groups.setdefault(k, {})[rest] = groups.setdefault(k, {}).get(rest, 0) + c
    r = Poly()
    npow = [Poly.const(1)]
    for k, t in groups.items():
        cf = faulhaber(k)
        S = Poly()
        for j, x in enumerate(cf):
            if x:
                while len(npow) <= j:
                    npow.append(npow[-1].mul(n))
                S = S.add(npow[j], x)
        r = r.add(S.mul(Poly(t)))
    return r


class ProofFail(Exception):
    pass


# ---------------------------------------------------------------- rules
class Rule:
    """pat[side] = list (bottom to top) of (sym, kind, val): kind 'c' const count val (int or INF), 'v' variable val.
    reqs: Lins in the variables that must be >= 0.  out[side]: list (bottom to top) of (sym, count Lin/int/INF), same
    length and symbols as pat (a cycle).  steps: Poly.  trans: deltas (list) when every variable moves by a constant
    and nothing else changes, else None."""
    __slots__ = ("q", "d", "pat", "nv", "reqs", "out", "steps", "deltas", "uses", "depth", "deg")

    def __init__(self, q, d, pat, nv, reqs, out, steps, depth):
        self.q, self.d, self.pat, self.nv, self.reqs, self.out, self.steps = q, d, pat, nv, reqs, out, steps
        self.uses = 0
        self.depth = depth
        self.deltas = None
        deltas = [None] * nv
        ok = True
        for side in (0, 1):
            for (s, kd, v), (s2, e) in zip(pat[side], out[side]):
                if kd == "c":
                    if not (e == v or (isinstance(e, Lin) and e.is_const() and e.c == v)):
                        ok = False
                else:
                    e = as_lin(e)
                    if len(e.a) == 1 and e.a.get(v) == 1:
                        deltas[v] = e.c
                    else:
                        ok = False
        if ok and all(x is not None for x in deltas):
            self.deltas = deltas
        self.deg = max((len(m) for m in steps.t), default=0)


def side_match(stack, pat):
    """bind pattern (bottom->top) to the top of stack; returns list of bound counts per var position or None"""
    n = len(pat)
    if len(stack) < n:
        return None
    base = len(stack) - n
    binds = []
    for j, (s, kd, v) in enumerate(pat):
        blk = stack[base + j]
        if blk[0] != s:
            return None
        c = blk[1]
        if kd == "c":
            if v == INF:
                if c != INF:
                    return None
            else:
                if c == INF:
                    return None
                c = norm(c)
                if not isinstance(c, int) or c != v:
                    return None
        else:
            if c == INF:
                return None
            binds.append((v, c))
    return binds


# ---------------------------------------------------------------- the simulator
class Sim:
    def __init__(self, m, k=1, W=10, maxloop=3000, gen_thresh=3, maxdepth=6, verbose=False, same_period=True):
        self.m = m
        self.mm = Macro(m, k)
        self.k = k
        self.L = [[0, INF]]
        self.R = [[0, INF]]
        self.q = 0
        self.d = 1
        self.steps = 0
        self.nact = 0
        self.halted = None
        self.nonhalt = None
        self.past = {}
        self.rules = {}  # (q, d, topL sym, topR sym) -> [Rule]
        self.fails = {}
        self.W = W
        self.maxloop = maxloop
        self.gen_thresh = gen_thresh
        self.maxdepth = maxdepth
        self.verbose = verbose
        self.nrules = 0
        self.napply = 0
        self.nproofs = 0
        self.proofcost = 0
        self.haltinfo = None
        self.same_period = same_period

    # ------------------------------------------------ one basic macro step, concrete or symbolic
    def _basic(self, L, R, q, d, symbolic, ctx):
        """mutates L, R; returns (q, d, steps as int or Poly) or raises/flags.  ctx: proof context (reqs, touch) or
        None"""
        if d == 1:
            stack, other, si, oi = R, L, 1, 0
        else:
            stack, other, si, oi = L, R, 0, 1
        if not stack:
            raise ProofFail("window")
        if ctx is not None:
            ctx.touch(si, len(stack) - 1)
        top = stack[-1]
        sym, cnt = top
        tr = self.mm.trans(q, sym, d)
        if tr[0] != "ok":
            if not symbolic:
                if tr[0] == "halt":
                    self.halted = tr
                    return q, d, tr[1]
                self.nonhalt = "in-block loop"
                return q, d, 0
            raise ProofFail("halt/loop in proof")
        _, ns, nq, nd, st = tr
        if nq == q and nd == d:
            if cnt == INF:
                if not symbolic:
                    self.nonhalt = "runs off to infinity"
                    return q, d, 0
                raise ProofFail("inf chain")
            stack.pop()
            self._push(other, ns, cnt, ctx, oi)
            if isinstance(cnt, int):
                return q, d, cnt * st
            return q, d, Poly.lin(cnt).mul(Poly.const(st)) if symbolic else cnt * st
        if cnt != INF:
            if isinstance(cnt, int):
                if cnt == 1:
                    stack.pop()
                else:
                    top[1] = cnt - 1
            else:
                ctx.require(cnt.plus(-1))  # cnt >= 1
                nc = norm(cnt.plus(-1))
                if isinstance(nc, int):
                    if nc == 0:
                        stack.pop()
                    else:
                        top[1] = nc
                else:
                    ctx.require(nc.plus(-1))  # keep the block: cnt - 1 >= 1
                    top[1] = nc
        tgt, ti = (other, oi) if nd == d else (stack, si)
        self._push(tgt, ns, 1, ctx, ti)
        return nq, nd, st

    @staticmethod
    def _push(stack, ns, cnt, ctx, side):
        if not stack:
            raise ProofFail("window")
        if ctx is not None:
            ctx.touch(side, len(stack) - 1)
        o = stack[-1]
        if o[0] == ns:
            if o[1] != INF:
                if isinstance(o[1], int) and isinstance(cnt, int):
                    o[1] += cnt
                else:
                    o[1] = norm(as_lin(o[1]).plus(cnt))
        else:
            stack.append([ns, cnt])

    # ------------------------------------------------ rule application
    def _find_rule(self, L, R, q, d):
        key = (q, d, L[-1][0] if L else None, R[-1][0] if R else None)
        return self.rules.get(key, ())

    def _apply_concrete(self, r):
        bl = side_match(self.L, r.pat[0])
        if bl is None:
            return False
        br = side_match(self.R, r.pat[1])
        if br is None:
            return False
        xs = [0] * r.nv
        for v, c in bl + br:
            xs[v] = c
        for e in r.reqs:
            if e.ev(xs) < 0:
                return False
        if r.deltas is not None:
            n = None
            for e in r.reqs:
                rd = sum(a * r.deltas[v] for v, a in e.a.items())
                if rd < 0:
                    nn = e.ev(xs) // (-rd) + 1
                    if n is None or nn < n:
                        n = nn
            if n is None:
                self.nonhalt = "a proved rule repeats forever"
                return True
            # steps: sum_{i<n} P(x + i delta)
            env = {v: Poly({(): Fraction(xs[v]), (IVAR,): Fraction(r.deltas[v])} if r.deltas[v] else
                           {(): Fraction(xs[v])}) for v in range(r.nv)}
            P = r.steps.subst(env)
            st = sum_over_i(P, Poly.const(n)).ev({})
            newx = [xs[v] + n * r.deltas[v] for v in range(r.nv)]
        else:
            n = 1
            st = r.steps.ev(xs)
            newx = None
        assert st.denominator == 1, st
        self._write_out(self.L, self.R, r, xs if newx is None else newx, newx is not None)
        self.steps += int(st)
        r.uses += 1
        self.napply += 1
        return True

    @staticmethod
    def _write_out(L, R, r, xs, trans):
        for side, stack in ((0, L), (1, R)):
            pat = r.pat[side]
            n = len(pat)
            base = len(stack) - n
            del stack[base:]
            for j, (s, kd, v) in enumerate(pat):
                if trans:
                    val = v if kd == "c" else xs[v]
                else:
                    e = r.out[side][j][1]
                    val = e if (e == INF or isinstance(e, int)) else e.ev(xs)
                if val == 0:
                    continue  # cannot happen when reqs hold; kept safe
                if stack and stack[-1][0] == s and stack[-1][1] != INF and val != INF:
                    stack[-1][1] += val
                elif stack and stack[-1][0] == s and stack[-1][1] == INF:
                    pass
                else:
                    stack.append([s, val])

    def _apply_symbolic(self, r, L, R, ctx):
        """apply rule r (once if affine, as many times as it runs if a translation) on symbolic stacks"""
        bl = side_match(L, r.pat[0])
        if bl is None:
            return None
        br = side_match(R, r.pat[1])
        if br is None:
            return None
        env = {}
        for v, c in bl + br:
            env[v] = as_lin(c)
        ctx.touch(0, len(L) - len(r.pat[0]))
        ctx.touch(1, len(R) - len(r.pat[1]))
        subreqs = [norm(e.subst(env)) for e in r.reqs]
        for e in subreqs:
            if isinstance(e, int) and e < 0:
                return None
        if r.deltas is not None:
            # n = min over decreasing reqs of floor(e / k) + 1 ; must be exact and unique
            cands = []
            for e0, e in zip(r.reqs, subreqs):
                rd = sum(a * r.deltas[v] for v, a in e0.a.items())
                if rd < 0:
                    cands.append((as_lin(e), -rd))
            if not cands:
                raise ProofFail("infinite inner rule")
            best = None
            for e, k in cands:
                if any(a % k for a in e.a.values()) or e.c % k:
                    if e.is_const():
                        nn = Lin(e.c // k + 1)
                    else:
                        raise ProofFail("inexact division")
                else:
                    nn = Lin(e.c // k + 1, {v: a // k for v, a in e.a.items()})
                if best is None:
                    best = nn
                else:
                    diff = norm(nn.plus(best, -1))
                    if not isinstance(diff, int):
                        raise ProofFail("min undecided")
                    if diff < 0:
                        best = nn
            n = norm(best)
            if isinstance(n, int) and n <= 0:
                return None
            for e in subreqs:
                if not isinstance(e, int):
                    ctx.require(e)
            if isinstance(n, Lin):
                ctx.require(n.plus(-1))
            # new values and steps
            newenv = {v: norm(as_lin(env[v]).plus(as_lin(n).scale(r.deltas[v]))) for v in range(r.nv)}
            penv = {v: Poly.lin(env[v]).add(Poly({(IVAR,): Fraction(r.deltas[v])})) if r.deltas[v] else
                    Poly.lin(env[v]) for v in range(r.nv)}
            P = r.steps.subst(penv)
            st = sum_over_i(P, Poly.lin(n))
            self._write_sym(L, R, r, newenv, True, ctx)
        else:
            for e in subreqs:
                if not isinstance(e, int):
                    ctx.require(e)
            penv = {v: Poly.lin(env[v]) for v in range(r.nv)}
            st = r.steps.subst(penv)
            outenv = {}
            self._write_sym(L, R, r, env, False, ctx)
        return st

    def _write_sym(self, L, R, r, env, trans, ctx):
        for side, stack in ((0, L), (1, R)):
            pat = r.pat[side]
            n = len(pat)
            base = len(stack) - n
            del stack[base:]
            for j, (s, kd, v) in enumerate(pat):
                if trans:
                    val = v if kd == "c" else env[v]
                else:
                    e = r.out[side][j][1]
                    val = e if (e == INF or isinstance(e, int)) else norm(e.subst(env))
                if isinstance(val, int) and val == 0:
                    continue
                if isinstance(val, Lin):
                    ctx.require(val.plus(-1))
                if stack and stack[-1][0] == s and stack[-1][1] != INF and val != INF:
                    stack[-1][1] = norm(as_lin(stack[-1][1]).plus(val))
                elif stack and stack[-1][0] == s and stack[-1][1] == INF:
                    pass
                else:
                    stack.append([s, val])

    # ------------------------------------------------ proofs
    def try_prove(self, old, nact):
        oq, od, oL, oR = old[0], old[1], old[2], old[3]
        self.nproofs += 1
        nv = 0
        L, R = [], []
        homes = []
        curL, curR = self.L[-self.W:], self.R[-self.W:]
        if len(curL) != len(oL) or len(curR) != len(oR):
            raise ProofFail("window length")
        orig = ([], [])
        for side, src, cur, dst in ((0, oL, curL, L), (1, oR, curR, R)):
            for i, (s, c) in enumerate(src):
                if cur[i][0] != s:
                    raise ProofFail("sym")
                if c != INF and (c != cur[i][1] or c >= self.gen_thresh):
                    dst.append([s, Lin.var(nv)])
                    orig[side].append((s, "v", nv))
                    nv += 1
                else:
                    dst.append([s, c])
                    orig[side].append((s, "c", c))
        ctx = Ctx(len(L), len(R))
        for v in range(nv):
            ctx.require(Lin(-1, {v: 1}))
        q, d = oq, od
        steps = Poly()
        depth = 0
        for _ in range(nact):
            done = False
            for r in self._find_rule(L, R, q, d):
                st = self._apply_symbolic(r, L, R, ctx)
                if st is not None:
                    steps = steps.add(st)
                    depth = max(depth, r.depth + 1)
                    done = True
                    break
            if done:
                continue
            q, d, st = self._basic(L, R, q, d, True, ctx)
            steps = steps.add(st if isinstance(st, Poly) else Poly.const(st))
        if depth > self.maxdepth:
            raise ProofFail("too deep")
        if q != oq or d != od:
            raise ProofFail("state")
        # touched region: from ctx.low[side] to top; below untouched and identical
        pat = ([], [])
        out = ([], [])
        for side, stack, src in ((0, L, orig[0]), (1, R, orig[1])):
            lo = ctx.low[side]
            if len(stack) < lo:
                raise ProofFail("shrank")
            fin = stack[lo:]
            if len(fin) != len(src) - lo:
                raise ProofFail("shape")
            for j, (s, kd, v) in enumerate(src[lo:]):
                if fin[j][0] != s:
                    raise ProofFail("sym changed")
                pat[side].append((s, kd, v))
                out[side].append((s, fin[j][1]))
        # renumber vars to those in the pattern; vars below the touched region must not appear
        used = sorted({v for side in (0, 1) for (s, kd, v) in pat[side] if kd == "v"})
        ren = {v: i for i, v in enumerate(used)}
        allv = set(used)

        def rl(e):
            if isinstance(e, Lin):
                if any(v not in allv for v in e.a):
                    raise ProofFail("var outside")
                return Lin(e.c, {ren[v]: a for v, a in e.a.items()})
            return e
        pat2 = tuple([(s, kd, ren[v] if kd == "v" else v) for (s, kd, v) in pat[side]] for side in (0, 1))
        out2 = tuple([(s, rl(e)) for (s, e) in out[side]] for side in (0, 1))
        reqs = []
        seen = set()
        for e in ctx.reqs:
            if len(e.a) == 1 and e.c == -1 and next(iter(e.a.values())) == 1 and next(iter(e.a)) not in allv:
                continue  # the positivity of a block the replay never touched
            e2 = rl(e)
            k = e2.key()
            if k not in seen:
                seen.add(k)
                reqs.append(e2)
        st2 = Poly()
        for m, c in steps.t.items():
            if any(v not in allv for v in m):
                raise ProofFail("var outside (steps)")
            st2.t[tuple(sorted(ren[v] for v in m))] = c
        # a rule must change something
        r = Rule(oq, od, pat2, len(used), reqs, out2, st2, depth)
        if r.deltas is not None and all(x == 0 for x in r.deltas):
            raise ProofFail("identity")
        return r

    def add_rule(self, r):
        key = (r.q, r.d, r.pat[0][-1][0] if r.pat[0] else None, r.pat[1][-1][0] if r.pat[1] else None)
        self.rules.setdefault(key, []).insert(0, r)
        self.nrules += 1

    # ------------------------------------------------ main loop
    def sig(self):
        W = self.W
        return (self.q, self.d, tuple(r[0] for r in self.L[-W:]), tuple(r[0] for r in self.R[-W:]))

    def run(self, max_act, max_sec=None, stop_steps=None):
        t0 = time.time()
        past = self.past
        while self.nact < max_act and self.halted is None and self.nonhalt is None:
            self.nact += 1
            if max_sec is not None and (self.nact & 1023) == 0 and time.time() - t0 > max_sec:
                break
            applied = False
            for r in self._find_rule(self.L, self.R, self.q, self.d):
                if self._apply_concrete(r):
                    applied = True
                    break
            if not applied:
                sig = self.sig()
                old = past.get(sig)
                if old is not None:
                    na = self.nact - old[4]
                    if ((na == old[5] or not self.same_period) and na <= self.maxloop and self.fails.get(sig, 0) < 4
                            and self.proofcost <= 4 * self.nact + 200000):
                        self.proofcost += na
                        try:
                            r = self.try_prove(old, na)
                            self.add_rule(r)
                            if self.verbose:
                                print("rule", self.nrules, "depth", r.depth, "trans" if r.deltas else "affine",
                                      r.pat, r.out, r.reqs, file=sys.stderr)
                            past.clear()
                            if self._apply_concrete(r):
                                continue
                        except ProofFail as e:
                            self.fails[sig] = self.fails.get(sig, 0) + 1
                past[sig] = (self.q, self.d, [b[:] for b in self.L[-self.W:]], [b[:] for b in self.R[-self.W:]],
                             self.nact, self.nact - old[4] if old is not None else 0)
                if len(past) > 50000:
                    past.clear()
                self.q, self.d, st = self._basic(self.L, self.R, self.q, self.d, False, None)
                self.steps += st
            else:
                past.clear()
            if stop_steps is not None and self.steps >= stop_steps:
                break
        if len(self.rules) > 100000:
            self.rules.clear()

    # ------------------------------------------------ display
    def tape_str(self, maxlen=400):
        k = self.k

        def w(s):
            return format(s, "0%db" % k)

        def c(x):
            if x == INF:
                return "inf"
            if isinstance(x, int) and x > 10 ** 12:
                return "~1e%d" % (len(str(x)) - 1)
            return str(x)
        l = " ".join("%s^%s" % (w(s), c(n)) for s, n in self.L[1:])
        r = " ".join("%s^%s" % (w(s), c(n)) for s, n in reversed(self.R[1:]))
        st = "ABCDEFGH"[self.q]
        mid = (" %s> " % st) if self.d == 1 else (" <%s " % st)
        s = l + mid + r
        return s if len(s) <= maxlen else s[:maxlen // 2] + " ... " + s[-maxlen // 2:]

    def width(self):
        return self.k * (sum(c for _, c in self.L[1:]) + sum(c for _, c in self.R[1:]))


class Ctx:
    """proof context: requirements (Lin >= 0) and the lowest stack index touched on each side"""

    def __init__(self, nl, nr):
        self.reqs = []
        self.low = [nl, nr]

    def touch(self, side, idx):
        if idx < self.low[side]:
            self.low[side] = max(idx, 0)

    def require(self, e):
        e = norm(e)
        if isinstance(e, int):
            if e < 0:
                raise ProofFail("false requirement")
            return
        self.reqs.append(e)


def digits(n):
    n = int(n)
    return len(str(n)) if n < 10 ** 4000 else int(n.bit_length() * 0.30103) + 1


def hunt(m, k, max_act, max_sec, verbose=False, W=10):
    s = Sim(m, k, W=W, verbose=verbose)
    s.run(max_act, max_sec)
    return s


if __name__ == "__main__":
    sys.set_int_max_str_digits(0) if hasattr(sys, "set_int_max_str_digits") else None
    m = sys.argv[1]
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    mx = int(float(sys.argv[3])) if len(sys.argv) > 3 else 10 ** 6
    sec = float(sys.argv[4]) if len(sys.argv) > 4 else 60
    t0 = time.time()
    s = Sim(m, k, verbose="-v" in sys.argv)
    s.run(mx, sec)
    print("actions %d, steps ~1e%d, rules %d, applications %d, %.1fs" % (
        s.nact, digits(s.steps) - 1, s.nrules, s.napply, time.time() - t0))
    if s.halted:
        print("HALTED after", s.steps, "steps")
    elif s.nonhalt:
        print("DOES NOT HALT:", s.nonhalt)
    else:
        print("no halt in the first %d-digit number of steps" % digits(s.steps))
    print(s.tape_str())
