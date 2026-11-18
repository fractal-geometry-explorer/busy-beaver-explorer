"""A region-memo accelerator for counters that live at the left end of the tape (odometers, nested counters).

The tape is run-length coded in blocks of K cells (as in rleaccel.py and recaccel.py).  A *region* is the part of
the tape left of some block boundary; E(region) runs the machine until the head first touches the block right of
the region, and returns the region as it is then (the head leaves it on the right, moving right).  E is computed
recursively: inside a region, while the head is left of the region's last block, E of the smaller region (the
region without its last block) is applied; otherwise one ordinary macro step touches the last block.

E is memoized by the region's *pattern*: the block symbols, and each count either exact (below SMALL) or "big".  The
first time a pattern is seen again, E is computed symbolically for it, with every big count a variable: the result
is the region after E as counts that are affine in the variables, the step count as a polynomial, and the linear
inequalities the symbolic run assumed.  Applying it to a region of that pattern checks the inequalities and writes
the new region, at a cost independent of the numbers.  For an odometer with digits at the left end, E of the region
of the lowest j digits is one carry out of digit j, so after a short start each level is computed once per digit
pattern and a run of b^j visits costs about j applications.

Every entry is a symbolic run of the machine; when an entry's inequalities fail, or no entry can be made, the region
is run by the same recursion with concrete numbers.  So the run is exact (steps included) whatever the machine;
only the speed depends on its structure.

Trust level: trusted computation (Python), tested against direct runs (tools/tests/test_regaccel.py).

usage: python3 tools/py/bbtools/regaccel.py MACHINE [K] [SECONDS] [mirror]
"""
import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from recaccel import Macro, Lin, Poly, norm, as_lin, INF, ProofFail, IVAR, sum_over_i  # noqa: E402

FAIL = object()


class Halt(Exception):
    pass


class NonHalt(Exception):
    pass


class Budget(Exception):
    pass


class SymBudget(Exception):
    """the symbolic work of one outermost build ran out; only the outermost build records a failure"""


class Ctx:
    """requirements e >= 0, kept as the strongest constant for each linear part"""
    __slots__ = ("req", "steps", "ops")

    def __init__(self):
        self.req = {}
        self.steps = Poly()
        self.ops = 0

    def require(self, e):
        e = norm(e)
        if isinstance(e, int):
            if e < 0:
                raise ProofFail("false")
            return
        k = tuple(sorted(e.a.items()))
        o = self.req.get(k)
        if o is None or e.c < o.c:
            self.req[k] = e

    @property
    def reqs(self):
        return list(self.req.values())


class Entry:
    __slots__ = ("nv", "reqs", "outL", "q", "steps", "uses", "bdelta")

    def __init__(self, nv, reqs, outL, q, steps):
        self.nv, self.reqs, self.outL, self.q, self.steps = nv, reqs, outL, q, steps
        self.uses = 0


def mirror(m):
    rows = m.split("_")
    out = []
    for row in rows:
        r = ""
        for b in range(2):
            t = row[3 * b:3 * b + 3]
            if t[0] == "-" or ord(t[2]) - 65 >= len(rows):
                r += t
            else:
                r += t[0] + ("L" if t[1] == "R" else "R") + t[2]
        out.append(r)
    return "_".join(out)


class Sim:
    def __init__(self, m, k=1, small=4, maxinner=500, maxbuild=30000):
        self.m = m
        self.mm = Macro(m, k)
        self.k = k
        self.small = small
        self.maxinner = maxinner
        self.maxbuild = maxbuild
        self.L = [[0, INF]]
        self.R = [[0, INF]]
        self.q = 0
        self.d = 1
        self.steps = 0
        self.memo = {}
        self.seen = set()
        self.halted = None
        self.nonhalt = None
        self.napply = 0
        self.nbuilt = 0
        self.nfail = 0
        self.nbasic = 0
        self.deadline = None
        self.symops = 0
        self.building = 0
        self.tick = 0
        self.memsize = 0
        self.maxmem = 4000000
        self.nclear = 0
        self.ncycles = 0

    # ---------------------------------------------------------------- patterns
    def cls(self, c):
        if c == INF:
            return "I"
        if isinstance(c, Lin):
            if c.a:
                return "B"
            c = c.c
        return c if c < self.small else "B"

    def key(self, L, R, b, q, d):
        cls = self.cls
        bd = R[b - 1]
        return (q, d, bd[0], bd[1] == INF, tuple([(s, cls(c)) for s, c in L]),
                tuple([(s, cls(c)) for s, c in R[b:]]))

    # ---------------------------------------------------------------- one macro step inside a region
    def push(self, stack, ns, cnt, R, b):
        o = stack[-1]
        if o[0] == ns:
            if o[1] != INF:
                if isinstance(o[1], int) and isinstance(cnt, int):
                    o[1] += cnt
                else:
                    o[1] = norm(as_lin(o[1]).plus(cnt))
        else:
            stack.append([ns, cnt])

    def basic(self, L, R, b, q, d, ctx):
        if d == 1:
            stack, other = R, L
        else:
            stack, other = L, R
        top = stack[-1]
        sym, cnt = top
        tr = self.mm.trans(q, sym, d)
        if tr[0] != "ok":
            if ctx is not None:
                raise ProofFail("halt in proof")
            if tr[0] == "halt":
                self.steps += tr[1]
                self.halted = tr
                raise Halt()
            self.nonhalt = "in-block loop"
            raise NonHalt()
        _, ns, nq, nd, st = tr
        if ctx is None:
            self.nbasic += 1
        else:
            ctx.ops += 1
        if nq == q and nd == d:
            if cnt == INF:
                if ctx is not None:
                    raise ProofFail("inf")
                self.nonhalt = "runs off to infinity"
                raise NonHalt()
            stack.pop()
            self.push(other, ns, cnt, R, b)
            if ctx is None:
                self.steps += cnt * st
            elif isinstance(cnt, int):
                ctx.steps = ctx.steps.add(Poly.const(cnt * st))
            else:
                ctx.steps = ctx.steps.add(Poly.lin(cnt), st)
            return q, d
        if cnt != INF:
            if isinstance(cnt, int):
                if cnt == 1:
                    stack.pop()
                else:
                    top[1] = cnt - 1
            else:
                ctx.require(cnt.plus(-1))
                nc = norm(cnt.plus(-1))
                if isinstance(nc, int):
                    if nc == 0:
                        stack.pop()
                    else:
                        top[1] = nc
                else:
                    ctx.require(nc.plus(-1))
                    top[1] = nc
        self.push(other if nd == d else stack, ns, 1, R, b)
        if ctx is None:
            self.steps += st
        else:
            ctx.steps = ctx.steps.add(Poly.const(st))
        return nq, nd

    # ---------------------------------------------------------------- E
    def E(self, L, R, b, q, d, ctx):
        """run until the head moves right off R[b:] (len(R) == b, d == 1); returns the state then"""
        key = self.key(L, R, b, q, d)
        ent = self.memo.get(key)
        if ent is None:
            if ctx is not None or key in self.seen:
                ent = self.build(L, R, b, q, d)
                self.memsize += len(key[4]) + len(key[5]) + (0 if ent is FAIL else len(ent.outL) + len(ent.reqs))
                if self.memsize > self.maxmem:
                    self.memo.clear()
                    self.seen.clear()
                    self.memsize = 0
                    self.nclear += 1
                self.memo[key] = ent
            else:
                self.seen.add(key)
                self.memsize += len(key[4]) + len(key[5])
        if ent is not None and ent is not FAIL:
            r = self.apply(ent, L, R, b, ctx)
            if r is not None:
                return r
        return self.E_raw(L, R, b, q, d, ctx)

    def E_raw(self, L, R, b, q, d, ctx):
        it = 0
        snaps = {}
        dead = set()
        while True:
            nR = len(R) - b
            if nR == 0 and d == 1:
                return q
            it += 1
            if ctx is not None:
                self.symops += 1
                if it > self.maxinner:
                    raise ProofFail("inner loop")
                if self.symops > self.maxbuild:
                    raise SymBudget()
            else:
                self.tick += 1
                if self.deadline is not None and (self.tick & 1023) == 0 and time.time() > self.deadline:
                    raise Budget()
            if it >= 3:
                sk = (q, d, tuple([x[0] for x in L]), tuple([x[0] for x in R[b:]]))
                old = snaps.get(sk)
                cur = [x[1] for x in L] + [x[1] for x in R[b:]]
                if old is not None and sk not in dead:
                    done = self.try_cycle(L, R, b, q, d, ctx, old, cur, it, sk)
                    if done:
                        snaps.clear()
                        continue
                    dead.add(sk)
                snaps[sk] = (it, cur)
            if nR >= 2 or (nR == 1 and d == -1):
                q = self.E(L, R, b + 1, q, d, ctx)
                d = 1
            else:
                q, d = self.basic(L, R, b, q, d, ctx)

    def step_once(self, L, R, b, q, d, ctx):
        nR = len(R) - b
        if nR == 0 and d == 1:
            raise ProofFail("left region in cycle")
        if nR >= 2 or (nR == 1 and d == -1):
            return self.E(L, R, b + 1, q, d, ctx), 1
        return self.basic(L, R, b, q, d, ctx)

    def try_cycle(self, L, R, b, q, d, ctx, old, cur, it, sk):
        """the region came back to the same symbols after it - old[0] iterations: if every count moved by a
        constant, prove that segment for all counts (fresh variables) and apply it as many times as it runs"""
        i0, prev = old
        deltas = []
        for a, c in zip(prev, cur):
            if a == INF or c == INF:
                if not (a == INF and c == INF):
                    return False
                deltas.append(0)
                continue
            dl = norm(as_lin(c).plus(as_lin(a), -1))
            if not isinstance(dl, int):
                return False
            deltas.append(dl)
        if not any(deltas):
            return False
        nsteps = it - i0
        # abstract start: every count that moves, or is big, is a variable
        vpos = []
        aL, aR = [], []
        n_l = len(L)
        for idx, c in enumerate(cur):
            s = (L[idx] if idx < n_l else R[b + idx - n_l])[0]
            dst = aL if idx < n_l else aR
            if c != INF and (deltas[idx] != 0 or self.cls(c) == "B"):
                dst.append([s, Lin.var(len(vpos))])
                vpos.append(idx)
            else:
                dst.append([s, c if c == INF else norm(c)])
                if c != INF and not isinstance(norm(c), int):
                    return False
        BV = len(vpos)
        bd = R[b - 1]
        aR.insert(0, [bd[0], INF if bd[1] == INF else Lin.var(BV)])
        sub = Ctx()
        for v in range(len(vpos)):
            sub.require(Lin(-1, {v: 1}))
        outer = self.building == 0
        if outer:
            self.symops = 0
        self.building += 1
        try:
            qq, dd = q, d
            for _ in range(nsteps):
                qq, dd = self.step_once(aL, aR, 1, qq, dd, sub)
        except ProofFail:
            return False
        except SymBudget:
            if not outer:
                raise
            return False
        finally:
            self.building -= 1
        if (qq, dd) != (q, d) or len(aL) != len(L) or len(aR) != len(R) - b + 1:
            return False
        bnd = aR.pop(0)[1]
        bstep = 0
        if bnd != INF:
            bstep = norm(as_lin(bnd).plus(Lin.var(BV), -1))
            if not isinstance(bstep, int):
                return False
        if any(BV in e.a for e in sub.reqs) or any(BV in m for m in sub.steps.t):
            return False
        fin = [x[1] for x in aL] + [x[1] for x in aR]
        vd = []
        for v, idx in enumerate(vpos):
            e = as_lin(fin[idx])
            if len(e.a) != 1 or e.a.get(v) != 1:
                return False
            vd.append(e.c)
        for idx, c in enumerate(fin):
            if idx not in vpos and norm(c) != norm(cur[idx]) and c != cur[idx]:
                return False
        syms = [x[0] for x in aL] + [x[0] for x in aR]
        if syms != [x[0] for x in L] + [x[0] for x in R[b:]]:
            return False
        reqs = sub.reqs
        rates = [sum(a * vd[v] for v, a in e.a.items()) for e in reqs]
        xs = [cur[idx] for idx in vpos]
        if ctx is None:
            vals = [e.ev(xs) for e in reqs]
            if any(x < 0 for x in vals):
                return False
            n = None
            for x, r in zip(vals, rates):
                if r < 0:
                    nn = x // (-r) + 1
                    n = nn if n is None or nn < n else n
            if n is None:
                self.nonhalt = "a proved cycle repeats forever"
                raise NonHalt()
            env = {v: Poly({(): Fraction(xs[v]), (IVAR,): Fraction(vd[v])}) if vd[v] else Poly.const(xs[v])
                   for v in range(len(vpos))}
            st = sum_over_i(sub.steps.subst(env), Poly.const(n)).ev({})
            assert st.denominator == 1
            self.steps += int(st)
            newx = [xs[v] + n * vd[v] for v in range(len(vpos))]
            if bstep and R[b - 1][1] != INF:
                R[b - 1][1] += n * bstep
        else:
            env = [as_lin(x) for x in xs]
            subs = [norm(e.subst(env)) for e in reqs]
            if any(isinstance(e, int) and e < 0 for e in subs):
                return False
            best = None
            for e, r in zip(subs, rates):
                if r < 0:
                    e = as_lin(e)
                    k = -r
                    if e.c % k or any(a % k for a in e.a.values()):
                        if not e.is_const():
                            return False
                    nn = Lin(e.c // k + 1, {v: a // k for v, a in e.a.items()})
                    if best is None:
                        best = nn
                    else:
                        diff = norm(nn.plus(best, -1))
                        if not isinstance(diff, int):
                            return False
                        if diff < 0:
                            best = nn
            if best is None:
                return False
            n = norm(best)
            if isinstance(n, int) and n <= 0:
                return False
            for e in subs:
                if not isinstance(e, int):
                    ctx.require(e)
            if isinstance(n, Lin):
                ctx.require(n.plus(-1))
            penv = {v: Poly.lin(env[v]).add(Poly({(IVAR,): Fraction(vd[v])})) if vd[v] else Poly.lin(env[v])
                    for v in range(len(vpos))}
            ctx.steps = ctx.steps.add(sum_over_i(sub.steps.subst(penv), Poly.lin(n)))
            newx = [norm(env[v].plus(as_lin(n).scale(vd[v]))) for v in range(len(vpos))]
            for x in newx:
                if isinstance(x, Lin):
                    ctx.require(x.plus(-1))
            if bstep and R[b - 1][1] != INF:
                R[b - 1][1] = norm(as_lin(R[b - 1][1]).plus(as_lin(n).scale(bstep)))
        for v, idx in enumerate(vpos):
            if idx < n_l:
                L[idx][1] = newx[v]
            else:
                R[b + idx - n_l][1] = newx[v]
        self.ncycles += 1
        return True

    def build(self, L, R, b, q, d):
        nv = 0
        aL, aR = [], []
        for src, dst in ((L, aL), (R[b:], aR)):
            for s, c in src:
                k = self.cls(c)
                if k == "B":
                    dst.append([s, Lin.var(nv)])
                    nv += 1
                else:
                    dst.append([s, k if k != "I" else INF])
        BV = nv
        bd = R[b - 1]
        aR.insert(0, [bd[0], INF if bd[1] == INF else Lin.var(BV)])
        ctx = Ctx()
        for v in range(nv):
            ctx.require(Lin(-1, {v: 1}))
        outer = self.building == 0
        if outer:
            self.symops = 0
        self.building += 1
        try:
            q2 = self.E_raw(aL, aR, 1, q, d, ctx)
        except ProofFail:
            self.nfail += 1
            return FAIL
        except SymBudget:
            if not outer:
                raise
            self.nfail += 1
            return FAIL
        finally:
            self.building -= 1
        seen = set()
        reqs = []
        for e in ctx.reqs:
            kk = e.key()
            if kk not in seen:
                seen.add(kk)
                reqs.append(e)
        bdelta = None
        if bd[1] != INF:
            bdelta = norm(as_lin(aR[0][1]).plus(Lin.var(BV), -1))
            if isinstance(bdelta, Lin) and BV in bdelta.a:
                self.nfail += 1
                return FAIL
            if bdelta == 0:
                bdelta = None
        if any(BV in e.a for e in reqs) or any(BV in m for m in ctx.steps.t) or \
                any(isinstance(c, Lin) and BV in c.a for s, c in aL):
            self.nfail += 1
            return FAIL
        self.nbuilt += 1
        ent = Entry(nv, reqs, [(s, c) for s, c in aL], q2, ctx.steps)
        ent.bdelta = bdelta
        return ent

    def apply(self, ent, L, R, b, ctx):
        xs = []
        for src in (L, R[b:]):
            for s, c in src:
                if self.cls(c) == "B":
                    xs.append(c)
        if ctx is None:
            for e in ent.reqs:
                if e.ev(xs) < 0:
                    return None
            newL = []
            for s, c in ent.outL:
                newL.append([s, c.ev(xs) if isinstance(c, Lin) else c])
            st = ent.steps.ev(xs)
            assert st.denominator == 1
            self.steps += int(st)
            bd = ent.bdelta
            if bd is not None and R[b - 1][1] != INF:
                R[b - 1][1] += bd.ev(xs) if isinstance(bd, Lin) else bd
        else:
            env = [as_lin(x) for x in xs]
            subs = []
            for e in ent.reqs:
                e2 = norm(e.subst(env))
                if isinstance(e2, int):
                    if e2 < 0:
                        return None
                else:
                    subs.append(e2)
            for e2 in subs:
                ctx.require(e2)
            newL = []
            for s, c in ent.outL:
                newL.append([s, norm(c.subst(env)) if isinstance(c, Lin) else c])
            penv = {v: Poly.lin(env[v]) for v in range(ent.nv)}
            ctx.steps = ctx.steps.add(ent.steps.subst(penv))
            ctx.ops += 1
            bd = ent.bdelta
            if bd is not None and R[b - 1][1] != INF:
                add = norm(bd.subst(env)) if isinstance(bd, Lin) else bd
                R[b - 1][1] = norm(as_lin(R[b - 1][1]).plus(add))
        L[:] = newL
        del R[b:]
        ent.uses += 1
        self.napply += 1
        return ent.q

    # ---------------------------------------------------------------- top level
    def run(self, seconds=60, max_steps=None):
        self.deadline = time.time() + seconds
        sys.setrecursionlimit(1000000)
        try:
            while True:
                if max_steps is not None and self.steps >= max_steps:
                    return
                if len(self.R) == 1 and self.d == 1:
                    self.q, self.d = self.basic(self.L, self.R, 1, self.q, self.d, None)
                    self.tick += 1
                    if (self.tick & 1023) == 0 and time.time() > self.deadline:
                        return
                    continue
                self.q = self.E(self.L, self.R, 1, self.q, self.d, None)
                self.d = 1
                if time.time() > self.deadline:
                    return
        except (Halt, NonHalt, Budget):
            return

    def tape_str(self, maxlen=400):
        k = self.k

        def c(x):
            if x == INF:
                return "inf"
            if isinstance(x, int) and x > 10 ** 12:
                return "~1e%d" % (len(str(x)) - 1)
            return str(x)
        w = lambda s: format(s, "0%db" % k)  # noqa: E731
        l = " ".join("%s^%s" % (w(s), c(n)) for s, n in self.L[1:])
        r = " ".join("%s^%s" % (w(s), c(n)) for s, n in reversed(self.R[1:]))
        st = "ABCDEFGH"[self.q]
        mid = (" %s> " % st) if self.d == 1 else (" <%s " % st)
        s = l + mid + r
        return s if len(s) <= maxlen else s[:maxlen // 2] + " ... " + s[-maxlen // 2:]


def ndigits(n):
    n = int(n)
    if n < 10 ** 3000:
        return len(str(n))
    return int(n.bit_length() * 0.30103) + 1


if __name__ == "__main__":
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    import threading
    threading.stack_size(512 * 1024 * 1024)
    m = sys.argv[1]
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    sec = float(sys.argv[3]) if len(sys.argv) > 3 else 60
    if "mirror" in sys.argv[4:]:
        m = mirror(m)
    out = {}

    def go():
        t0 = time.time()
        s = Sim(m, k)
        s.run(sec)
        out["s"] = s
        out["t"] = time.time() - t0
    th = threading.Thread(target=go)
    th.start()
    th.join()
    s = out["s"]
    print("K=%d  steps ~1e%d  basic %d  entries %d (failed %d)  applications %d  cycles %d  %.1fs" % (
        k, ndigits(s.steps) - 1, s.nbasic, s.nbuilt, s.nfail, s.napply, s.ncycles, out["t"]))
    if s.halted:
        print("HALTED after", s.steps, "steps")
    elif s.nonhalt:
        print("DOES NOT HALT:", s.nonhalt)
    else:
        print("no halt in the first %d-digit number of steps" % ndigits(s.steps))
    print(s.tape_str())
