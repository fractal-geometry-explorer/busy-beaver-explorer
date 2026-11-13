"""Closure search: an attempt to prove non-halting from blank tape by covering every reachable configuration with a
finite set of *templates* (shapes whose long blocks have arbitrary counts above a threshold).

A branch is a symbolic configuration (block counts are linear forms in variables over the naturals).  It is run with
the moves of accel.py.  Whenever a shape recurs with a constant change of the counts, the period is re-run from the
generalised configuration (every changing or long block gets a fresh variable plus a threshold T_i); if that symbolic
run returns to the same shape with counts x_i + T_i + d_i, the period holds for all x_i.  The generalised
configuration is the template.  If an earlier template covers it, the branch ends; otherwise the period is iterated
as far as it goes, splitting on which shrinking block runs out first and on its remainder, and every case continues
as a new branch.  A count that might be zero splits the branch (v = 0, v >= 1).  All splits over-approximate (the
relation between counts is forgotten), so if the search ends with no halt, no configuration reachable from blank
tape halts.

usage (from the repo root): python3 holdouts/1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---/py/closure.py MACHINE [MAXTEMPLATES]
"""
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import accel  # noqa: E402
from accel import Rep, Lin, BL, NeedSplit, Halted, move, compress, shape, reps  # noqa: E402

_fresh = [0]
SPLIT = 32


def fresh():
    _fresh[0] += 1
    return 'v%d' % _fresh[0]


def is_var(n):
    return not isinstance(n, int) and not n.is_const()


def cval(n):
    return n if isinstance(n, int) else n.k


def map_counts(c, f):
    """new Cfg with each Rep count replaced by f(index, count)"""
    rs = reps(c)
    idx = {id(z): i for i, z in enumerate(rs)}

    def g(z):
        if isinstance(z, Rep):
            return Rep(z.w, f(idx[id(z)], z.n))
        return z
    d = accel.Cfg(c.m, [g(z) for z in c.L], c.st, [g(z) for z in c.R], 0)
    d.ev = c.ev
    return d


def subst_lin(n, v, k):
    if isinstance(n, int) or v not in n.c:
        return n
    if k is None:
        return Lin(n.k, {u: a for u, a in n.c.items() if u != v})
    return n + n.c[v] * k


def subst(c, v, k):
    """v := v + k (k>=0 int) or v := 0 (k=None)"""
    return map_counts(c, lambda i, n: subst_lin(n, v, k))


def subst_hist(hist, v, k):
    return {sh: ([subst_lin(n, v, k) for n in cn], e) for sh, (cn, e) in hist.items()}


def generalise(c, delta, T):
    Ts = {}

    def f(i, n):
        if is_var(n) or delta[i] != 0 or cval(n) >= 3 * T:
            t = min(T, cval(n))
            Ts[i] = t
            return Lin(fresh()) + t
        return Lin(cval(n))
    return map_counts(c, f), Ts


def spec(c):
    return tuple(('v', n.k) if is_var(n) else ('c', cval(n)) for n in (z.n for z in reps(c)))


def covers(t, s):
    for (a, x), (b, y) in zip(t, s):
        if a == 'c':
            if b != 'c' or x != y:
                return False
        elif y < x:
            return False
    return True


def run_events(c, nev, maxmoves):
    k = 0
    mv = 0
    while k < nev:
        mv += 1
        if accel.advance(c):
            k += 1
        if mv > maxmoves:
            raise RuntimeError('moves')


def verify(c, nev, delta, T):
    g, Ts = generalise(c, delta, T)
    s = map_counts(g, lambda i, n: n)
    sh0 = shape(s)
    start = [z.n for z in reps(s)]
    try:
        run_events(s, nev, 10 ** 6)
    except NeedSplit:
        return None
    if shape(s) != sh0:
        return None
    end = [z.n for z in reps(s)]
    for i, (a, b) in enumerate(zip(start, end)):
        d = Lin(b) - Lin(a)
        if not d.is_const() or d.k != delta[i]:
            return None
    return g, Ts


class Search:
    def __init__(s, M, maxt=20000, log=print):
        s.m = accel.Machine(M)
        s.templates = {}
        s.ntempl = 0
        s.queue = [(accel.Cfg(s.m, [BL], 0, [BL], Lin(0)), {}, 0)]
        s.log = log
        s.maxt = maxt
        s.branches = 0
        s.forever = 0

    def add_template(s, g):
        sh = shape(g)
        sp = spec(g)
        lst = s.templates.setdefault(sh, [])
        for t in lst:
            if covers(t, sp):
                return False
        lst.append(sp)
        s.ntempl += 1
        return True

    def jump_cases(s, g, Ts, delta):
        """configurations after iterating the period from template g as far as it goes"""
        rs = reps(g)
        shrink = [i for i, d in enumerate(delta) if d < 0 and i in Ts]
        if not shrink:
            if any(d < 0 for d in delta):
                return None          # only constant blocks shrink: no jump, run on
            return 'forever'
        for i in shrink:
            if Ts[i] < -delta[i]:
                return None
        out = []
        for i in shrink:
            r = -delta[i]
            for sres in range(r):
                def f(j, n, i=i, sres=sres):
                    if j == i:
                        return Lin(Ts[i] - r + sres)
                    if j in shrink:
                        return Lin(fresh()) + (Ts[j] + delta[j])
                    if delta[j] > 0:
                        return Lin(fresh()) + Ts[j]
                    return n
                out.append(map_counts(g, f))
        return out

    def branch(s, item, maxmoves=3 * 10 ** 6):
        s.branches += 1
        c, hist, evn = item
        mv = 0
        while True:
            try:
                isev = accel.advance(c)
            except NeedSplit as e:
                n = e.args[0].n
                v = next(u for u, a in n.c.items() if a > 0)
                for j in range(SPLIT):      # v = j
                    cj = map_counts(c, lambda i, n, j=j: subst_lin(subst_lin(n, v, j), v, None))
                    s.queue.append((cj, {}, 0))
                s.queue.append((subst(c, v, SPLIT), subst_hist(hist, v, SPLIT), evn))
                return
            mv += 1
            if mv > maxmoves:
                raise RuntimeError('branch too long: %s' % c)
            if not isev:
                continue
            evn += 1
            sh = shape(c)
            cn = [z.n for z in reps(c)]
            h = hist.get(sh)
            hist[sh] = (cn, evn)
            if h is None:
                continue
            pc = h[0]
            d = []
            ok = True
            for a, b in zip(cn, pc):
                x = Lin(a) - Lin(b)
                if not x.is_const():
                    ok = False
                    break
                d.append(x.k)
            if not ok or not any(d):
                continue
            nev = evn - h[1]
            res = None
            for T in (8, 24, 72):
                res = verify(c, nev, d, T)
                if res:
                    break
            if not res:
                continue
            g, Ts = res
            if not s.add_template(g):
                return
            if s.ntempl > s.maxt:
                raise RuntimeError('too many templates')
            cases = s.jump_cases(g, Ts, d)
            if cases == 'forever':
                s.forever += 1
                return
            if cases is None:
                continue
            s.queue.extend((x, {}, 0) for x in cases)
            return

    def run(s):
        t0 = time.time()
        while s.queue:
            c = s.queue.pop()
            s.branch(c)
            if s.branches % 200 == 0:
                mb = max((len(sp) for l in s.templates.values() for sp in l), default=0)
                s.log('branches %d templates %d shapes %d maxblocks %d queue %d forever %d %.0fs' %
                      (s.branches, s.ntempl, len(s.templates), mb, len(s.queue), s.forever, time.time() - t0))
        s.log('CLOSED: branches %d templates %d forever %d' % (s.branches, s.ntempl, s.forever))


def main():
    M = sys.argv[1]
    mx = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    S = Search(M, mx)
    try:
        S.run()
    except Halted as h:
        print('HALT reached in a branch', h)


if __name__ == '__main__':
    main()
