"""Level-stripping accelerator for the twins 1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA (1) and
1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA (2).

The word right of the wall is cut into SEGMENTS from the left.  A segment is a token list with at most one
symbolic count (a run (1 0)^n), whose behaviour under one hit (one wall visit G for the first segment) was derived
by running the engine's recursion on  segment ++ Omega  with n symbolic and an opaque rest Omega:
    op(pre (1 0)^n post  Omega) = pre' (1 0)^(n+dn) post'  h^c(Omega)      at a n + b machine steps,
valid for every rest and every n >= nmin.  The reachable states (pre, post) of a segment must close up (a finite
automaton, a rho-shaped path).  Below the last segment that closes up lies the BOTTOM B, a word handled by the
engine (geng.hpow).  Since a segment does not look into its rest, the ladder of segments is a mixed-radix counter:
the number of wall visits after which B has received exactly m hits, and the counts, states and steps after any
number of visits, are computed level by level in closed form (no recursion, no simulation of single hits).
"""
import sys, pickle, time
sys.set_int_max_str_digits(0)
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import geng
from geng import Lin, Rec, h, G, build_raw, build, to_tokens, Opaque, Budget, Event
geng.CST.update({'g0': 16, 'cend': -4, 'c1': 0, 'd1': 2, 'd0': 0, 'cR': 26})
geng.DROP[0] = False
sys.setrecursionlimit(1000000)
OPS = {'G': G, 'h': h}
BIG = 50          # a run (1 0)^n with n > BIG must be the symbolic count of its segment
JMAX = 24         # longest segment (tokens)
MAXST = 24        # most states of a segment automaton

TR = {}
TRMAX = 400000    # the caches TR and CYC are emptied when they grow past these sizes (memory of a long run)
CYCMAX = 40000
NEG = [False]     # also accept levels whose count falls (dn < 0, fuel-like); they run out, advance stops there


def trans(opn, pre, sym, post):
    """one op on pre (1 0)^n post Omega (sym) or pre Omega (not sym).  -> (pre', post', dn, c, a, b, nmin) or None"""
    key = (opn, pre, sym, post, NEG[0])
    r = TR.get(key, 0)
    if r != 0:
        return r
    n = Lin.var(0, 1000)
    toks = list(pre) + ([('R', n)] + list(post) if sym else [])
    T = build_raw(toks, (('O', 0), None))
    Rec.cons = []; Rec.work = 0; Rec.limit = 20000
    cs = geng.C[0]; geng.C[0] = 0
    res = None
    try:
        out = to_tokens(OPS[opn](T))
        cost = geng.C[0]
        if out and type(out[-1]) is tuple and out[-1][0] == 'O' and len(out) >= 1:
            body = out[:-1]
            c = out[-1][1]
            si = [i for i, t in enumerate(body) if type(t) is tuple and len(t) > 1 and isinstance(t[1], Lin)]
            bad = any(isinstance(t, Lin) for t in body)
            if not bad and ((sym and len(si) == 1 and body[si[0]][0] == 'R' and body[si[0]][1].c == {0: 1})
                            or (not sym and not si)):
                okc = True; nmin = 1
                for cf, k, s, thr in Rec.cons:
                    a = cf.get(0, 0)
                    if (s == 1 and a < 0) or (s == -1 and a > 0):
                        okc = False; break
                    if a != 0:
                        nm = -((k - thr) // a) if s == 1 else -((thr - k) // (-a))
                        nmin = max(nmin, nm)
                    elif (s == 1 and k < thr) or (s == -1 and k > thr):
                        okc = False; break
                if isinstance(cost, Lin):
                    if set(cost.c) - {0}:
                        okc = False
                    a, b = cost.c.get(0, 0), cost.k
                else:
                    a, b = 0, cost
                if okc:
                    if sym:
                        i = si[0]
                        dn = body[i][1].k
                        if dn >= 0 or NEG[0]:
                            res = (tuple(body[:i]), tuple(body[i + 1:]), dn, c, a, b, max(nmin, 1 - dn))
                    else:
                        res = (tuple(body), (), 0, c, 0, b, 0)
    except (Opaque, Budget, Event, RecursionError, AssertionError, TypeError):
        res = None
    finally:
        Rec.cons = None; geng.C[0] = cs
    if len(TR) >= TRMAX:
        TR.clear()
    TR[key] = res
    return res


CYC = {}


def cycle(opn, sym, st):
    """the path of states from st: (tail, cyc) lists of (state, dn, c, a, b, nmin); None if not closed"""
    key = (opn, sym, st, NEG[0])
    r = CYC.get(key, 0)
    if r != 0:
        return r
    seq = []; seen = {}
    cur = st
    res = None
    while True:
        if cur in seen:
            k = seen[cur]
            res = (seq[:k], seq[k:])
            break
        if len(seq) >= MAXST:
            break
        t = trans(opn, cur[0], sym, cur[1])
        if t is None:
            break
        seen[cur] = len(seq)
        seq.append((cur,) + t[2:])
        cur = (t[0], t[1])
    if len(CYC) >= CYCMAX:
        CYC.clear()
    CYC[key] = res
    return res


class Level:
    __slots__ = ('op', 'sym', 'st', 'n', 'agg')

    def __init__(self, op, sym, st, n):
        self.op, self.sym, self.st, self.n = op, sym, st, n

    def path(self):
        return cycle(self.op, self.sym, self.st)

    def tokens(self):
        pre, post = self.st
        if self.sym:
            return list(pre) + [('R', self.n)] + list(post)
        return list(pre)


def agg(cyc):
    """totals of one round of the cycle: p, D (dn), Cc (passes), A (sum a), B (sum a*cum dn + b), cum passes"""
    D = 0; Cc = 0; A = 0; B = 0; cum = []
    for (_, dn, c, a, b, nm) in cyc:
        A += a; B += a * D + b
        D += dn; Cc += c
        cum.append(Cc)
    return len(cyc), D, Cc, A, B, cum


AG = {}


def advance(L, q, stop=None):
    """apply q hits to level L in place; returns (passes, steps).  A level whose count falls runs out: then
    only the hits it can take are applied, and if stop is a list, the number of hits not applied is put in it"""
    passes = 0; steps = 0
    while q > 0:
        tail, cyc = L.path()
        if tail:
            (st, dn, c, a, b, nm) = tail[0]
            if NEG[0] and L.sym and L.n < nm:
                break
            steps += a * L.n + b; L.n += dn; passes += c; q -= 1
            L.st = trans(L.op, st[0], L.sym, st[1])[:2]
            continue
        key = (L.op, L.sym, L.st, NEG[0])
        g = AG.get(key)
        if g is None:
            g = AG[key] = agg(cyc)
        p, D, Cc, A, B, cum = g
        j = q // p
        if NEG[0] and D < 0 and j and L.sym:
            NR = max(nm - cd for (cd, nm) in zip(cumdn(cyc), (t[5] for t in cyc)))
            j = min(j, 0 if L.n < NR else (L.n - NR) // (-D) + 1)
        if j:
            n = L.n
            steps += j * (A * n + B) + A * D * (j * (j - 1) // 2)
            passes += j * Cc
            L.n = n + j * D
            q -= j * p
        k = 0
        for (st, dn, c, a, b, nm) in cyc[:q]:
            if NEG[0] and L.sym and L.n < nm:
                break
            steps += a * L.n + b; L.n += dn; passes += c; k += 1
        if k:
            L.st = cyc[k][0] if k < p else cyc[0][0]
        q -= k
        break
    if q and stop is None:
        raise AssertionError('level ran out')
    if stop is not None:
        stop.append(q)
    return passes, steps


def cumdn(cyc):
    out = []; D = 0
    for t in cyc:
        out.append(D); D += t[1]
    return out


def first_pass(L, m):
    """least q >= 1 such that q hits to L (from its present state) make it pass at least m >= 1 hits; None if never"""
    tail, cyc = L.path()
    q = 0; P = 0
    for (st, dn, c, a, b, nm) in tail:
        q += 1; P += c
        if P >= m:
            return q
    key = (L.op, L.sym, cyc[0][0], NEG[0])
    g = AG.get(key)
    if g is None:
        g = AG[key] = agg(cyc)
    p, D, Cc, A, B, cum = g
    if Cc == 0:
        return None
    r = m - P
    j = (r - 1) // Cc
    r -= j * Cc
    for t, cc in enumerate(cum):
        if cc >= r:
            return q + j * p + t + 1
    raise AssertionError


def segment(toks, i0, opn0):
    """cut regular segments off toks from index i0; returns (levels, index of the bottom)"""
    levels = []
    i = i0
    opn = opn0
    N = len(toks)
    while i < N - 1:
        found = None
        jmax = min(i + JMAX, N - 1)
        for j in range(i + 1, jmax + 1):
            t = toks[j - 1]
            if j - 1 > i and type(t) is tuple and t[0] == 'R' and t[1] > BIG:
                jmax = j - 1
                break
        cand = []
        for j in range(jmax, i, -1):
            cand.append((j, None))
            t = toks[j - 1]
            if type(t) is tuple and t[0] == 'P' and t[1] > 2:
                cand.append((j, 1)); cand.append((j, 2))
        for j, peel in cand:
            seg = toks[i:j]
            if peel:
                t = seg[-1]
                seg = seg[:-1] + [('P', peel, t[2])]
            if j - i > 1 and type(seg[-1]) is tuple and seg[-1][0] == 'R':
                continue
            big = [k for k, t in enumerate(seg) if type(t) is tuple and t[0] == 'R' and t[1] > BIG]
            if len(big) > 1:
                continue
            if len(seg) > 1 and not NEG[0] and any(type(t) is tuple and t[0] in ('P', 'Z') and t[1] > 10 ** 6 for t in seg):
                continue
            cands = []
            if big:
                cands = [big[0]]
            else:
                cands = [None] + [k for k, t in enumerate(seg) if type(t) is tuple and t[0] == 'R'][:2]
            for k in cands:
                if k is None:
                    st = (tuple(seg), ()); sym = False; n = 0
                else:
                    st = (tuple(seg[:k]), tuple(seg[k + 1:])); sym = True; n = seg[k][1]
                pc = cycle(opn, sym, st)
                if pc is None:
                    continue
                if sym and any(nm > n for (_, _, _, _, _, nm) in pc[0] + pc[1]):
                    continue
                if not any(c for (_, _, c, _, _, _) in pc[0] + pc[1]) and not NEG[0]:
                    continue      # never passes a hit on: not a level of a ladder (with NEG: a level that keeps them)
                found = (j, Level(opn, sym, st, n), peel)
                break
            if found:
                break
        if not found:
            break
        j, L, peel = found
        if peel:
            t = toks[j - 1]
            toks[j - 1:j] = [('P', peel, t[2]), ('P', t[1] - peel, t[2])]     # in place: callers index this list
            N = len(toks)
        levels.append(L)
        i = j
        opn = 'h'
    return levels, i


def chain(levels, m):
    """visits (hits to levels[0]) after which the bottom has received exactly m >= 1 hits"""
    for L in reversed(levels):
        m = first_pass(L, m)
        if m is None:
            return None
    return m


def apply(levels, q):
    """q hits to levels[0]; returns (hits passed to the bottom, steps)"""
    steps = 0
    for L in levels:
        q, s = advance(L, q)
        steps += s
        if q == 0:
            break
    return q, steps


def apply_stop(levels, q):
    """like apply, but a level that runs out stops it: returns (i, r, passes to the bottom, steps), where levels[i]
    is the level that ran out with r hits not applied (i = None: none ran out)"""
    steps = 0
    for i, L in enumerate(levels):
        stop = []
        q, s = advance(L, q, stop)
        steps += s
        if stop[0]:
            return i, stop[0], q, steps
        if q == 0:
            break
    return None, 0, q, steps


def word(levels, B):
    toks = []
    for L in levels:
        toks += L.tokens()
    return build(toks, B)
