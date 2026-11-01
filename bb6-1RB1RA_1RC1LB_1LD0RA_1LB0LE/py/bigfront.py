"""Does a large first block bound the halvings?  (notes/LAB_NOTES.md, 1 November 2026, "Bound the halvings by the
first block at a change".)

The first block changes only at a few kinds of pass (`invsearch.changes_first`); between two changes it is only
halved, by front stops, so a stop at a first block of 1 needs a change to leave it at f = 2^(H+1) - 1 and then a run of
H front stops (the Mersenne lemma).  The idea tested here: if the orbit keeps f large at every change, a fraction c of
the ones, and a run of H front stops needed many more ones than 2^H, the event would be excluded.

* `orbit_runs(n)`: along the blank orbit, the first block f and the ones right after each change, and the front stops
  in the run that follows (computed, on the closed form `passmap`, which Lean's `next` proves).
* `search(k0, H, ...)`: an exact search for the smallest list (k0 blocks, first block 2^(H+1) - 1, `Good`,
  4 | ones, |psi| <= W) whose run makes H front stops with no change of the first block and then stops at a first block
  of 1.  Branch and bound on lattice classes: every start block is p + 2^m u, every later block an affine form in the
  u's, and a parity the pass needs splits one u; a leaf is a route, and its smallest list is found exactly.

usage:
  python3 py/bigfront.py orbit N              runs along the first N passes (after pass 50)
  python3 py/bigfront.py search K0 H INV W    the smallest list with ones <= INV * f, |psi| <= W (first one found
                                              with FIRST=1 in the environment)
  python3 py/bigfront.py witness              the lists of lean/BigFront.lean, pass by pass
"""
import collections
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import passmap  # noqa: E402
from invsearch import changes_first, psi  # noqa: E402

sys.setrecursionlimit(100000)

# lean/BigFront.lean (first block first)
WF = [255, 512, 32, 60, 32, 64, 9]                    # psi -23, ones 964, f/ones 0.265, 7 halvings, H = 7
WH = [255, 528, 48, 24, 8, 32, 64, 128, 129]        # psi 1, ones 1216, f/ones 0.210, H = 7


def orbit_runs(n):
    """Rows (pass, f, ones, k, R) for each run of the blank orbit within the first n passes: the pass where the run
    starts (right after a change of the first block), the first block and ones there, the block count, and R the
    front stops before the next change."""
    y = list(passmap.FIRST)
    cur = None
    for i in range(1, n + 1):
        k, j = len(y), passmap.stop_index(y)
        if cur is None:
            cur = [i, y[0], sum(y), k, 0]
        cur[4] += j == 1
        if changes_first(k, j):
            yield tuple(cur)
            cur = None
        y = passmap.passmap(y)


def orbit_summary(n, skip=50):
    hist = collections.Counter()
    low = most = slack = None
    for row in orbit_runs(n):
        p, f, s, k, r = row
        hist[r] += 1
        if p <= skip:
            continue
        if low is None or f / s < low[0]:
            low = (f / s, row)
        if most is None or r > most[0]:
            most = (r, row)
        sl = math.log2(f + 1) - r
        if slack is None or sl < slack[0]:
            slack = (sl, row)
    return hist, low, most, slack


# ---------------------------------------------------------------------------------------------------------------
# lattice forms: (c, a_1, .., a_(K-1)) is c + sum a_i u_i; start block i (i >= 1) is c_i + 2^m_i u_i

def _sub(f, j, b):
    g = list(f)
    g[0] += g[j] * b
    g[j] *= 2
    return tuple(g)


def _add(*fs):
    return tuple(sum(x) for x in zip(*fs))


def _cadd(f, c):
    return (f[0] + c,) + tuple(f[1:])


def _half(f):
    assert all(x % 2 == 0 for x in f), f
    return tuple(x // 2 for x in f)


def _oddvar(f):
    for j in range(1, len(f)):
        if f[j] % 2:
            return j
    return 0


def _least(f, i):
    """The least value >= 2 (>= 1 for the first block) of the start form f of block i, and its u."""
    lo = 1 if i == 0 else 2
    if i == 0:
        return f[0], 0
    M = f[i]
    u = max(0, -((f[0] - lo) // M))
    return f[0] + M * u, u


def _psi_form(start, K):
    P = [0] * K
    for i, f in enumerate(start):
        c = (-2) ** (K - 1 - i)
        for t in range(K):
            P[t] += c * f[t]
    return P


def _lower(start, K, W):
    """A lower bound on the ones of the class: least values, then the cheapest single move that brings psi into
    [-W, W] (the LP bound, whose optimum moves one coordinate)."""
    s = sum(_least(f, i)[0] for i, f in enumerate(start))
    if W is not None:
        P = _psi_form(start, K)
        p = P[0] + sum(P[i] * _least(start[i], i)[1] for i in range(1, K))
        if not -W <= p <= W:
            need = p - W if p > W else p + W
            cost = None
            for i in range(1, K):
                a = P[i]
                if a == 0 or (a > 0) == (need > 0):
                    continue
                c = start[i][i] * -(-abs(need) // abs(a))
                cost = c if cost is None or c < cost else cost
            if cost is None:
                return math.inf
            s += cost
    return s + (-s) % 4


def _exact(start, K, W, bound):
    """The smallest list of the class with ones < bound, 4 | ones and |psi| <= W, or None (exact, by search on u)."""
    P = _psi_form(start, K)
    base = [_least(f, i) for i, f in enumerate(start)]
    p0 = P[0] + sum(P[i] * base[i][1] for i in range(1, K))
    s0 = sum(v for v, _ in base)
    best = [bound, None]

    def rest_lb(i, p):
        if W is None or -W <= p <= W:
            return 0
        need = p - W if p > W else p + W
        cost = None
        for t in range(i, K):
            a = P[t]
            if a == 0 or (a > 0) == (need > 0):
                continue
            c = start[t][t] * -(-abs(need) // abs(a))
            cost = c if cost is None or c < cost else cost
        return math.inf if cost is None else cost

    def go(i, du, s, p):
        if s + rest_lb(i, p) >= best[0]:
            return
        if i == K:
            if (W is None or -W <= p <= W) and s % 4 == 0:
                best[0] = s
                best[1] = [base[0][0]] + [base[t][0] + start[t][t] * du[t - 1] for t in range(1, K)]
            return
        d = 0
        while s + start[i][i] * d < best[0]:
            go(i + 1, du + [d], s + start[i][i] * d, p + P[i] * d)
            d += 1

    go(1, [], s0, p0)
    return (best[0], best[1]) if best[1] else None


class _Found(Exception):
    pass


def search(k0, H, bound, W=None, first=False, maxpass=None):
    """The smallest list (k0 blocks, first block 2^(H+1) - 1, ones < bound, Good, 4 | ones, |psi| <= W) whose run
    makes H front stops with no change of the first block and then stops at a first block of 1.
    Returns (ones, list) or None, and the number of nodes."""
    F, K = 2 ** (H + 1) - 1, k0
    maxpass = 3 * H + 2 if maxpass is None else maxpass
    best = [bound, None]
    nodes = [0]

    def split(start, cur, form):
        j = _oddvar(form)
        for b in (0, 1):
            yield [_sub(f, j, b) for f in start], [_sub(f, j, b) for f in cur]

    def go(start, cur, fronts, prevfront, npass):
        nodes[0] += 1
        if _lower(start, K, W) >= best[0]:
            return
        S = _add(*start)                       # 4 | ones
        if _oddvar(S):
            for st, cu in split(start, cur, S):
                go(st, cu, fronts, prevfront, npass)
            return
        if S[0] % 2:
            return
        S2 = _half(S)
        if _oddvar(S2):
            for st, cu in split(start, cur, S2):
                go(st, cu, fronts, prevfront, npass)
            return
        if S2[0] % 2:
            return
        k = len(cur)
        for i in range(k - 1, -1, -1):         # the parities the stop index reads, right to left
            if _oddvar(cur[i]):
                for st, cu in split(start, cur, cur[i]):
                    go(st, cu, fronts, prevfront, npass)
                return
            if (cur[i][0] % 2 == 0) == (i == k - 1):
                break                          # an even last block, or the odd block the sweep stops at
        if cur[-1][0] % 2 == 0:
            j = k
        else:
            j = k - 1
            while j >= 1 and cur[j - 1][0] % 2 == 0:
                j -= 1
            if j == 0:
                return                         # a halt, not a stop at a block of 1
        if j == 1:
            if prevfront:
                return
            if fronts == H:                    # the first block is 1: the event
                r = _exact(start, K, W, best[0])
                if r is not None:
                    best[0], best[1] = r[0], r[1]
                    if first:
                        raise _Found()
                return
            q = [_half(_cadd(f, -1)) if t in (0, k - 1) else _half(f) for t, f in enumerate(cur)]
            h = q[:]
            h[-1] = _cadd(q[-1], 3)
            out = [q[0], _add(_cadd(q[0], 1), h[1])] + [_add(h[t], h[t + 1]) for t in range(1, k - 1)] + [_cadd(h[-1], -1)]
            go(start, out, fronts + 1, True, npass + 1)
            return
        if changes_first(k, j) or npass >= maxpass:
            return
        if j == k:
            m = _half(cur[-1])
            out = cur[:k - 3] + [_add(cur[k - 3], _cadd(m, 2)), _add(cur[k - 2], _cadd(m, 2))]
        else:
            q = {t: _half(cur[t - 1]) for t in range(j + 1, k)}
            q[k] = _cadd(_half(_cadd(cur[k - 1], -1)), 3)
            qj = _half(_cadd(cur[j - 1], -1))
            out = (cur[:j - 3] + [_add(cur[j - 3], qj), _add(_add(cur[j - 2], _cadd(qj, 1)), q[j + 1])]
                   + [_add(q[t], q[t + 1]) for t in range(j + 1, k)] + [_cadd(q[k], -1)])
        go(start, out, fronts, False, npass + 1)

    start = [(F,) + (0,) * (K - 1)] + [(0,) + tuple(1 if t == i else 0 for t in range(1, K)) for i in range(1, K)]
    try:
        go(start, list(start), 0, False, 0)
    except _Found:
        pass
    return (best[0], best[1]) if best[1] else None, nodes[0]


def trace(y, max_passes=200):
    """(first block, block count, stop index) per pass until a change of the first block, the event, or a halt."""
    rows = []
    for _ in range(max_passes):
        k, j = len(y), passmap.stop_index(y)
        rows.append((y[0], k, j))
        if changes_first(k, j):
            return rows, "change"
        z = passmap.passmap(y)
        if z is None:
            return rows, "stop at a block of 1"
        if not isinstance(z, list):
            return rows, "halt"
        y = z
    return rows, "max"


def main(argv):
    if not argv:
        print(__doc__)
    elif argv[0] == "orbit":
        hist, low, most, slack = orbit_summary(int(argv[1]))
        print("front stops per run (all runs):", sorted(hist.items()))
        print("smallest f/ones at a change after pass 50: %.4f %s" % low)
        print("most front stops in a run after pass 50:", most)
        print("smallest log2(f+1) - R after pass 50: %.2f %s" % slack)
    elif argv[0] == "search":
        k0, H, inv, W = int(argv[1]), int(argv[2]), float(argv[3]), int(argv[4])
        F = 2 ** (H + 1) - 1
        r, n = search(k0, H, int(F * inv) + 1, W=W, first=bool(os.environ.get("FIRST")))
        if r:
            v, y = r
            print(k0, H, y, "ones", v, "f/ones %.4f" % (F / v), "psi", psi(y), "->", trace(y)[1], "nodes", n)
        else:
            print(k0, H, "none with ones <=", inv, "* f; nodes", n)
    elif argv[0] == "witness":
        for y in (WF, WH):
            rows, end = trace(y)
            print(y, "psi", psi(y), "ones", sum(y), "f/ones %.4f" % (y[0] / sum(y)))
            print("  first blocks", [r[0] for r in rows], "->", end)
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
