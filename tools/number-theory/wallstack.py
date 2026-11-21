"""Evidence for 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC: the wall as a stack of counters under every parity sequence.

The step map (W, N) -> (W', N') of that machine (lean/Reduction.lean, `stepMap`) changes the wall W only through
N mod 2. So the walls reachable when the parity of N is chosen freely at every step over-approximate the real run.
A closed set of such walls without a halting step would prove non-halting. This script explores that set with the
stack-of-counters model of the machine's py/stackmodel.py (fitted, then checked against the Lean step map: `compare`).

usage (from the repository root):
  python3 tools/number-theory/wallstack.py bfs LIM        every wall of at most LIM cells reachable from the wall `1`
                                                         under free parities: count, negative counts, smallest
                                                         ratio of a counter to the one below it, largest lower count
  python3 tools/number-theory/wallstack.py margin LIM     for every reachable wall with two open counters on top: how
                                                         many odd steps in a row the top would need before its count
                                                         goes below zero, against how many it actually gets
  python3 tools/number-theory/wallstack.py orbit STEPS    the model along the real orbit (from step 10,206 of the run)
  python3 tools/number-theory/wallstack.py runs STEPS     along the real orbit: odd runs of N, and the fewest odd steps in
                                                         a row that would drive a count below zero (two open counters
                                                         on top)
  python3 tools/number-theory/wallstack.py need           odd steps in a row needed for a negative count, for a top
                                                         count k over an open counter kl
  python3 tools/number-theory/wallstack.py compare LIM    the model against the Lean step map (py/zonemap.py) on every
                                                         step of the free-parity wall graph to LIM cells (slow: 300
                                                         takes about 2 minutes)
"""
import os
import sys
import threading
from collections import deque
from fractions import Fraction

M = "1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC"
PY = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "holdouts", M, "py")
sys.path.insert(0, PY)
from stackmodel import step, stepN, unword, word  # noqa: E402

sys.setrecursionlimit(1_000_000)
threading.stack_size(512 * 1024 * 1024)


def wlen(lv):
    return 1 + sum(3 * k + (6 if closed else 7) for k, closed in lv)


def reachable(lim):
    seen, queue, neg = {()}, deque([()]), []
    while queue:
        lv = queue.popleft()
        for s in (0, 1):
            r = step(list(lv), s)
            if r is None:
                neg.append((lv, s))
                continue
            nl = tuple(r[0])
            if wlen(nl) <= lim and nl not in seen:
                seen.add(nl)
                queue.append(nl)
    return seen, neg


def bfs(lim):
    seen, neg = reachable(lim)
    ratio, lower = None, 0
    for lv in seen:
        for i in range(len(lv) - 1):
            t, k = lv[i][0], lv[i + 1][0]
            if t > 0:
                lower = max(lower, t)
                if ratio is None or k / t < ratio[0]:
                    ratio = (k / t, lv[i:i + 2])
    print(f"{len(seen)} walls of at most {lim} cells; a count goes below zero in {len(neg)} steps; "
          f"smallest counter/lower ratio {ratio[0]:.2f} at {ratio[1]}; largest count below the top {lower}; "
          f"at most {max(len(x) for x in seen)} items")


def margin(lim):
    seen, _ = reachable(lim)
    res = []
    for lv in seen:
        if len(lv) < 2 or lv[-1][1] or lv[-2][1]:
            continue
        below, k, need = list(lv[:-1]), Fraction(lv[-1][0]), 0
        while k >= 0 and need < 5000:
            r = step(below, 1)
            below, k, need = r[0], (3 * k - 1) / 2 + r[1], need + 1
        cur, got = list(lv), 0
        while len(cur) >= 2 and not cur[-1][1] and not cur[-2][1] and cur[-1][0] % 2 == 1:
            cur, got = step(cur, 1)[0], got + 1
        res.append((need, got, lv[-2:]))
    res.sort(key=lambda x: x[0])
    print(f"{len(res)} walls with two open counters on top")
    print("fewest odd steps needed for a negative count:", [(a, b, c) for a, b, c in res[:5]])
    print(f"largest share of the needed run actually reached: {max(b / a for a, b, _ in res if a):.2f}")


def orbit(steps):
    import zonemap as Z
    W, N = Z.START
    lv, ratio, lower, depth = unword(Z.show(W)), None, 0, 0
    for i in range(steps):
        m = stepN(lv, N)
        if m is None:
            print("the model breaks at step", i, lv)
            return
        lv, N = m
        depth = max(depth, len(lv))
        for j in range(len(lv) - 1):
            t, k = lv[j][0], lv[j + 1][0]
            if t > 0:
                lower = max(lower, t)
                if ratio is None or k / t < ratio:
                    ratio = k / t
    print(f"{steps} steps of the real orbit: N has {N.bit_length()} bits, at most {depth} items, "
          f"largest count below the top {lower}, smallest counter/lower ratio {ratio}")


def need_of(lv):
    below, k, n = list(lv[:-1]), Fraction(lv[-1][0]), 0
    while k >= 0 and n < 5000:
        r = step(below, 1)
        below, k, n = r[0], (3 * k - 1) / 2 + r[1], n + 1
    return n


def runs(steps):
    import zonemap as Z
    from collections import Counter
    W, N = Z.START
    lv, run, hist, best, height = unword(Z.show(W)), 0, Counter(), None, 0
    for i in range(steps):
        if N % 2:
            run += 1
        else:
            hist[run] += 1
            run = 0
        if len(lv) >= 2 and not lv[-1][1] and not lv[-2][1] and i % 5 == 0:
            n = need_of(lv)
            if best is None or n < best[0]:
                best = (n, lv[-2:], i)
        lv, N = stepN(lv, N)
        height = max(height, len(lv))
    print(f"{steps} steps: at most {height} items; odd runs of N (length: how many) {sorted(hist.items())}; "
          f"fewest odd steps in a row a negative count would need: {best[0]} (counters {best[1]}, step {best[2]})")


def need(_):
    for kl in (0, 1, 2, 5, 10, 17):
        print(kl, [(k, need_of([(kl, False), (k, False)])) for k in (10, 20, 50, 100, 200, 500, 1000)])


def compare(lim):
    import zonemap as Z
    dist, queue, bad, n = {(1,): 0}, [(1,)], 0, 0
    while queue:
        W = queue.pop(0)
        lv = unword(Z.show(W))
        for par in (0, 1):
            N = 10 ** 7 + par
            r = Z.step_map(W, N)
            m = stepN(lv, N)
            n += 1
            if len(r) != 2 or m is None or word(m[0]) != Z.show(r[0]) or m[1] != r[1]:
                bad += 1
                continue
            if r[0] not in dist and len(r[0]) <= lim:
                dist[r[0]] = 0
                queue.append(r[0])
    print(f"{len(dist)} walls, {n} steps compared, {bad} differ")


if __name__ == "__main__":
    cmd, arg = sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 0
    f = {"bfs": bfs, "margin": margin, "orbit": orbit, "compare": compare, "runs": runs, "need": need}[cmd]
    t = threading.Thread(target=f, args=(arg,))
    t.start()
    t.join()
