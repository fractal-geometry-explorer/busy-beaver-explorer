"""Runs of passes that leave the first block alone: how many front stops psi allows in one, by block count.
(notes/LAB_NOTES.md, 1 November 2026, "A second invariant beside psi?")

A pass *changes* the first block (`invsearch.changes_first`) if it stops at the second block, at the third of a
longer list, or has an even last block on 2 or 3 blocks. Between two changes the first block is only halved, by front
stops, so a stop at a first block of 1 at the end of R front stops needs the first block to have been 2^R - 1 after
the last change (the Mersenne lemma). In such a run a front stop adds a block and every other pass removes one, and
front stops never come two in a row (`front_twice`), so the block count stays at most k0 + 1, k0 the count after
the change. So the (k, psi, f) graph bounds R from the state after the change alone, with no cap on the block count.

usage:
  python3 py/runbound.py table W        the most front stops in a run, for k0 = 2..6 and |psi| <= W at the change
  python3 py/runbound.py cycles W       cyclic parts of the run graph from k0 = 7, 8, 9, |psi| <= W
  python3 py/runbound.py witness        the 7-block list of lean/Run7.lean, pass by pass
  python3 py/runbound.py second N       the rule of `front_second` on N random front stops
  python3 py/runbound.py ratio N        the largest y2 / (y1 + 1) along the first N passes of the blank orbit (after 50)
"""
import functools
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import passmap  # noqa: E402
from invsearch import changes_first, psi, step_state  # noqa: E402

W7 = [31, 96, 64, 32, 88, 162, 235]     # first block first; lean/Run7.lean has it nearest first


def run_moves(s):
    """The passes from (k, psi, f) that do not change the first block: (j, next state)."""
    k, p, f = s
    for j in ([k] if p % 2 == 0 else range(1, k)):
        if (j == 1 and f) or changes_first(k, j):
            continue
        k2, p2 = step_state(k, p, j)
        yield j, (k2, p2, j == 1)


def run_bound(k0, p0):
    """The most front stops on a path of `run_moves` from (k0, p0) right after a change (finite for k0 <= 6)."""
    assert k0 <= 6
    sys.setrecursionlimit(20000)

    @functools.lru_cache(None)
    def best(s):
        assert s[0] <= k0 + 1
        return max([best(t) + (j == 1) for j, t in run_moves(s)], default=0)

    return best((k0, p0, False))


def table(W):
    out = {}
    for k0 in range(2, 7):
        vals = {p: run_bound(k0, p) for p in range(-W, W + 1)}
        out[k0] = (max(vals.values()), max(v for p, v in vals.items() if abs(p) <= 60))
    return out


def cyclic_parts(W, ks=(7, 8, 9)):
    """Strongly connected parts with more than one state, reached from (k, psi, False), k in ks, |psi| <= W."""
    starts = [(k, p, False) for k in ks for p in range(-W, W + 1)]
    E, stack, seen = {}, list(starts), set(starts)
    while stack:
        s = stack.pop()
        E[s] = [t for _, t in run_moves(s)]
        for t in E[s]:
            if t not in seen:
                seen.add(t)
                stack.append(t)
    # Kosaraju: order by finish time, then sweep the reversed graph
    order, done = [], set()
    for v in E:
        if v in done:
            continue
        done.add(v)
        st = [(v, iter(E[v]))]
        while st:
            u, it = st[-1]
            w = next(it, None)
            if w is None:
                order.append(u)
                st.pop()
            elif w not in done:
                done.add(w)
                st.append((w, iter(E[w])))
    rev = {v: [] for v in E}
    for v in E:
        for w in E[v]:
            rev[w].append(v)
    comp, parts = {}, []
    for v in reversed(order):
        if v in comp:
            continue
        part, st = [], [v]
        comp[v] = v
        while st:
            u = st.pop()
            part.append(u)
            for w in rev[u]:
                if w not in comp:
                    comp[w] = v
                    st.append(w)
        if len(part) > 1:
            parts.append(sorted(part))
    return parts


def trace(y, max_passes=100):
    """(first block, k, psi, j) pass by pass until the event, a change of the first block or max_passes."""
    out = []
    for _ in range(max_passes):
        k, j = len(y), passmap.stop_index(y)
        out.append((y[0], k, psi(y), j))
        if changes_first(k, j):
            return out, "change"
        y = passmap.passmap(y)
        if y is None:
            return out, "stop at a block of 1"
        if y == passmap.HALT:
            return out, "halt"
    return out, "max"


def check_second(n, seed=1):
    """front_second: on a front stop of >= 3 blocks, y1' = (y1 - 1)/2 and y2' = (y1 + 1)/2 + y2/2."""
    rnd = random.Random(seed)
    for _ in range(n):
        k = rnd.randint(3, 9)
        y = [2 * rnd.randint(1, 500) + 1] + [2 * rnd.randint(1, 500) for _ in range(k - 2)] + [2 * rnd.randint(0, 500) + 1]
        z = passmap.passmap(y)
        assert z[0] == (y[0] - 1) // 2 and z[1] == (y[0] + 1) // 2 + y[1] // 2, (y, z)
        assert z[1] * (y[0] + 1) == (y[1] + y[0] + 1) * (z[0] + 1)      # y2/(y1+1) goes up by exactly 1
    return n


def max_ratio(n):
    best = (0, None)
    for i, y in enumerate(passmap.orbit(n)):
        if i > 50 and len(y) > 1 and y[1] / (y[0] + 1) > best[0]:
            best = (y[1] / (y[0] + 1), i)
    return best


def main(argv):
    if not argv:
        print(__doc__)
    elif argv[0] == "table":
        for k0, (m, m60) in table(int(argv[1])).items():
            print(f"k0 = {k0}: at most {m} front stops in a run (|psi| <= {argv[1]}), {m60} for |psi| <= 60")
    elif argv[0] == "cycles":
        for part in cyclic_parts(int(argv[1])):
            ks = sorted({s[0] for s in part})
            ps = [s[1] for s in part]
            print(f"cyclic part: {len(part)} states, k in {ks}, psi {min(ps)}..{max(ps)}, "
                  f"front stops: {sum(1 for s in part if s[2])}")
    elif argv[0] == "witness":
        out, end = trace(W7)
        for row in out:
            print("first %d  k %d  psi %d  j %d" % row)
        print(end)
    elif argv[0] == "second":
        print("front_second holds on", check_second(int(argv[1])), "random front stops")
    elif argv[0] == "ratio":
        print("largest y2/(y1+1) after pass 50 (value, pass):", max_ratio(int(argv[1])))
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
