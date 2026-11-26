"""Failed counts that halt: configurations of the wall-stack form of 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC that
halt (plain simulation in C, c/haltscan.c).  See README, "A failed count can halt (26 November)", and
lean/Halting.lean, which proves the first one for every odd N >= 252.

A step start is  W A> 0 b^N 1  (b = 110) with W = 1 X_1 ... X_n, K(k) = b^k 1^3 b 1 (walls bottom first here).

usage (from this directory):
  python3 failhalt.py wall LO HI      the N in [LO, HI) for which 1 K(24) K(7) K(1) A> 0 b^N 1 halts
  python3 failhalt.py triples A C E   walls 1 K(a) K(c) K(e) (a < A, c < C, e < E; c, e odd) on which the model
                                      fails under an odd signal: which halt (N = 61), against the counts the model
                                      would give without its check for negative counts
  python3 failhalt.py lower           the same over 21 other lower stacks (N = 101)
  python3 failhalt.py small A C N     walls 1 K(a) K(c) with a block of fewer than N copies: which halt
"""
import collections
import os
import subprocess
import sys
import tempfile
import threading

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import stackmodel as S  # noqa: E402

sys.setrecursionlimit(100000)
b = '110'


def build():
    exe = os.path.join(tempfile.gettempdir(), 'h3292_haltscan')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(HERE, '..', 'c', 'haltscan.c')], check=True)
    return exe


def halting(cfgs, limit, procs=4):
    """cfgs: (wall word, N).  -> {(wall, N): steps} for those that halt within `limit` steps."""
    exe = build()
    lines = [f"{w} A {'0' + b * N + '1'}" for w, N in cfgs]
    outs = [None] * procs

    def run(i):
        outs[i] = subprocess.run([exe, str(limit)], input='\n'.join(lines[i::procs]) + '\n', capture_output=True,
                                 text=True, check=True).stdout
    th = [threading.Thread(target=run, args=(i,)) for i in range(procs)]
    [t.start() for t in th]
    [t.join() for t in th]
    res = {}
    for o in outs:
        for line in o.splitlines():
            f = line.split()
            if f[0] == 'HALT':
                res[(f[2], (len(f[4]) - 2) // 3)] = int(f[1])
    return res


def name(lv):
    return '1 ' + ' '.join(("K'" if p else 'K') + f'({k})' for k, p in lv)


def formal(lv):
    """The new counts of the two top counters (both open, both odd) under an odd signal, as the model computes them
    but without its check for negative counts; None when the signal does not pass through both."""
    V = lv[:-2]
    (c, pc), (e, pe) = lv[-2], lv[-1]
    if pc or pe or e % 2 == 0 or c % 2 == 0:
        return None
    r = S.step(V, 1)
    if r is None:
        return None
    c2 = 3 * c // 2 + r[1]
    return c2, 3 * e // 2 - (c2 - c) + r[2]


def table(walls, N_of, limit):
    cfgs, info = [], {}
    for lv in walls:
        if S.step(lv, 1) is not None:
            continue
        f = formal(lv)
        if f is None:
            continue
        w = S.word(lv)
        cfgs.append((w, N_of(w)))
        info[w] = (lv, f)
    h = halting(cfgs, limit)
    hw = {w for w, _ in h}
    allc, haltc = collections.Counter(), collections.Counter()
    for w, _ in cfgs:
        allc[info[w][1]] += 1
        if w in hw:
            haltc[info[w][1]] += 1
    print(f"{len(cfgs)} walls on which the model fails (top two counters open and odd, odd signal); {len(hw)} halt")
    print("new counts (middle, top) the model would give, for the halting ones:", dict(haltc))
    print("walls with new counts (-2, -2):", allc[(-2, -2)], "of which halt:", haltc[(-2, -2)])
    for w in sorted(hw, key=len)[:14]:
        print("  halts:", name(info[w][0]))


def wall(lo, hi):
    w = S.word([(24, False), (7, False), (1, False)])
    h = halting([(w, N) for N in range(lo, hi)], 30000 * hi)
    ns = sorted(N for _, N in h)
    print(f"1 K(24) K(7) K(1), N in [{lo}, {hi}): halts for N =", ns)
    print("all odd N in the range:", ns == [N for N in range(lo, hi) if N % 2 == 1])


def triples(A, C, E):
    walls = [[(a, False), (c, False), (e, False)] for a in range(A) for c in range(1, C, 2) for e in range(1, E, 2)]
    table(walls, lambda w: 61, 500000)


def lower():
    bottoms = ([[]] + [[(z, p)] for z in range(8) for p in (False, True)]
               + [[(0, True), (0, True)], [(0, True), (0, False)], [(3, False), (17, False)], [(2, False), (10, True)]])
    walls = [V + [(a, pa), (c, False), (e, False)] for V in bottoms for a in range(70) for pa in (False, True)
             for c in range(1, 40, 2) for e in range(1, 12, 2)]
    table(walls, lambda w: 101, 600000)


def small(A, C, NN):
    cfgs = [(S.word([(a, False), (c, False)]), N) for a in range(A) for c in range(C) for N in range(NN)]
    h = halting(cfgs, 300000)
    print(f"{len(cfgs)} configurations 1 K(a) K(c) A> 0 b^N 1 (a < {A}, c < {C}, N < {NN}); {len(h)} halt within 300,000 steps")
    for (w, N), t in sorted(h.items(), key=lambda x: x[1]):
        print(f"  {name(S.unword(w))}, N = {N}: halts after {t} steps")


if __name__ == '__main__':
    cmd, args = sys.argv[1], [int(x) for x in sys.argv[2:]]
    {'wall': wall, 'triples': triples, 'lower': lower, 'small': small}[cmd](*args)
