"""Orbit-only structure: the ancestry of block lists, and the jumps of the return map (notes/LAB_NOTES.md, 1 November).

`preimages(z)` lists every block list y with passmap(y) == z, the exact inverse of the closed form in py/passmap.py.
A pass that stops at block j >= 3 leaves y_j = 2s + 1 free, so a list has many preimages (about a third of the ones on the orbit, 159 for w7): the
backward tree branches in the hundreds, and "has a long ancestry" is no constraint (only the root [2, 2] is).

`skips(D)` runs the class search of py/returnmap.py to depth D and returns, for every route that jumps k >= 2, the
2-adic valuations v2(a + 12j - 1) of the values it skips, and the valuations v2(a - 1) of the open classes.  The jumps
never skip a value = 1 mod 32 and the open classes are all = 1 mod 256: the counter passes through every value that
could fail (lean/Visit.lean proves it for every a).

usage:
  python3 py/ancestry.py preimages N     preimage counts of the orbit's pass N and of the halving lists
  python3 py/ancestry.py skips D         the valuations above, classes to mod 2^(D+2)
"""
import collections
import os
import random
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import passmap as pm  # noqa: E402
import returnmap  # noqa: E402
from passmap import passmap  # noqa: E402


def _tail(z, t):
    """h_(k-t+1) .. h_k from the last t entries of z, or None if some block would be < 1 (h_k >= 3)."""
    L = len(z)
    h = [0] * t
    h[t - 1] = z[L - 1] + 1
    if h[t - 1] < 3:
        return None
    for i in range(t - 2, -1, -1):
        h[i] = z[L - t + i] - h[i + 1]
        if h[i] < 1:
            return None
    return h


def preimages(z):
    z = list(z)
    L = len(z)
    out = []
    # even last block
    if L == 2 and z[0] == z[1] and z[0] >= 3:
        out.append([2 * (z[0] - 2)])
    if L == 2 and z[0] >= 3 and z[1] - z[0] >= 1:
        out.append([z[1] - z[0], 2 * (z[0] - 2)])
    if L >= 2:
        for m in range(1, min(z[-1], z[-2]) - 2):
            out.append(z[:-2] + [z[-2] - m - 2, z[-1] - m - 2, 2 * m])
    # odd last block, tail of t blocks after the stop block
    for t in range(1, L - 1):
        h = _tail(z, t)
        if h is None:
            continue
        ys = [2 * x for x in h[:-1]] + [2 * h[-1] - 5]
        A, B = z[L - t - 2], z[L - t - 1]
        P = z[:L - t - 2]
        if not P:
            # j = 1: y1 = 2A + 1 (A >= 1 so y1 >= 3), B = A + 1 + h_2
            if B == A + 1 + h[0]:
                out.append([2 * A + 1] + ys)
            # j = 2: y2 = 2A + 1, y1 = B - A - 1 - h_3
            y1 = B - A - 1 - h[0]
            if y1 >= 1:
                out.append([y1, 2 * A + 1] + ys)
        # j >= 3: prefix P = y_1 .. y_(j-3); y_j = 2s + 1
        for s in range(1, A):
            ym1 = B - s - 1 - h[0]
            if ym1 < 1:
                break
            out.append(P + [A - s, ym1, 2 * s + 1] + ys)
    return [y for y in out if passmap(y) == z]


def check_inverse(n=3000, seed=1):
    """y is among the preimages of passmap(y), for n random lists."""
    r = random.Random(seed)
    for _ in range(n):
        y = [r.randint(1, 40) for _ in range(r.randint(1, 7))]
        z = passmap(y)
        if isinstance(z, list):
            assert y in preimages(z), (y, z)
    return True


HALVING = {  # the lists of lean/Run7.lean and lean/BigFront.lean, first block first
    "w7": [31, 96, 64, 32, 88, 162, 235],
    "wF": [255, 512, 32, 60, 32, 64, 9],
    "wH": [255, 528, 48, 24, 8, 32, 64, 128, 129],
}


def v2(x):
    return (x & -x).bit_length() - 1


def skips(depth):
    """(skipped, open): Counter of v2(a + 12j - 1) over the skipped values of every leaf class with k >= 2 (the
    valuation is the class's own, so 'undetermined' if it reaches the modulus), and Counter of v2(a - 1) over the
    open classes."""
    leaves, open_, _, bad = returnmap.explore(lambda a: [a, 2 * a + 1], [returnmap.Aff(1, 4)],
                                              returnmap.two_block(1), depth + 2)
    assert not bad
    skipped = collections.Counter()
    for (ends, _), cl in leaves.items():
        k = ends[0] // 12
        for a, _ in cl:
            m = a.q.bit_length() - 1
            for j in range(1, k):
                v = v2(a.p + 12 * j - 1)
                skipped[v if v < m else "undetermined"] += 1
    return skipped, collections.Counter(v2(a.p - 1) for a in open_ if a.p > 1)


def open34():
    """The 67 open residues mod 2^34 of lean/Thin.lean."""
    src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean", "Thin.lean")).read()
    return [int(x) for x in re.findall(r"\d+", src.split("def open34 : List Nat := [")[1].split("]")[0])]


def open_jumps(n, seed=3):
    """G on n random members a >= 5 of the open residue classes mod 2^34: Counter of k, and how many jumps skip a
    value = 1 mod 32."""
    r, L = random.Random(seed), open34()
    ks, bad = collections.Counter(), 0
    for _ in range(n):
        a = r.choice(L) + 2 ** 34 * r.getrandbits(r.choice([10, 30, 60, 100]))
        if a < 5:
            continue
        g, _, _ = returnmap.G(a)
        k = (g - a) // 12
        ks[k] += 1
        bad += any((a + 12 * j) % 32 == 1 for j in range(1, k))
    return ks, bad


def main(argv):
    if len(argv) == 2 and argv[0] == "preimages":
        orbit = list(pm.orbit(int(argv[1]) + 1))
        print("orbit pass", argv[1], len(preimages(orbit[-1])))
        for name, z in HALVING.items():
            print(name, len(preimages(z)))
    elif len(argv) == 2 and argv[0] == "skips":
        sk, op = skips(int(argv[1]))
        print("v2(a + 12j - 1) of skipped values:", sorted(sk.items(), key=str))
        print("v2(a - 1) of open classes:", sorted(op.items()))
        print("open-class jumps (k, count), and skips of 1 mod 32:", *open_jumps(2000))
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
