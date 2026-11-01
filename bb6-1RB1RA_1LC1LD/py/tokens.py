"""`pre` (lean/Formula.lean) seen from its A states: two words at a time, and the tokens it carries.

At an A state with no ones under the head (`A`, `h = 0`), `pre` reads words `0 1^k` to its right.  Between two such
states it always eats exactly the first two words.  Call a word other than `0 1 1` (a 2) *irregular*, and count the
*tokens*: irregular words plus nonzero blocks to the left.  Observed on random good lists (`check`):

* Only the pair `1, 2` writes new words; then what it writes ends in a word 3 in place of the 2 (or nothing), so the
  irregular word in front moves one word to the right, and every new irregular word lies to its left.  Every other
  pair (`2 2`, `2 1`, `2 3`, `3 2`, `3 1`, `3 3`) writes nothing.
* The token count never goes up, except by exactly 1 on a step where the tape grows at the left end (the converter
  passes the leftmost block and starts a block 2 further left).

usage:
  python3 py/tokens.py check SEED COUNT      the two facts on COUNT random good lists
  python3 py/tokens.py climb N SEED          hill climb for a list of N blocks with many growth steps
"""
import os
import random
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import macro  # noqa: E402


def trim(L):
    L = list(L)
    while L and L[-1] == 0:
        L.pop()
    return L


def run(ls, fuel=10 ** 6):
    """The configurations of `pre` from `ls` (blocks nearest first), as `macro.pre` runs them, with `u`."""
    q, h, L, W, u = "B", 0, list(ls[:1] or [0]) + list(ls[1:]), [0, 1], 0
    out = []
    for _ in range(fuel):
        out.append((q, h, list(L), list(W), u))
        if q == "A" and h == 0 and all(w == 2 for w in W):
            return out
        if not W or (q == "C" and W == [1]):
            W, u = W + [2], u + 1
            continue
        r = macro.astep(q, h, L, W)
        if r is None or r == macro.HALT or r[0] == "pass":
            return None
        q, h, L, W = r
    return None


def width(c):
    """Cells from the leftmost block to the right end, without the supply words taken."""
    q, h, L, W, u = c
    return sum(b + 1 for b in trim(L)) + h + sum(W) + len(W) - 3 * u


def tokens(c):
    return sum(1 for w in c[3] if w != 2) + len(trim(c[2]))


def a_states(ls):
    return [c for c in run(ls) if c[0] == "A" and c[1] == 0]


def check(seed, count):
    """Counts of pairs eaten and of (token change, growth); a list of exceptions (empty if both facts hold)."""
    rnd = random.Random(seed)
    pairs, moves, bad = Counter(), Counter(), []
    for _ in range(count):
        ls = [rnd.randint(2, rnd.choice([5, 8, 12, 30])) for _ in range(rnd.randint(1, 12))]
        A = a_states(ls)
        for c, d in zip(A, A[1:]):
            W = c[3] + [2] * (d[4] - c[4])
            R, W2 = W[2:], d[3]
            pair = tuple(W[:2])
            pairs[pair] += 1
            if pair != (1, 2):
                ok = W2 == R
            else:
                n = len(W2) - len(R)
                ok = n >= 0 and W2[n:] == R and (n == 0 or W2[n - 1] == 3)
            dt, g = tokens(d) - tokens(c), width(d) - width(c)
            moves[(dt, g > 0)] += 1
            if not ok or dt > (1 if g > 0 else 0) or g < 0:
                bad.append((ls, c, d))
    return pairs, moves, bad


def growth(ls):
    A = a_states(ls)
    return sum(1 for c, d in zip(A, A[1:]) if width(d) > width(c)), max(width(c) for c in run(ls)) - width(run(ls)[0])


def climb(n, seed, restarts=10, steps=300):
    rnd = random.Random(seed)
    best, bs = None, (-1, 0)
    for _ in range(restarts):
        ls = [rnd.randint(2, 30) for _ in range(n)]
        s = growth(ls)
        for _ in range(steps):
            l2 = list(ls)
            i = rnd.randrange(n)
            l2[i] = max(2, l2[i] + rnd.choice([-6, -3, -2, -1, 1, 2, 3, 6]))
            s2 = growth(l2)
            if s2 >= s:
                ls, s = l2, s2
        if s > bs:
            bs, best = s, ls
    return bs, best


def main(argv):
    if argv and argv[0] == "check":
        pairs, moves, bad = check(int(argv[1]), int(argv[2]))
        print("pairs eaten:", dict(pairs))
        print("(token change, tape grew):", dict(moves))
        print("exceptions:", len(bad))
        for b in bad[:5]:
            print("  ", b)
    elif argv and argv[0] == "climb":
        (g, d), ls = climb(int(argv[1]), int(argv[2]))
        print(f"{g} growth steps, head {d} cells past the left end: {ls}")
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
