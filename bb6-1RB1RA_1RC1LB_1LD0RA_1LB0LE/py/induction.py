"""Two tests of a first-block lower bound by induction (notes/LAB_NOTES.md, 1 November 2026).

`free`: the pass map with every block a real number and every parity chosen freely (the constants ±1, ±3, ±5 of the
closed form dropped, so a block of y ones contributes y/2 where the closed form has (y ± c)/2).  From [1, 2] (the
shape [a, 2a+1] scaled by a) it lists every list reachable in d passes, scaled to one in total, and reports the
smallest first block.  It halves every two passes: no statement made only of inequalities between block sizes can
be kept by the pass map, so an induction has to carry parities (2-adic digits).

`sentinel`: near a = 1 (a = 1 + 2^m u) the blocks of the excursion from [a, 2a+1] are congruent, modulo a power of
two that loses one bit per pass, to the orbit of the closed form from [1, 3] in which a block of 1 is not an event
(`loose`).  In that orbit the last block is 3 for ever ((3 + 3)/2 = 3) and adds 4 to the block before it each pass:
an inner counter [x, 2x+6, 3] with x growing by 12 every 9 passes.  So the deepest excursions are run by the same
map one level down, and the induction is self-similar rather than closing on a fixed set of shapes.

usage:
  python3 py/induction.py free D            the smallest first block / ones after 1..D free-parity passes
  python3 py/induction.py sentinel M N      a = 2^M + 1: check N passes against the sentinel orbit, print its returns
"""
import itertools
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import passmap  # noqa: E402


def free_step(y, par):
    """One pass of the real-valued closed form on y (first block first) with the parities par; None for a halt."""
    k = len(y)
    g = [0, 0] + list(y)

    def Y(i):
        return g[i + 1]

    if par[-1] == 0:
        add = y[-1] / 2
        out = [Y(i) for i in range(-1, k - 2)] + [Y(k - 2) + add, Y(k - 1) + add]
    else:
        j = k - 1
        while j >= 1 and par[j - 1] == 0:
            j -= 1
        if j == 0:
            return None
        h = {i: Y(i) / 2 for i in range(j + 1, k)}
        h[k] = y[-1] / 2
        out = [Y(i) for i in range(-1, j - 2)] + [Y(j - 2) + Y(j) / 2, Y(j - 1) + Y(j) / 2 + h[j + 1]]
        out += [h[i] + h[i + 1] for i in range(j + 1, k)] + [h[k]]
    while out and out[0] == 0:
        out.pop(0)
    return out


def free(depth, max_blocks=5):
    """The smallest first block (as a fraction of the ones) after each of 1..depth free-parity passes from [1, 2],
    over lists of at most max_blocks blocks (exact, with Fractions)."""
    frontier, mins = {(Fraction(1, 3), Fraction(2, 3))}, []
    for _ in range(depth):
        new = set()
        for y in frontier:
            if len(y) > max_blocks:
                continue
            for par in itertools.product((0, 1), repeat=len(y)):
                o = free_step(list(y), par)
                if o:
                    s = sum(o)
                    new.add(tuple(v / s for v in o))
        frontier = new
        mins.append(min(y[0] for y in frontier))
    return mins


def loose(y):
    """The closed form (py/passmap.py) with a stop at a block of 1 allowed (it leaves a block of 0) and the list kept
    at its length plus any new blocks (no leading zeros dropped)."""
    k = len(y)
    g = [0, 0] + list(y)

    def Y(i):
        return g[i + 1]

    j = passmap.stop_index(y)
    assert j >= 1, y
    if j == k:
        add = (y[-1] + 4) // 2
        return [Y(i) for i in range(-1, k - 2)] + [Y(k - 2) + add, Y(k - 1) + add]
    yj = Y(j)
    h = {i: Y(i) // 2 for i in range(j + 1, k)}
    h[k] = (y[-1] + 5) // 2
    out = [Y(i) for i in range(-1, j - 2)] + [Y(j - 2) + (yj - 1) // 2, Y(j - 1) + (yj + 1) // 2 + h[j + 1]]
    return out + [h[i] + h[i + 1] for i in range(j + 1, k)] + [h[k] - 1]


def sentinel(m, n, slack=12):
    """Run [a, 2a+1], a = 2^m + 1, and the loose orbit from [1, 3] side by side for n passes (n <= m - slack - 1):
    after pass t the blocks agree modulo 2^(m - t - slack).  Returns the loose orbit's two-block-plus-sentinel states
    [x, 2x+d, 3] as (pass, x, d)."""
    assert n <= m - slack - 1
    a = 2 ** m + 1
    y, e, inner = [a, 2 * a + 1], [1, 3], []
    for t in range(n):
        y, e = passmap.passmap(y), loose(e)
        assert isinstance(y, list), (t, y)
        assert len(e) >= len(y) and not any(e[:len(e) - len(y)]), (t, e, y)
        e = e[len(e) - len(y):]
        mod = 2 ** (m - t - slack)
        assert all((v - w) % mod == 0 for v, w in zip(y, e)), (t, y, e)
        assert e[-1] == 3, (t, e)
        if len(e) == 3:
            inner.append((t + 1, e[0], e[1] - 2 * e[0]))
    return inner


def main(argv):
    if not argv:
        print(__doc__)
    elif argv[0] == "free":
        for d, v in enumerate(free(int(argv[1])), 1):
            print(f"pass {d}: smallest first block / ones = {float(v):.6f} = {v}")
    elif argv[0] == "sentinel":
        m, n = int(argv[1]), int(argv[2])
        inner = sentinel(m, n)
        print(f"a = 2^{m} + 1: {n} passes agree with the sentinel orbit from [1, 3]")
        print("its states [x, 2x+d, 3] (pass, x, d):", inner[:40])
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
