"""Is the block count bounded along excursions?  (notes/LAB_NOTES.md, 1 November 2026, "The block count is not
bounded by 6".)

The reduction of 1 November needs every list of the blank orbit to have at most 6 blocks.  This finds excursions
from [a, 2a+1] with 7, by following the "sentinel" orbit: for a = 1 + 2^m u the excursion agrees, modulo a power of
two that loses one bit per pass, with the closed form run from [1, 3] with a stop at a block of 1 allowed
(`loose`), and that orbit reaches 6 blocks with odd psi at pass 202, which the classes split only to mod 2^66 cannot
see.  The witness a = 2^203 + 2^221 + 1 (a = 5 mod 12) has 7 blocks after 204 passes; `lean/Seven.lean` proves it.

usage:
  python3 py/blockcount.py witness          the passes of the witness excursion, with (k, psi, j)
  python3 py/blockcount.py powers R         a = 2^r + 1 for r < R: the excursions with 7 or more blocks
  python3 py/blockcount.py loose N          the loose orbit from [1, 3]: first pass with each block count, to N passes
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import passmap  # noqa: E402
from invsearch import psi  # noqa: E402

WITNESS = 2 ** 203 + 2 ** 221 + 1


def excursion(a, max_passes=10 ** 6):
    """The pass starts from [a, 2a+1] up to the next [a', 2a'+1] (inclusive), or up to a halt / stop block of 1."""
    y, out = [a, 2 * a + 1], []
    for _ in range(max_passes):
        out.append(y)
        y = passmap.passmap(y)
        if not isinstance(y, list):
            out.append(y)
            return out
        if len(y) == 2 and y[1] - 2 * y[0] == 1:
            out.append(y)
            return out
    raise RuntimeError("long excursion")


def loose_step(y):
    """One pass of the closed form with a stop at a block of 1 allowed (it leaves an empty block, dropped here, as
    the zeros on the left are; `py/induction.py` in the first-block thread keeps them).  The sweep never reaches
    them on the orbit from [1, 3] in the range run (asserted)."""
    k = len(y)
    g = [0, 0] + list(y)

    def Y(i):
        return g[i + 1]

    j = passmap.stop_index(y)
    assert j >= 1, y
    if j == k:
        add = (y[-1] + 4) // 2
        out = [Y(i) for i in range(-1, k - 2)] + [Y(k - 2) + add, Y(k - 1) + add]
    else:
        yj = Y(j)
        h = {i: Y(i) // 2 for i in range(j + 1, k)}
        h[k] = (y[-1] + 5) // 2
        out = [Y(i) for i in range(-1, j - 2)] + [Y(j - 2) + (yj - 1) // 2, Y(j - 1) + (yj + 1) // 2 + h[j + 1]]
        out += [h[i] + h[i + 1] for i in range(j + 1, k)] + [h[k] - 1]
    while out and out[0] == 0:
        out.pop(0)
    return out


def loose_firsts(n):
    """{block count: (pass, list)} for the first time each count occurs in n passes of the loose orbit from [1, 3]."""
    y, first = [1, 3], {}
    for t in range(1, n + 1):
        y = loose_step(y)
        first.setdefault(len(y), (t, y))
    return first


def powers(r_max):
    out = []
    for r in range(4, r_max):
        ex = excursion(2 ** r + 1)
        assert isinstance(ex[-1], list)
        big = [t for t, y in enumerate(ex) if len(y) >= 7]
        if big:
            out.append((r, (2 ** r + 1) % 12, big[0], len(ex[big[0]])))
    return out


def main(argv):
    if not argv:
        print(__doc__)
    elif argv[0] == "witness":
        ex = excursion(WITNESS)
        for t, y in enumerate(ex[:-1]):
            print(t, len(y), psi(y), passmap.stop_index(y))
        print("returns after", len(ex) - 1, "passes to a +", ex[-1][0] - WITNESS)
    elif argv[0] == "powers":
        for row in powers(int(argv[1])):
            print("r = %d, a mod 12 = %d: %d blocks at pass %d" % (row[0], row[1], row[3], row[2]))
    elif argv[0] == "loose":
        for k, (t, y) in sorted(loose_firsts(int(argv[1])).items()):
            print(k, "blocks first at pass", t, "psi", psi(y), y)
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
