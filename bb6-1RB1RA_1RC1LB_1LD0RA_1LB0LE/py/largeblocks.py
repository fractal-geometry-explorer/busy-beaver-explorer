"""Large blocks: how many blocks are at least ones/2^c, along the orbit, and the lists of lean/Large.lean.
(notes/LAB_NOTES.md, 1 November 2026, "Bound the number of large blocks".)

The idea was that the orbit keeps few large blocks, with the extra ones a small tail, and that this with psi would rule
out the long halving runs of lean/Run7.lean, whose lists have seven blocks of comparable size.  The orbit does keep
few: at most 5 blocks of at least ones/32 in the passes run.  But adding 2^8 * V (psi(V) = 0) to the lists of Run7
gives lists of the orbit's shape, at most 5 large blocks at every pass start, that still reach a first block of 1.

usage:
  python3 py/largeblocks.py orbit N      the most blocks >= ones/2^c along passes 51..N of the blank orbit, c = 1..12
  python3 py/largeblocks.py loose N      the same along the sentinel orbit from [1, 3] (py/blockcount.py)
  python3 py/largeblocks.py witness      the passes of WL and WLB with their large-block counts
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import passmap  # noqa: E402
from blockcount import loose_step  # noqa: E402
from invsearch import psi  # noqa: E402
from runbound import W7  # noqa: E402

W7B = [255, 1280, 2304, 2432, 5464, 10594, 6507]
V = [0, 993, 3400, 3300, 1000, 128, 32]          # psi(V) = 0, first entry 0: the orbit's shape [1, 3.4, 3.3, 1] + tail
WL = [a + 2 ** 8 * b for a, b in zip(W7, V)]     # [31, 254304, 870464, 844832, 256088, 32930, 8427]
WLB = [a + 2 ** 8 * b for a, b in zip(W7B, V)]   # [255, 255488, 872704, 847232, 261464, 43362, 14699]


def large(c, y):
    """The number of blocks of y that are at least 1/2^c of its ones (lean/Large.lean, `large`)."""
    s = sum(y)
    return sum(1 for v in y if s <= 2 ** c * v)


def most_large(lists, cs=range(1, 13), skip=50):
    """{c: (most blocks >= ones/2^c, first pass index with it)} over the lists after index `skip`."""
    best = {c: (0, None) for c in cs}
    for i, y in enumerate(lists):
        if i <= skip:
            continue
        for c in cs:
            n = large(c, y)
            if n > best[c][0]:
                best[c] = (n, i)
    return best


def orbit_lists(n):
    return passmap.orbit(n)


def loose_lists(n, y=(1, 3)):
    y = list(y)
    for _ in range(n):
        yield y
        y = loose_step(y)


def profile(y, max_passes=100):
    """(first block, block count, large at ones/16, large at ones/32) per pass start until a stop at a block of 1;
    returns (rows, end) with end the value of the closed form after the last row (None for a stop at a block of 1)."""
    rows = []
    for _ in range(max_passes):
        rows.append((y[0], len(y), large(4, y), large(5, y)))
        y = passmap.passmap(y)
        if not isinstance(y, list):
            return rows, y
    return rows, y


def main(argv):
    if not argv:
        print(__doc__)
    elif argv[0] in ("orbit", "loose"):
        lists = orbit_lists(int(argv[1])) if argv[0] == "orbit" else loose_lists(int(argv[1]))
        for c, (m, i) in most_large(lists).items():
            print(f"blocks >= ones/2^{c}: at most {m} (first at pass {i})")
    elif argv[0] == "witness":
        for name, y in (("WL", WL), ("WLB", WLB)):
            rows, end = profile(y)
            print(name, y, "psi", psi(y), "ones", sum(y))
            for r in rows:
                print("  first %d  k %d  large/16 %d  large/32 %d" % r)
            print("  then:", "stop at a block of 1" if end is None else end)
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
