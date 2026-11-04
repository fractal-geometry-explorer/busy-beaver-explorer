"""The first block: where a stop block of 1 can be, and how far the first block falls along the blank-tape orbit.

`lean/Front.lean` proves, for the pass map `next` of `lean/Pass.lean` (the closed form of `py/passmap.py`):

* `Good`: every block after the first is at least 2 (the first at least 1); the pass map keeps it, so on the orbit a
  sweep can stop at a block of 1 only at the first block, after crossing every other one (`one_front`);
* with 4 | ones, two passes in a row never both stop at the first block (`front_twice`).

So the stop block of 1 needs the first block to fall to 1.  The first block falls only when a sweep stops at it or at
the second block (it halves, or becomes about half the second block); every other pass keeps it or makes it larger.
This script measures the falls along the orbit: a *descent* is a maximal stretch of passes over which the first block
never grows, and its depth is the number of passes in it that stop at the first block (each halves it).  To reach 1
from f a descent needs about log2(f) of them.

usage:
  python3 py/front.py stats N       N passes from blank tape: Good on every list, no two front stops in a row, the
                                    descents by depth, the deepest one, the smallest first block / ones after pass 50
  python3 py/front.py loop          the halving loop that the small starts use to reach the event (examples)
"""
import collections
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import passmap  # noqa: E402


def good(y):
    """Every block after the first is at least 2, the first at least 1."""
    return bool(y) and y[0] >= 1 and all(b >= 2 for b in y[1:])


def front_stop(y):
    """The sweep crosses every block but the first and stops at it."""
    return len(y) >= 2 and passmap.stop_index(y) == 1


def stats(n):
    y = list(passmap.FIRST)
    depths = collections.Counter()
    depth, start, deepest = 0, None, None
    prev_front = False
    min_ratio = None
    for i in range(1, n + 1):          # y is pass i (pass 0 is blank tape)
        assert good(y), (i, y)
        fs = front_stop(y)
        assert not (fs and prev_front), (i, y)
        prev_front = fs
        if i > 50 and (min_ratio is None or y[0] / sum(y) < min_ratio[0]):
            min_ratio = (y[0] / sum(y), i, y[0], sum(y))
        z = passmap.passmap(y)
        assert isinstance(z, list), (i, y, z)
        if z[0] < y[0]:
            if start is None:
                start = (i, y[0])
            depth += fs
        elif z[0] > y[0] and start is not None:
            depths[depth] += 1
            if deepest is None or depth > deepest[0] or (depth == deepest[0] and z[0] and start[1] / y[0] > deepest[3]):
                deepest = (depth, start, (i, y[0]), start[1] / y[0])
            depth, start = 0, None
        y = z
    return depths, deepest, min_ratio


LOOP_EXAMPLES = ([110, 63, 23], [34, 31, 7])


def main(argv):
    if not argv:
        print(__doc__)
    elif argv[0] == "stats":
        n = int(argv[1])
        depths, deepest, min_ratio = stats(n)
        print(f"passes 1..{n}: Good on every list, no two front stops in a row")
        print("descents of the first block by depth (front stops in it):", sorted(depths.items()))
        (d, (i0, f0), (i1, f1), r) = deepest
        print(f"deepest: {d} front stops, first block {f0} at pass {i0} down to {f1} at pass {i1} (/{r:.2f})")
        print("smallest first block / ones after pass 50: %.4f at pass %d (%d of %d)" % min_ratio)
    elif argv[0] == "loop":
        for y in LOOP_EXAMPLES:
            z = y
            while isinstance(z, list):
                print(passmap.stop_index(z), z)
                z = passmap.passmap(z)
            print("->", z, "(stop block 1)\n")
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
