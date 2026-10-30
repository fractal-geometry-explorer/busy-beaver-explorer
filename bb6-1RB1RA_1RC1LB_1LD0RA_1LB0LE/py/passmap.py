"""The passes of 1RB1RA_1RC1LB_1LD0RA_1LB0LE_1LF1LD_---0LD as a map on lists of block lengths.

A pass starts with the head in A on the blank cell just right of the visited part of the tape, and the tape is
`1^y1 0 1^y2 0 ... 0 1^yk A>0` (blocks of ones separated by single 0s).  The pass writes three ones on the right,
then D and E run left writing 0 and 1 in turn (the sweep), crossing into the next block on the left whenever E
reaches a separating 0, until D reaches one; then A, B and C zigzag back to the right end (notes/LAB_NOTES.md).
Left of y1 the tape is blank, read as empty blocks y0 = y-1 = 0.

`passmap(y)` is the conjectured closed form of one pass; `run_pass(y)` runs the machine on the tape of `y` until the
next pass start (or a halt) and reads the block list off.  Tests compare them (tests/test_machine.py).

usage:
  python3 py/passmap.py orbit N        the first N pass starts from blank tape, from the closed form
  python3 py/passmap.py stats N        N passes: block counts, the 2-block states [a, 2a+d], smallest stop block
  python3 py/passmap.py check N K      N random block lists of length <= K: closed form against the machine
"""
import collections
import random
import sys

M = "1RB1RA_1RC1LB_1LD0RA_1LB0LE_1LF1LD_---0LD"

# (write, move, next) for each (state, symbol); None halts.  A..F = 0..5.
TABLE = {}
for _q, _tr in enumerate(M.split("_")):
    for _r in (0, 1):
        _x = _tr[3 * _r:3 * _r + 3]
        TABLE[(_q, _r)] = None if _x[0] == "-" else (int(_x[0]), 1 if _x[1] == "R" else -1, ord(_x[2]) - 65)

HALT = "HALT"
FIRST = [2, 2]          # the first pass start, step 17: 1^2 0 1^2 A>0 (lean/Blank.lean, `blank_at_17`)


def stop_index(y):
    """For a pass from y: the 1-based index j of the block whose left 0 D reaches, 0 if the sweep runs off the left
    end (a halt).  The last block is crossed if odd; then blocks are crossed while even."""
    k = len(y)
    if y[-1] % 2 == 0:
        return k
    j = k - 1
    while j >= 1 and y[j - 1] % 2 == 0:
        j -= 1
    return j


def passmap(y):
    """The block list at the next pass start, HALT, or None where the closed form is not known (a stop block of 1).

    b = y_k even, m = b/2:   ... y_(k-2) + m+2,  y_(k-1) + m+2
    b odd, stop at j < k:    ... y_(j-2) + (y_j - 1)/2,  y_(j-1) + (y_j + 1)/2 + h_(j+1),  h_(j+1) + h_(j+2), ...,
                             h_(k-1) + h_k,  h_k - 1      with h_i = y_i/2 (even blocks) and h_k = (b + 5)/2
    """
    y = list(y)
    k = len(y)
    if k == 0:
        return None
    g = [0, 0] + y                       # g[i + 1] = y_i for i = -1 .. k

    def Y(i):
        return g[i + 1]

    j = stop_index(y)
    if j == 0:
        return HALT
    if j == k:
        add = (y[-1] + 4) // 2
        out = [Y(i) for i in range(-1, k - 2)] + [Y(k - 2) + add, Y(k - 1) + add]
    else:
        yj = Y(j)
        if yj == 1:
            return None
        h = {i: Y(i) // 2 for i in range(j + 1, k)}
        h[k] = (y[-1] + 5) // 2
        out = [Y(i) for i in range(-1, j - 2)] + [Y(j - 2) + (yj - 1) // 2, Y(j - 1) + (yj + 1) // 2 + h[j + 1]]
        out += [h[i] + h[i + 1] for i in range(j + 1, k)] + [h[k] - 1]
    while out and out[0] == 0:
        out.pop(0)
    return out


def tape_of(y):
    cells = []
    for i, b in enumerate(y):
        if i:
            cells.append(0)
        cells += [1] * b
    return cells


def run_pass(y, max_steps=10 ** 7):
    """Run the machine from `1^y1 0 ... 1^yk A>0` (blank around) to the next C on a 0 at the right end, then back up
    to its pass start.  Returns (block list or HALT, steps, clean): clean is False if the tape at the pass start is not
    blocks separated by single 0s.  None if max_steps run out."""
    t = dict(enumerate(tape_of(y)))
    h, q, n = len(y) and sum(y) + len(y) - 1, 0, 0
    hi = h
    while n < max_steps:
        r = t.get(h, 0)
        tr = TABLE[(q, r)]
        if tr is None:
            return HALT, n + 1, True
        if q == 2 and r == 0 and n > 2:
            if h < hi:
                raise AssertionError(f"C on a 0 inside the tape from {y}")
            # the pass start was two steps ago: A>0 at h - 2
            t[h - 1] = t[h - 2] = 0
            lo = min(i for i, v in t.items() if v)
            s = "".join(str(t.get(i, 0)) for i in range(lo, h - 2))
            return [len(p) for p in s.split("0")], n - 2, "00" not in s
        w, d, q = tr
        t[h] = w
        h += d
        n += 1
        hi = max(hi, h)
    return None


def orbit(n, y=FIRST):
    y = list(y)
    for _ in range(n):
        yield y
        y = passmap(y)
        if not isinstance(y, list):
            yield y
            return


def stats(n):
    kc, two = collections.Counter(), collections.Counter()
    min_stop = None
    last = None
    for i, y in enumerate(orbit(n)):
        if not isinstance(y, list):
            print("event", i, y)
            break
        kc[len(y)] += 1
        if len(y) == 2:
            two[y[1] - 2 * y[0]] += 1
        j = stop_index(y)
        if j < len(y) and i > 50 and (min_stop is None or y[j - 1] < min_stop[0]):
            min_stop = (y[j - 1], i)
        last = y
    print("passes", n, "last sum", sum(last), "blocks", len(last))
    print("block counts", sorted(kc.items()))
    print("2-block states [a, 2a+d], d:", sorted(two.items()))
    print("smallest stop block after pass 50 (size, pass):", min_stop)


def check(n, k, seed=1):
    rnd = random.Random(seed)
    tried = skipped = 0
    for _ in range(n):
        y = [rnd.randint(1, 12) for _ in range(rnd.randint(1, k))]
        want = passmap(y)
        if want is None:
            skipped += 1
            continue
        got, _, clean = run_pass(y)
        assert got == want and clean, (y, want, got)
        tried += 1
    return tried, skipped


def main(argv):
    if not argv:
        print(__doc__)
    elif argv[0] == "orbit":
        for i, y in enumerate(orbit(int(argv[1]))):
            print(i, sum(y) if isinstance(y, list) else "", y)
    elif argv[0] == "stats":
        stats(int(argv[1]))
    elif argv[0] == "check":
        print("agree on %d lists, %d skipped (stop block 1)" % check(int(argv[1]), int(argv[2])))
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
