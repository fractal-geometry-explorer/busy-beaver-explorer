"""Chance-of-a-hit heuristic for 1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD (see the README).

The machine halts iff the orbit of (7, 1, 0) under the sample map reaches H (Lean: lean/MapThm.lean, halts_iff),
and H can only come at the end of a chain of C steps with s = 0, when the chain uses up the pairs exactly.  If the
remainder x at the end of a chain (0 <= x < h, h = (m+5)/2) were uniform, the chain would have hit H with chance
about 1/h.  This sums 1/h over the chains of the orbit and prints the running sum and the size of x by round, and
the spread of the remainders x/h over tenths.

usage (from the repository root): python3 holdouts/1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD/py/heuristic.py ROUNDS
"""
import collections, sys


def inv(h):
    """1/h as a float, also for huge h."""
    b = h.bit_length()
    return 1.0 / h if b < 1000 else 2.0 ** (-(b - 1)) / (h >> (b - 53)) * 2 ** 52


def ratio(x, h):
    b = h.bit_length()
    if b < 1000:
        return x / h
    return (x >> (b - 60)) / (h >> (b - 60))


def run(rounds):
    x, m, s, r = 7, 1, 0, 0
    acc, inchain = 0.0, False
    tenths = collections.Counter()
    marks = {}
    while r < rounds:
        if m % 2 == 0:
            if x >= 1:                       # a whole B phase at once
                m += 4 * x; s ^= x & 1; x = 0
                continue
            x, m, s = (m + 6) // 2, (1 if s == 0 else 3), 0   # R
            r += 1
            marks[r] = (acc, x.bit_length())
            continue
        if x == 0:
            print("the map reaches H in round", r)
            return
        h = (m + 5) // 2
        if x >= h and s == 0:                # C with s = 0: the chain goes on
            x, m, inchain = x - h, 2 * m + 7, True
            continue
        if inchain:                          # the chain ended with remainder x < h
            acc += inv(h)
            tenths[int(10 * ratio(x, h))] += 1
            inchain = False
        if x >= h:
            x, m = x - h, 2 * m + 7 - s      # C with s = 1
        elif x == h - 1 and s == 0:
            x, m, s = 2 * x + 3, 1, 0        # A'
        else:
            x, m, s = 2 * x + 1, m - 2 * x + 4, 1 - s   # A
    for k in sorted(marks):
        if k in (1, 2, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000) or k == rounds:
            print(f"round {k}: x has {marks[k][1]} bits, sum of 1/h so far {marks[k][0]:.9g}")
    print("remainders x/h at chain ends, by tenth:", dict(sorted(tenths.items())))


if __name__ == "__main__":
    run(int(sys.argv[1]))
