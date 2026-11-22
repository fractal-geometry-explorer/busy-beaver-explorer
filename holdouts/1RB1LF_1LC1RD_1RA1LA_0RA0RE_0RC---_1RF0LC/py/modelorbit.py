"""The orbit of the integer counter-stack model of 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC, checked against the
hypothesis of `not_halts_of_model` (lean/Model.lean).

lean/Model.lean proves: if along the orbit of `mstepN` (= stepN of stackmodel.py) from the wall K(2) and N = 48
(the step start the run from blank tape reaches at step 10,206) every step answers, N stays >= 5 and no K(0) appears
anywhere but directly on the pile of K'(0)s, then the machine never halts.  The kernel checks the first 50,000 steps
(`model_first`); this script runs the same recursion further, with Python integers.  Every step of the orbit takes
more than N steps of the machine (`part1` alone takes 5(N - 5) + 695), so T steps without a failure mean no halt in
the first N_(T-1) > 2^(bits of N_T - 2) steps.

It also reports the least ratio k_upper / k_lower over two open counters next to each other.

usage: python3 modelorbit.py STEPS
"""
import math
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from stackmodel import stepN  # noqa: E402

sys.setrecursionlimit(10000)


def okO(lv):
    """Every K(0) has only K'(0)s below it (lists bottom first, as in stackmodel.py)."""
    for i, (k, closed) in enumerate(lv):
        if k == 0 and not closed and any(x != (0, True) for x in lv[:i]):
            return False
    return True


def run(T):
    lv, N, t0, minr, maxlen = [(2, False)], 48, time.time(), None, 1
    for i in range(1, T + 1):
        r = stepN(lv, N)
        if r is None or r[1] < 5 or not okO(r[0]):
            print(f"the hypothesis fails at step {i}: wall {lv}, N mod 2 = {N % 2}")
            return
        lv, N = r
        maxlen = max(maxlen, len(lv))
        for a in range(len(lv) - 1):
            (j, cj), (k, ck) = lv[a], lv[a + 1]
            if j > 0 and not cj and not ck and (minr is None or k / j < minr):
                minr = k / j
        if i % 100000 == 0:
            print(f"{i} steps: N has {N.bit_length()} bits, at most {maxlen} items, {time.time() - t0:.0f} s", flush=True)
    digits = int((N.bit_length() - 2) * math.log10(2))
    print(f"{T} steps: the hypothesis holds; N has {N.bit_length()} bits (no halt in the first 10^{digits} steps); "
          f"at most {maxlen} items; least ratio of two adjacent open counters {minr}")


if __name__ == "__main__":
    run(int(sys.argv[1]))
