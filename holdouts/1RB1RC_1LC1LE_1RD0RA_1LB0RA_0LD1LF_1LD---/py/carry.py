"""Checks the carry rule of the counter list against the exact simulation (blocksim.py), visit by visit.

The tape at a visit (A at the right end, on blank) is  0^inf P (10)^c1 s1 (10)^c2 s2 ... s(m-1) (10)^cm A>
with separators s_i in {0, 1}.  The carry starts at the last counter, i = m:
  * s(i-1) = 0 and c_i even: c(i-1) loses 1, stop;
  * s(i-1) = 0 and c_i odd: go on with i - 1;
  * s(i-1) = 1: the separator becomes 0, and c_i loses 1 if c_i is even, c(i-1) loses 1 if c_i is odd; stop;
and in every case c_m gains 3.  Visits where a counter is 0, or the carry passes the first counter, or the shape
changes, are counted as skipped (they are the rare events described in the README).

usage: python3 carry.py SECONDS
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from blocksim import BlockSim

M = "1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---"


def counters(b):
    items = b.norm.merge(b.norm.flatten(b.cfg.left[1:]))
    pre, rest = (items[0], items[1:]) if isinstance(items[0], str) else ("", items)
    cs, seps = rest[0::2], rest[1::2]
    if not all(isinstance(c, int) for c in cs) or not all(s in ("0", "1") for s in seps):
        return None
    return pre, cs, seps


def predict(cs, seps):
    cs, seps = list(cs), list(seps)
    i = len(cs) - 1
    while i > 0:
        if seps[i - 1] == "1":
            seps[i - 1] = "0"
            cs[i if cs[i] % 2 == 0 else i - 1] -= 1
            cs[-1] += 3
            return cs, seps
        if cs[i] % 2 == 0:
            cs[i - 1] -= 1
            cs[-1] += 3
            return cs, seps
        i -= 1
    return None


def main(secs):
    b = BlockSim(M, "10", "A", "R")
    b.next_visit()
    prev = counters(b)
    t0, n, ok, bad, skip = time.time(), 0, 0, 0, 0
    while time.time() - t0 < secs:
        b.next_visit()
        n += 1
        cur = counters(b)
        p = predict(prev[1], prev[2]) if prev and cur and len(prev[1]) == len(cur[1]) and min(prev[1]) > 0 else None
        if p is None:
            skip += 1
        elif p == (cur[1], cur[2]) and prev[0] == cur[0]:
            ok += 1
        else:
            bad += 1
            print("BAD", prev, cur, p)
        prev = cur
    print(f"visits {n} (to step {b.steps}): rule holds {ok}, fails {bad}, events skipped {skip}")


if __name__ == "__main__":
    main(float(sys.argv[1]))
