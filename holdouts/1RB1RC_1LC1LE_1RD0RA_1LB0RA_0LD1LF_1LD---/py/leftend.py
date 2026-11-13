"""The left end of the counter list over a long run (exact simulation, blocksim.py): prints a line whenever the
prefix or the first counter changes: visit, step, number of counters m, tape length, the first items.

usage: python3 leftend.py SECONDS
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from blocksim import BlockSim
from bbtools.symtm import Halted

M = "1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---"


def main(secs):
    b = BlockSim(M, "10", "A", "R")
    t0, n, prev = time.time(), 0, None
    while time.time() - t0 < secs:
        try:
            b.next_visit()
        except Halted as e:
            print("HALT", e, b.steps)
            return
        n += 1
        items = b.norm.merge(b.norm.flatten(b.cfg.left[1:]))
        if items[:2] != prev:
            ints = [x for x in items if isinstance(x, int)]
            cells = 2 * sum(ints) + sum(len(x) for x in items if isinstance(x, str))
            head = " ".join(x if isinstance(x, str) else "(10)^%d" % x for x in items[:4])
            print(n, b.steps, "m=%d" % len(ints), "cells=%d" % cells, head, flush=True)
        prev = items[:2]
    print("visits", n, "steps", b.steps)


if __name__ == "__main__":
    main(float(sys.argv[1]))
