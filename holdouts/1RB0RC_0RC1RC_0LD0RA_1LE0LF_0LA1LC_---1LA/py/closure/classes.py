"""The cheap first test: do neighbouring classes of the cycle's node halt?

The node is  <E> 0 (1011001)^P 1011 (0)^5 1101100110110 (011)^K 001101100110 (011)^r 0  with r = b + 2x free.  For P
near 59, K near 16 and both parities of r, the symbolic engine of accel.py runs until the head halts (then every r
of the class halts: the run never asked for the value of x), the run needs the value of x (undecided), or the budget
of moves is used up.  The real run is the class P = 59, K = 16, r odd, which returns to itself (cycle.py).

usage (from the repo root): python3 holdouts/1RB0RC_0RC1RC_0LD0RA_1LE0LF_0LA1LC_---1LA/py/closure/classes.py [MOVES]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import accel  # noqa: E402
import cycle  # noqa: E402
from accel import Driver, Undecided  # noqa: E402


def outcome(P, K, base, budget):
    claim = dict(cycle.CLAIM, base=base,
                 config=cycle.CLAIM["config"].replace("^59", "^%d" % P).replace("(011)^16", "(011)^%d" % K))
    s, start, idx = cycle.symbolic_start(claim)
    d = Driver(s, True)
    d.env = {0: 8398822}
    try:
        d.run(None, None, max_moves=budget)
    except Undecided as e:
        return "undecided after %d events (%s)" % (d.ev, e)
    if d.s.halt:
        return "HALTS for every r of the class, at event %d, step %r" % (d.ev, d.s.steps)
    return "no halt in %d moves (%d events)" % (d.moves, d.ev)


def main(argv):
    budget = int(argv[1]) if len(argv) > 1 else 2000000
    for P in (57, 58, 59, 60, 61):
        for K in (15, 16, 17):
            for base in (65, 64):
                print("P=%d K=%d r=%d+2x: %s" % (P, K, base, outcome(P, K, base, budget)), flush=True)


if __name__ == "__main__":
    main(sys.argv)
