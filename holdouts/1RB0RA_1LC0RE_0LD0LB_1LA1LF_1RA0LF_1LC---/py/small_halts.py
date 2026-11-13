"""Do tapes that satisfy the README's digit table halt?  (1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---)

Enumerates trip starts `r0 r1 | x1 y1 | ... | xk yk` whose digit 0 and digits 1..k all have residues mod 4 from the
table (values 0, 1, 2 and their pending forms), with each run at one of its SHORT smallest admissible lengths
(r0 >= 4, r1 >= 5, y >= 5, x >= 1), and runs each one on the exact simulator until it halts or MOVES accelerated
moves pass.  Prints the number of halting tapes per k and the halting tape with the fewest cells.

usage (from the repo root): python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/small_halts.py [KMAX] [MOVES] [EXTRA]
EXTRA = how many lengths per run (1: only the smallest, 2: also + 4, ...).
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import runs as R  # noqa: E402

D0 = [(0, 3), (2, 2), (3, 1)]
DK = [(2, 3), (3, 3), (0, 2), (1, 2), (1, 1), (2, 1)]


def lens(res, lo, extra):
    first = lo + (res - lo) % 4
    return [first + 4 * i for i in range(extra)]


def fate(r, maxmoves):
    s = R.start(r)
    trips = 0
    for _ in range(maxmoves):
        if not s.step():
            return s.steps + 1, trips
        if s.at_left():
            trips += 1
    return None, trips


def main():
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    moves = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    extra = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    best = None
    for k in range(1, kmax + 1):
        n = h = 0
        for d0 in D0:
            for ds in itertools.product(DK, repeat=k):
                choices = [lens(d0[0], 4, extra), lens(d0[1], 5, extra)]
                for x, y in ds:
                    choices += [lens(x, 1, extra), lens(y, 5, extra)]
                for r in itertools.product(*choices):
                    r = list(r)
                    if R.canon(r) != r:
                        continue
                    n += 1
                    st, trips = fate(r, moves)
                    if st is not None:
                        h += 1
                        key = (sum(r), r)
                        if best is None or key < best[0]:
                            best = (key, st, trips)
        print(f"k = {k}: {h} of {n} tapes halt", flush=True)
    if best:
        print("fewest cells:", best[0][1], f"({best[0][0]} cells) halts at step {best[1]} after {best[2]} trips")


if __name__ == "__main__":
    main()
