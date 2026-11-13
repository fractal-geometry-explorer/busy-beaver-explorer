"""Sort the trips of 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC--- by the Lean theorem that covers them.

At every trip start (A at the left end) the run lengths r0 r1 x1 y1 x2 y2 ... are matched against the shapes of
lean/Counter.lean: `inc0`, `inc1`, or digit 0 at 2, digits at 2 (`carry_chain`) and a digit at 1 (`trip_stop1`) or at
0 (`trip_stop0`), with the minimum lengths those statements need.  Everything else is counted by where the match
failed (the carry reached the right end, a run too short, a digit with residues outside the table).  Also counts the
times D reads a 1, by the length k of the alternating stretch that ends at D's cell (a halt needs k = 1).

usage (from the repo root): python3 holdouts/1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---/py/classify.py STEPS
"""
import collections
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rsim import Sim, D  # noqa: E402


def classify(r):
    n = len(r)
    if n < 2:
        return "short"
    m = (r[0] % 4, r[1] % 4)
    if m == (0, 3):
        return "inc0" if r[0] >= 4 and r[1] >= 7 and n > 2 and r[2] >= 2 else "other: digit 0 too short"
    if m == (2, 2):
        return "inc1" if r[0] >= 6 and r[1] >= 6 else "other: digit 0 too short"
    if m != (3, 1):
        return "other: digit 0 residues"
    if r[0] < 7 or r[1] < 5:
        return "other: digit 0 too short"
    k = 2
    while True:
        if k + 1 >= n:
            return "other: carry reaches the right end"
        x, y = r[k], r[k + 1]
        if (x % 4, y % 4) == (1, 1):
            if x >= 9 and y >= 5:
                k += 2
                continue
            return "other: passed digit too short"
        if (x % 4, y % 4) == (0, 2):
            return "trip_stop1" if x >= 4 and y >= 6 else "other: stopping digit too short"
        if (x % 4, y % 4) == (2, 3):
            return "trip_stop0" if x >= 6 and y >= 7 and k + 2 < n and r[k + 2] >= 2 else "other: stopping digit too short"
        return "other: digit residues outside the table"


def main():
    n = float(sys.argv[1])
    s, trips, dk = Sim(), collections.Counter(), collections.Counter()
    while s.steps < n:
        if s.st == D and s.h == 1:
            if s.L:
                b, m = s.L[-1]
                k = 1 if (b ^ ((m - 1) & 1)) == s.h else 1 + m
            else:
                k = 1
            dk[min(k, 12)] += 1
        if not s.step():
            print("HALT after", s.steps + 1, "steps")
            return
        if s.at_left():
            trips[classify(s.runs())] += 1
    tot = sum(trips.values())
    print(f"{s.steps} steps, {tot} trips")
    for k, v in trips.most_common():
        print(f"  {k}: {v} ({100 * v / tot:.3f}%)")
    print("D reads a 1, by stretch length k (12 = 12 or more):", dict(sorted(dk.items())))


if __name__ == "__main__":
    main()
