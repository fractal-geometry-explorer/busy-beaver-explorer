"""Real trip starts of 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC--- with their long runs made as short as possible.

Every run of length >= T is replaced by the smallest length >= T with the same residue mod 4 (runs shorter than T are
kept); each distinct shortened list is run on the exact simulator for MOVES accelerated moves.  Counts the lists
that halt and prints the one with the fewest cells for each T.

usage (from the repo root): python3 holdouts/<M>/py/minimal_test.py STEPS MOVES T [T ...]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rsim import Sim  # noqa: E402
import runs as R  # noqa: E402
from monitor import canon  # noqa: E402


def main():
    steps, moves = float(sys.argv[1]), int(sys.argv[2])
    s, trips = Sim(), []
    while s.steps < steps:
        s.step()
        if s.at_left():
            trips.append(canon(s.runs()))
    for T in [int(x) for x in sys.argv[3:]]:
        seen, h, best = set(), 0, None
        for r in trips:
            q = tuple(x if x < T else T + (x - T) % 4 for x in r)
            if q in seen:
                continue
            seen.add(q)
            sim = R.start(list(q))
            halted = None
            for _ in range(moves):
                if not sim.step():
                    halted = sim.steps + 1
                    break
            if halted:
                h += 1
                if best is None or (sum(q), q) < best[:2]:
                    best = (sum(q), q, halted, r)
        print(f"T = {T}: {len(seen)} distinct shortened lists, {h} halt", flush=True)
        if best:
            print(f"   fewest cells: {list(best[1])} ({best[0]} cells), halts at step {best[2]}; from the real {best[3]}",
                  flush=True)


if __name__ == "__main__":
    main()
