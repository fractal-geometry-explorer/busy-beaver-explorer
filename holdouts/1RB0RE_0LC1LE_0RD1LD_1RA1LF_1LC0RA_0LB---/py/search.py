"""Free-residue search for 1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB--- (see phases.py).

usage: python3 search.py [LEN]      (default 40)

Breadth-first over the words D reachable from the first phase start from blank tape, each phase with any residue
Z mod 4, keeping words of at most LEN cells; prints how many there are and every (D, Z mod 4) that halts.
"""
import sys
from collections import deque

from phases import BLANK, build, phase, short


def main():
    build()
    lim = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    start = BLANK[0][1]
    seen, q, halts, pruned = {start}, deque([start]), [], 0
    while q:
        d = q.popleft()
        for r in range(4):
            v = phase(d, 1000 + r)
            if v[0] == "halt":
                halts.append((d, r))
                continue
            if len(v[0]) > lim:
                pruned += 1
            elif v[0] not in seen:
                seen.add(v[0])
                q.append(v[0])
    print(f"{len(seen)} words of at most {lim} cells reachable with free residues; {pruned} steps left that bound")
    print("halting (D, Z mod 4):", [(short(d), r) for d, r in halts[:20]], len(halts))


if __name__ == "__main__":
    main()
