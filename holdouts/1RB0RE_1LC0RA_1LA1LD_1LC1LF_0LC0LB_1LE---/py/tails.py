"""The tail of 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE--- with the residues M mod 3 left free (see phases.py).

usage: python3 tails.py [RUNS]      (default 300; about 20 minutes, most of it for new tails' phases)

1. best-first search (by tail size, tails up to 40 cells) from the empty tail, each phase with any residue, until a
   halting (tail, residue) is reached; prints the path.  So halting is not excluded by the tail alone.
2. heuristic model: RUNS runs of 10,000 phases from the empty tail with independent uniform residues; counts halts.
"""
import heapq
import random
import sys

from phases import phase


def size(t):
    return sum(t) + len(t)


def search(lim=40):
    par, h = {(): None}, [(0, ())]
    while h:
        _, tl = heapq.heappop(h)
        for r in range(3):
            v = phase(300 + r, tl)
            if v[0] == "halt":
                path, x = [(tl, r)], tl
                while par[x]:
                    path.append(par[x])
                    x = par[x][0]
                return list(reversed(path))
            nt = v[1]
            if size(nt) <= lim and nt not in par:
                par[nt] = (tl, r)
                heapq.heappush(h, (size(nt), nt))
    return None


def main():
    runs = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    path = search()
    print(f"free residues: a halting tail is reached after {len(path)} phases:")
    print("  " + " ".join(f"{list(t)}/{r}" for t, r in path))
    random.seed(1)
    halts = 0
    for _ in range(runs):
        tl = ()
        for _ in range(10000):
            v = phase(300 + random.randrange(3), tl)
            if v[0] == "halt":
                halts += 1
                break
            tl = v[1]
    print(f"random residues: {halts} halts in {runs} runs of 10,000 phases")


if __name__ == "__main__":
    main()
