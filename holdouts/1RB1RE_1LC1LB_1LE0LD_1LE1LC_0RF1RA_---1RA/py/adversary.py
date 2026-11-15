"""Could ANY sequence of parities empty the stack?  A search over the epoch map of
1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA with the parity of m left free.

At an epoch start the tape is [6, 4, u^m, L].  For m large the next stack L' depends only on L and on the parity of m
(checked here for two sizes and for m, m+2 at every node of the breadth-first search).  The real run picks one
parity per epoch; this search follows both, from the stack L0 = 4 u^17 4 u^3 4 1 of the run at step 181,417.
A halt of the machine from any reachable (L, parity) would be printed as HALT.  The search is not exhaustive (the
set of stacks is infinite), so finding no halt is evidence, not a proof.

usage: python3 adversary.py bfs DEPTH          breadth first, all stacks
       python3 adversary.py best N             best first by number of runs, N expansions
       python3 adversary.py sample DEPTH CAP   breadth first keeping CAP random stacks per level; statistics
"""
import sys, os, heapq, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from runstack import Sim, B

BIG = 4 * 10 ** 9
L0 = ((4, 1), (1, 17), (4, 1), (1, 3), (4, 1), (1, 1))


def f(L, p, big=BIG):
    """L: tuple of (run, count), left to right.  One epoch from [6, 4, u^(big+p), L]: (L', m') or ('HALT', None)."""
    s = Sim(); s.st = B; s.d = -1
    s.R = [list(e) for e in reversed(L)] + [[1, big + p], [4, 1], [6, 1]]
    first = True; n = 0
    while True:
        if s.at_visit():
            R = s.R
            if not first and len(R) >= 3 and R[-1] == [6, 1] and R[-2] == [4, 1] and R[-3][0] == 1 and R[-3][1] > big:
                return tuple(tuple(e) for e in reversed(R[:-3])), R[-3][1]
            first = False
            s.sweep()
        if not s.step(): return 'HALT', None
        n += 1
        if n > 10 ** 6: return 'LOOP', None


def nruns(L): return sum(m for l, m in L)
def nodd(L): return sum(m for l, m in L if l % 2)
def fm(L): return ' '.join(str(l) if m == 1 else "%d^%d" % (l, m) for l, m in L)


def bfs(depth):
    seen = {L0}; fr = [L0]
    for d in range(1, depth + 1):
        nf = []
        for L in fr:
            for p in (0, 1):
                r, m = f(L, p)
                if r in ('HALT', 'LOOP'): print(r, fm(L), p); continue
                assert f(L, p + 2, 10 ** 7)[0] == r
                if r not in seen: seen.add(r); nf.append(r)
        fr = nf
        print("depth", d, "new", len(fr), "seen", len(seen), "fewest runs", min(map(nruns, fr)), flush=True)


def best(N):
    seen = {L0}; h = [(nruns(L0), L0)]; n = 0; lo = L0
    while h and n < N:
        k, L = heapq.heappop(h); n += 1
        if k < nruns(lo): lo = L
        for p in (0, 1):
            r, m = f(L, p)
            if r in ('HALT', 'LOOP'): print(r, fm(L), p); continue
            if r not in seen: seen.add(r); heapq.heappush(h, (nruns(r), r))
    print("expanded", n, "seen", len(seen), "| smallest stack met:", fm(lo))


def sample(depth, cap):
    random.seed(1); seen = {L0}; fr = [L0]
    for d in range(depth):
        nf = []
        for L in fr:
            for p in (0, 1):
                r, m = f(L, p)
                if isinstance(r, str): print(r, fm(L), p); continue
                if r not in seen: seen.add(r); nf.append(r)
        fr = random.sample(nf, cap) if len(nf) > cap else nf
    print("stacks seen", len(seen), "| fewest odd runs", min(map(nodd, seen)), "| last run always odd:",
          all(L[-1][0] % 2 for L in seen), "| a run of length 2 occurs:", any(l == 2 for L in seen for l, m in L),
          "| fewest runs", min(map(nruns, seen)))


if __name__ == "__main__":
    a = [int(x) for x in sys.argv[2:]]
    {"bfs": bfs, "best": best, "sample": sample}[sys.argv[1]](*a)
