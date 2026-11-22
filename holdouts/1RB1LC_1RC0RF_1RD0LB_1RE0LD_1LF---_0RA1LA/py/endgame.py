"""1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA: the level-2 phase map as one digit map, and where a level ends.

The digit map (lean/DigitMap.lean proves it is the walk of lean/Walk.lean):
    f(10a + d) = 31a + K[d // 2],  K = [15, 27, 47, 35, 36]
A state x stands for the phase end (n, r) = (10 + 31 (x // 10), (x % 10) // 2); one step of f is one phase (two for
r = 1, 2) and uses COST[r] = [4, 5, 8, 3, 2] words of the tail.  Every level starts at (17, 0, tl T s), which after
its first phase is the state x = 22 with T - 4 words: so every level runs a prefix of the same orbit
22, 697, 2162, ... of f, and stops at the first k with COST[r_k] > (words left); the near-empty and short-tail rows of
Walk.lean then decide what comes next.

usage: python3 endgame.py [KMAX]       (default 20000; about a minute)
  1. checks the digit map against the walk (walksim.py, read from Walk.lean) on random states, and that the last
     digits of an orbit are a bijective re-encoding of the start's digits;
  2. replays level 1 (budget 6801) and prints its end, as level1_end' proves;
  3. follows the orbit of 22 for KMAX steps: digit statistics, and for every budget the orbit can stop at
     (k from 2000 on, every words-left value) what the walk does next (halt / loop / the start of a new level);
  4. turns that into the heuristic chance that the machine halts, treating the budget of a new level as random.
"""
import random
import sys
import os
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import walksim as W

K = [15, 27, 47, 35, 36]
COST = [4, 5, 8, 3, 2]
LEN = [2, 3, 3, 2, 2]          # walk steps per step of f (reset, [reset,] periods)


def f(x):
    return 31 * (x // 10) + K[(x % 10) // 2]


def enc(x, s, t):
    return (10 + 31 * (x // 10), (x % 10) // 2, ("long", s, t))


def check(trials=20000):
    for _ in range(trials):
        x = random.randrange(10 ** random.randint(1, 40))
        s = random.choice(["s1", "s2", "s3"])
        r = (x % 10) // 2
        t = COST[r] + random.randrange(20)
        w = enc(x, s, t)
        for _ in range(LEN[r]):
            w = W.wstep(w)[1]
        assert w == enc(f(x), s, t - COST[r]), (x, t, w)
    w = (17, 0, ("long", "s2", 1000))
    w = W.wstep(W.wstep(w)[1])[1]
    assert w == enc(22, "s2", 996)
    print("digit map = walk on", trials, "random states; (17, 0, T) -> x = 22 with T - 4 words")


def bijection(kmax=4):
    """The last digits d_0..d_k of the orbit of x depend only on x mod 10^(k+1), and every list of k+1 digits comes
    from exactly one residue (31 is invertible mod 10^k): the orbit's last digits re-encode the start's digits."""
    for k in range(kmax + 1):
        M, seen = 10 ** (k + 1), set()
        for x in range(M):
            a, b, da, db = x, x + 7 * M, [], []
            for _ in range(k + 1):
                da.append(a % 10); db.append(b % 10); a, b = f(a), f(b)
            assert da == db
            seen.add(tuple(da))
        assert len(seen) == M
    print("last digits d_0..d_k of an orbit <-> start mod 10^(k+1), a bijection (k <= %d)" % kmax)


def level(budget, x=22):
    k = 0
    while COST[(x % 10) // 2] <= budget:
        budget -= COST[(x % 10) // 2]
        x = f(x)
        k += 1
    return k, x, budget


def after(x, s, t, cap=400):
    """Walk on from the state x with t words left (t below what its row needs) until halt, loop or a new level
    (a record (17, 0, tl T s') with T large).  Short-tail chains (level 0 and the third level) are followed exactly."""
    w = enc(x, s, t)
    for _ in range(cap):
        res = W.wstep(w)
        if res[0] != "go":
            return res[0]
        w = res[1]
        n, m, T = w
        if T[0] == "long" and T[2] > 60:
            assert (n, m) == (17, 0), w
            return "L" + T[1][1]
    return "cap"


def main():
    KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    check()
    bijection()
    k, x, t = level(6801)
    n = 10 + 31 * (x // 10)
    print("level 1 (budget 6801): stops after %d steps of f at r = %d, %d words left, n = %d mod 100, %d digits"
          % (k, (x % 10) // 2, t, n % 100, len(str(n))))
    x, C = 22, 0
    rc, dc = Counter(), Counter()
    out = {s: Counter() for s in ("s1", "s2", "s3")}
    for k in range(KMAX):
        r = (x % 10) // 2
        rc[r] += 1
        dc[(10 + 31 * (x // 10)) % 10] += 1
        if k >= 2000:
            for s in out:
                for tl in range(COST[r]):
                    out[s][(r, tl, after(x, s, tl))] += 1
        C += COST[r]
        x = f(x)
    print("orbit of 22, %d steps: r frequencies %s; n mod 10 frequencies %s; mean cost %.4f words/step"
          % (KMAX, [rc[i] for i in range(5)], [dc[i] for i in range(10)], C / KMAX))
    P = {}
    for s in ("s1", "s2", "s3"):
        tot = sum(out[s].values())
        agg = Counter()
        for (r, tl, o), c in out[s].items():
            agg[o] += c
        P[s] = {o: c / tot for o, c in agg.items()}
        print("end of a level with suffix %s (budgets stopping at k = 2000..%d, all weighted alike):" % (s, KMAX))
        for (r, tl) in sorted({(r, tl) for (r, tl, o) in out[s]}):
            row = {o: c for (rr, tt, o), c in out[s].items() if (rr, tt) == (r, tl)}
            print("   r=%d left=%d  %s" % (r, tl, ", ".join("%s %.3f" % (o, c / sum(row.values()))
                                                         for o, c in sorted(row.items()))))
        print("   total: %s" % ", ".join("%s %.4f" % (o, p) for o, p in sorted(P[s].items())))
    # absorption: h[s] = P(halt eventually | a level with suffix s starts with a random huge budget)
    h = {"s1": 0.0, "s2": 0.0, "s3": 0.0}
    for _ in range(10000):
        h = {s: P[s].get("halt", 0) + sum(p * h["s" + o[1]] for o, p in P[s].items() if o.startswith("L"))
             for s in h}
    print("heuristic chance of an eventual halt from the start of a level: %s"
          % ", ".join("%s %.4f" % (s, h[s]) for s in sorted(h)))


if __name__ == "__main__":
    main()
