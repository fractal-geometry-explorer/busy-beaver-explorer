"""1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA: statistics of the exact orbit of 22 (from orbitfast.py).

usage: python3 orbitstats.py OUT [LMAX]
  reads OUT.r and OUT.lo written by orbitfast.py and prints
  1. r frequencies, the mean cost (words of the tail per step) and the walk W(k) - 4.4 k of the words used;
  2. for every block length L <= LMAX: the chi-square of the counts of all 5^L blocks of r values against uniform,
     and how many blocks never occur, against the number a random sequence would miss (Poisson);
  3. at every sampled step k (x_k mod 10^20 is exact there) and every number of words left below what the step needs:
     what the walk does if a level ended there (endgame.after: halt / loop / a new level), for each suffix, and the
     heuristic chance of an eventual halt chained over levels (as endgame.py, on far more of the orbit).
Everything here is a measurement of one fixed sequence; none of it is a proof.
"""
import math
import os
import sys
from collections import Counter

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import endgame as E

COST = np.array([4, 5, 8, 3, 2], dtype=np.int64)


def blocks(r, LMAX):
    n = len(r)
    out = []
    for L in range(1, LMAX + 1):
        nb = 5 ** L
        cnt = np.zeros(nb, dtype=np.int64)
        CH = 1 << 24
        for s in range(0, n - L + 1, CH):
            e = min(n - L + 1, s + CH)
            code = np.zeros(e - s, dtype=np.int64)
            for j in range(L):
                code = code * 5 + r[s + j:e + j]
            cnt += np.bincount(code, minlength=nb)
        N = n - L + 1
        exp = N / nb
        chi = float(((cnt - exp) ** 2).sum() / exp)
        df = nb - 1
        z = (chi - df) / math.sqrt(2 * df)
        missing = int((cnt == 0).sum())
        out.append((L, nb, chi, df, z, missing, nb * math.exp(-exp), int(cnt.min()), int(cnt.max())))
    return out


def main():
    base = sys.argv[1]
    LMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    r = np.frombuffer(open(base + ".r", "rb").read(), dtype=np.uint8).astype(np.int64)
    n = len(r)
    fr = np.bincount(r, minlength=5)
    c = COST[r]
    W = np.cumsum(c)
    D = W - 4.4 * np.arange(1, n + 1)
    sig = float(np.std(np.array([4, 5, 8, 3, 2])))       # 2.059 per step if r were uniform and independent
    print("orbit of 22, %d steps (exact)" % n)
    print("  r frequencies: %s  (%s)" % (fr.tolist(), ", ".join("%.4f%%" % (100 * v / n) for v in fr)))
    print("  mean cost %.6f words/step (uniform: 4.4); W(n) - 4.4 n = %.0f = %.2f sigma*sqrt(n); max |W(k) - 4.4 k| "
          "= %.0f at k = %d" % (W[-1] / n, D[-1], D[-1] / (sig * math.sqrt(n)), abs(D).max(), int(abs(D).argmax())))
    for p in range(3, 10):
        k = 10 ** p
        if k <= n:
            print("     k = 10^%d: W - 4.4k = %+.0f (%+.2f sigma sqrt k)" % (p, D[k - 1], D[k - 1] / (sig * math.sqrt(k))))
    print("  blocks of r values (L, 5^L, chi^2, df, z, blocks never seen, expected unseen if random, min, max count):")
    for row in blocks(r, LMAX):
        print("     L=%d  %8d  chi2 %12.1f  df %8d  z %+6.2f  unseen %7d (random: %9.1f)  min %d max %d" % row)
    # end-of-level outcomes at the sampled steps
    los = [tuple(map(int, l.split())) for l in open(base + ".lo")]
    los = [(k, v) for k, v in los if k >= 2000]
    agg = {s: Counter() for s in ("s1", "s2", "s3")}
    unsure = Counter()
    for k, v in los:
        rr = (v % 10) // 2
        for s in agg:
            for tl in range(E.COST[rr]):
                o1 = E.after(v + 10 ** 20 * 7777777, s, tl)
                o2 = E.after(v + 10 ** 20 * 123456789123, s, tl)
                if o1 != o2:
                    unsure[s] += 1
                agg[s][o1] += 1
    P = {}
    for s in agg:
        tot = sum(agg[s].values())
        P[s] = {o: cc / tot for o, cc in agg[s].items()}
        print("  end of a level with suffix %s, %d samples (%d decided by more than 20 digits): %s"
              % (s, tot, unsure[s], ", ".join("%s %.4f" % (o, p) for o, p in sorted(P[s].items()))))
    h = {"s1": 0.0, "s2": 0.0, "s3": 0.0}
    for _ in range(10000):
        h = {s: P[s].get("halt", 0) + sum(p * h["s" + o[1]] for o, p in P[s].items() if o.startswith("L"))
             for s in h}
    print("  heuristic chance of an eventual halt from the start of a level: %s"
          % ", ".join("%s %.4f" % (s, h[s]) for s in sorted(h)))


if __name__ == "__main__":
    main()
