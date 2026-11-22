"""What follows the region Z_k, n < 12k + 12, by direct simulation.

    python3 exit_survey.py follow K0 K1        every region start with K0 <= k < K1, E-event by E-event, until a
                                             tail of the proved map (1, X, Y, Z outside the region) or a halt;
                                             counts, and the shapes of the tail words met on the way
    python3 exit_survey.py suffix              the X/Y/Z rules with an end word W after the tail: is W passive?
"""
import os
import re
import sys
from collections import Counter
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from emap import nxt, parse, step, word  # noqa: E402
import emap  # noqa: E402,F401  (puts g01tools on the path)
import g01tools as g  # noqa: E402


def shape(T):
    return re.sub(r"\^\d+", "^*", g.compress(T))


def follow(arg):
    k, n = arg
    T, shapes = word("Z", k), []
    for p in range(200):
        r = nxt(T, n, 10**12)
        if r is None:
            return k, n, "TIMEOUT", p, shapes
        if r[0] == "HALT":
            return k, n, "HALT", p + 1, shapes
        T, n = r[0], r[1]
        pr = parse(T)
        if pr and not (pr[0] == "Z" and n < 12 * pr[1] + 12):
            return k, n, "MAP", p + 1, shapes
        shapes.append(shape(T))
    return k, n, "LONG", 200, shapes  # the starts n = 2: Z_k -> Z_(k+1) at n = 2 forever


if __name__ == "__main__":
    if sys.argv[1] == "follow":
        K0, K1 = int(sys.argv[2]), int(sys.argv[3])
        res, maxp, allsh = Counter(), Counter(), Counter()
        with Pool(3) as P:
            for k, n, kind, p, sh in P.imap_unordered(follow, [(k, n) for k in range(K0, K1) for n in range(12 * k + 12)],
                                                      chunksize=8):
                res[kind] += 1
                maxp[kind] = max(maxp[kind], p)
                allsh.update(set(sh))
                if kind == "HALT":
                    print("halt", k, n, "after", p, "passes", flush=True)
        print(dict(res), "largest number of passes:", dict(maxp))
        print(len(allsh), "shapes of tail words on the way:")
        for s, c in allsh.most_common():
            print(c, s)
    elif sys.argv[1] == "suffix":
        for f in "XYZ":
            for W in ["0001", "000101", "0000001"]:
                same = cnt = 0
                for k in (0, 1, 2, 3, 5, 8):
                    lo = 12 * k + 12 if f == "Z" else 0
                    for n in range(lo, lo + 40):
                        p = step(f, k, n)
                        d = nxt(word(f, k) + W, n, 10**9)
                        cnt += 1
                        same += d is not None and d[0] != "HALT" and (d[0], d[1]) == (word(p[0], p[1]) + W, p[2])
                print(f"tail {f} followed by {W}: the map's next event with {W} still after it in {same} of {cnt}")
