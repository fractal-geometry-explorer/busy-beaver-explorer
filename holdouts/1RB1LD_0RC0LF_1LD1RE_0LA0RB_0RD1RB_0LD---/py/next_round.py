"""How the next round's count compares with this round's near the stop (exact visit-law simulation).

usage: python3 py/next_round.py [ROUNDS]       (default 6000; about 40 seconds)

Runs the visit law exactly (Python integers, every block of every round with its kind, visits and what it is
left as), then looks at rounds whose row ends in `100` followed by j blocks `000` and the stop. If the next round's
block reading into that `100` is a doubling block (`1010` or `0010`), it sends c visits along j + 1 halving blocks,
and the block at F-1 gets floor(c / 2^j). A dirty stop there needs exactly 1, and danger needs c not a power of 2
(`lean/Shift.lean`, README "The next round's blocks, and the dirty stop"). The script prints, for each j, the values
of floor(c / 2^j) that occur and the difference between the next round's count n_X at the doubling block and this
round's count n_o at the `100`.
"""
import sys
from collections import Counter


def run(R):
    N = 10 * R + 100
    off = 2 * R + 10
    t = [0] * (N + off)
    t[off] = 1
    rounds = []
    for r in range(1, R + 1):
        s = off - 2 * r
        t[s] = 1
        t[s + 1] = 0
        p, n, bl = s, 1, []
        while n > 0:
            a, b, c, d = t[p:p + 4]
            if (a, b, c) == (0, 0, 0):
                typ, out, m, L = "000", ([1, 0, 0] if n % 2 else [0, 0, 0]), n // 2, 3
            elif (a, b, c) in ((1, 0, 0), (1, 1, 0)):
                typ, out, m, L = "%d%d0" % (a, b), ([0, 0, 0] if n % 2 else [1, 0, 0]), (n + 1) // 2, 3
            elif (a, b, c) == (0, 1, 0):
                typ, L = "010", 3
                out, m = ([1, 1, 0], 0) if n == 1 else (([0, 0, 0] if n % 2 == 0 else [1, 0, 0]), n // 2)
            elif (a, b, c, d) == (1, 0, 1, 0):
                typ, out, m, L = "1010", [1, 0, 1, 0], 2 * n, 4
            elif (a, b, c, d) == (0, 0, 1, 0):
                typ, out, m, L = "0010", [1, 0, 1, 0], 2 * (n - 1), 4
            else:
                raise SystemExit("round %d meets %s: not one of the clean blocks" % (r, (a, b, c, d)))
            t[p:p + L] = out
            bl.append((p - off, L, typ, n, "".join(map(str, out))))
            p += L
            n = m
        rounds.append(bl)
    return rounds


def main(R):
    rounds = run(R)
    C = Counter()
    for r in range(len(rounds) - 1):
        A = rounds[r]
        outs = [b[4] for b in A]
        k, j = len(outs) - 2, 0
        while k >= 0 and outs[k] == "000":
            j, k = j + 1, k - 1
        if k < 0 or outs[k] != "100":
            continue
        o = A[k][0]
        x = [b for b in rounds[r + 1] if b[0] < o < b[0] + b[1]]
        if not x or x[0][2] not in ("1010", "0010"):
            continue
        x = x[0]
        c = 2 * x[3] if x[2] == "1010" else 2 * (x[3] - 1)
        q = c >> j
        C[(min(j, 3), q if q < 4 else 4, x[3] - A[k][3])] += 1
    print("j (3 = 3 or more), floor(c/2^j) (4 = 4 or more), n_X - n_o : rounds")
    for key in sorted(C):
        print("  j=%d  floor(c/2^j)=%d  n_X-n_o=%+d : %d" % (key + (C[key],)))


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 6000)
