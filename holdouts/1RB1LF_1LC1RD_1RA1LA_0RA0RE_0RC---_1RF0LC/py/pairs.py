"""Pairs of open counters of 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC and the 2-adic condition for a count to go
below 1 (free parities, the counter-stack model of stackmodel.py, proved in lean/Stack.lean where `stepRes` answers).

Items (bottom first here): K(k) open, K'(k) closed; P_a is a pile of a closed empty counters K'(0).  Under every
parity sequence (README, "Odd runs of a pair"):

* every K'(0) lies in one pile P_a at the bottom of the stack, and K(0) occurs only directly on it;
* new items are only ever put directly on the pile, so an open counter j with an open counter k directly above it
  has received only odd signals since it was put there as K(0): the stack from j down is Phi^m(P_a K(0)), where Phi
  is the answer of a stack to an odd signal (`step(V, 1)`) and m the number of signals it got;
* while the top k of the pair stays odd it passes odd signals down, and k_{t+1} = (3 k_t - 1)/2 + om(a, m + t),
  where om(a, s) is the amount the lower stack answers at its s-th odd signal.  So the run of k is an affine 3/2
  map driven by one fixed sequence, and k_t stays odd for t < J exactly when k_0 agrees with the 2-adic number
  rho(a, m) = 1 - sum_s (2/3)^(s+1) om(a, m + s) in its last J binary digits.

The certificate (`cert`): with theta_t the least k_0 for which k_t >= 1 (k_t is increasing in k_0 as long as the
parities agree), a start value k_0 reaches a count below 1 exactly when k_0 < max(theta_0..theta_r), r its run
length.  The k_0 with run length r form one residue class modulo 2^(r+1), so the largest bad k_0 below 2^B is found
in O(B) operations; a k_0 below 2^B with a run longer than B + 64 would have to be rho(a, m) mod 2^(B+64) itself
(reported as FLAG if that is below 2^B).

usage (from this directory):
  python3 pairs.py structure LIM       free-parity walls to LIM cells: the pile, the orbit position (a, m) of every
                                       pair, the smallest count put over a pile of height a, and whether every
                                       pair's top count is above the largest bad start value of its (a, m)
  python3 pairs.py creation A B [P]    runs from the moment a pair is made (m = 0), for every pile height a <= A:
                                       the largest bad k_0 below 2^B (to compare with 2^(a+2), the least count a pair
                                       over P_a is made with), P processes
  python3 pairs.py table A M B         the largest bad k_0 divided by the lower count j_m, for a <= A, m <= M
  python3 pairs.py rho a B             the first B binary digits of rho(a, 0) (lowest first), longest run of zeros
"""
import os
import sys
from collections import deque

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from stackmodel import step  # noqa: E402

sys.setrecursionlimit(100000)
EXTRA = 64


def base(a):
    return [(0, True)] * a + [(0, False)]


def orbit(a, n):
    """om(a, s) and the lower count j_s (the top of Phi^s(P_a K(0))) for s < n; None if a count goes below zero."""
    V, oms, tops = base(a), [], []
    for _ in range(n):
        tops.append(V[-1][0])
        r = step(V, 1)
        if r is None:
            return None
        V = r[0]
        oms.append(r[1])
    return oms, tops


def rho(oms, m, T):
    Mod = 1 << (T + 3)
    i3, p, acc = pow(3, -1, Mod), 1, 0
    for s in range(T + 2):
        p = p * 2 * i3 % Mod
        acc = (acc + p * oms[m + s]) % Mod
    return (1 - acc) % (1 << (T + 1))


def cert(oms, m, B):
    """(largest k_0 in [1, 2^B) whose run from orbit position m reaches a count below 1, FLAG or None)."""
    T = B + EXTRA
    r0 = rho(oms, m, T)
    Q, p3, theta, maxbad = 0, 1, None, 0
    for r in range(T + 1):
        th = -((Q - p3) // p3)                 # k_r >= 1  iff  3^r (k_0 - 1) + Q_r >= 0  iff  k_0 >= th
        theta = th if theta is None else max(theta, th)
        cls = (r0 % (1 << r)) + ((1 - ((r0 >> r) & 1)) << r)   # the k_0 with run length exactly r
        if theta > cls:
            st = 1 << (r + 1)
            maxbad = max(maxbad, cls + ((theta - 1 - cls) // st) * st)
        Q, p3 = 3 * Q + (1 << (r + 1)) * oms[m + r], p3 * 3
    cand = r0 % (1 << T)
    return maxbad, (cand if 1 <= cand < (1 << B) else None)


def brute(oms, m, K, T):
    bad = []
    for k0 in range(1, K):
        u, t = k0, 0
        while u % 2 == 1 and t <= T:
            u, t = (3 * u - 1) // 2 + oms[m + t], t + 1
            if u < 1:
                bad.append(k0)
                break
    return bad


def wlen(lv):
    return 1 + sum(3 * k + (6 if c else 7) for k, c in lv)


def structure(lim):
    seen, queue = {()}, deque([()])
    while queue:
        lv = queue.popleft()
        for s in (0, 1):
            r = step(list(lv), s)
            if r is None:
                print("a count goes below zero at", lv, s)
                continue
            nl = tuple(r[0])
            if wlen(nl) <= lim and nl not in seen:
                seen.add(nl)
                queue.append(nl)
    pos, cache, bad_shape, made, pairs, unsafe = {}, {}, 0, {}, 0, []

    def where(V):
        """(a, m) with Phi^m(P_a K(0)) = V (the pile may already be used up, so every a < 60 is tried)."""
        for a in range(60):
            if a not in cache:
                W, d = base(a), {}
                for mm in range(200):
                    d.setdefault(tuple(W), mm)
                    r = step(W, 1)
                    if r is None:
                        break
                    W = r[0]
                cache[a] = d
            if V in cache[a]:
                return a, cache[a][V]
        return None

    certs = {}
    for lv in seen:
        a = 0
        while a < len(lv) and lv[a] == (0, True):
            a += 1
        rest = lv[a:]
        if (0, True) in rest or (0, False) in rest[1:]:
            bad_shape += 1
        for i in range(a, len(lv) - 1):
            if lv[i][1] or lv[i + 1][1]:
                continue
            w = where(lv[:i + 1])
            pairs += 1
            if w is None:
                unsafe.append(("not on an orbit", lv))
                continue
            pos[w] = pos.get(w, 0) + 1
            if w[1] == 0:
                made[w[0]] = min(made.get(w[0], 10 ** 99), lv[i + 1][0])
            if w not in certs:
                o = orbit(w[0], w[1] + 600 + EXTRA + 5)
                certs[w] = cert(o[0], w[1], 600)
            if lv[i + 1][0] <= certs[w][0] or certs[w][1] is not None:
                unsafe.append((w, lv[i:i + 2], certs[w]))
    print(f"{len(seen)} walls of at most {lim} cells")
    print(f"a K'(0) above the pile, or a K(0) not directly on it: {bad_shape} walls")
    print(f"{pairs} pairs of open counters; orbit positions (a, m): {sorted(pos.items())}")
    print("least top count of a pair just made over P_a, against 2^(a+2):",
          [(a, made[a], 2 ** (a + 2)) for a in sorted(made)])
    print(f"pairs whose top count is not above the largest bad start value of their (a, m) (B = 600): {len(unsafe)}",
          unsafe[:5])


def _creation(args):
    a, B = args
    o = orbit(a, B + EXTRA + 5)
    if o is None:
        return a, None, None
    mb, f = cert(o[0], 0, B)
    return a, mb, f


def creation(A, B, P=1):
    from multiprocessing import Pool
    worst, flags, broken, above = (0, 0), [], [], []
    with Pool(P) as pool:
        for a, mb, f in pool.imap(_creation, [(a, B) for a in range(A + 1)], chunksize=4):
            if mb is None:
                broken.append(a)
                continue
            if f is not None:
                flags.append((a, f))
            if mb >= 2 ** (a + 2):
                above.append((a, mb))
            worst = max(worst, (mb, a))
            if a % 500 == 0:
                print(f"a = {a}: largest bad k_0 {mb}", flush=True)
    print(f"pile heights 0..{A}, start values below 2^{B}: largest bad k_0 {worst[0]} (a = {worst[1]}); "
          f"bad k_0 at or above 2^(a+2): {above}; FLAG {flags}; lower orbit breaks {broken}")


def table(A, M, B):
    worst = (0,)
    for a in range(A + 1):
        o = orbit(a, M + B + EXTRA + 5)
        row = []
        for m in range(M + 1):
            mb, f = cert(o[0], m, B)
            j = o[1][m]
            if f is not None:
                print("FLAG", a, m, f)
            if j and mb / j > worst[0]:
                worst = (mb / j, a, m, mb, j)
            row.append(f"{mb / j:.2f}" if j else f"[{mb}]")
        print(a, " ".join(row))
    print("largest (bad k_0)/j_m:", worst)


def digits(a, B):
    o = orbit(a, B + 10)
    r = rho(o[0], 0, B)
    bits = bin(r)[2:].zfill(B + 1)[::-1][:B]
    print(bits)
    print("longest run of zeros:", max(len(z) for z in bits.split("1")))


if __name__ == "__main__":
    cmd, args = sys.argv[1], [int(x) for x in sys.argv[2:]]
    {"structure": structure, "creation": creation, "table": table, "rho": digits}[cmd](*args)
