"""Congruence search for the map  n -> 3n - 10*2^k + 3k + 14  (h_k < n < h_{k+1}, halt at n = h_k = 5*2^k - k - 6)
iterated by 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE (start n = 4), 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE
(n = 10) and 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE (n = 1).

Is there a set of residue classes that contains the orbit, is kept by the map and misses every h_k?  With
v = n + k + 6 - 5*2^k (n = h_k iff v = 0) the step is, exactly,

    v' = 3v + 2 + 5*2^k + k' - 5*2^k',   k' = k + d,

and d = 0 or 1 for every residue of v once 2^k is large (d = 2 only in the top ~k/3 values of a level).  So what a
congruence mod M sees is the state (v mod M, k mod M, 2^k mod M) under the nondeterministic step `astep` with
d in {0, 1} (lean/Congruence.lean, `astep`, `realize`).  If a path of choices leads from the start to v = 0, no
congruence invariant mod M (or mod any divisor of M) exists (`no_inv_dvd`).

  python3 congruence.py check            the v-form of the step and the range of d, against the map (n < 2e5)
  python3 congruence.py all N            breadth-first search for every modulus 2 <= M <= N, all three starts
  python3 congruence.py grid J I         the same for every M = 2^j 3^i, j <= J, i <= I
  python3 congruence.py lean J I A B     meet-in-the-middle paths for M = 2^J 3^I (prefix A, suffix B choices),
                                         printed as the certificate theorems of lean/Congruence.lean
"""
import itertools
import sys
from collections import deque
from math import gcd

STARTS = [(4, "4"), (10, "10"), (1, "1")]
ROUNDS = 40          # the certificates start from the value after 40 steps of the map


def h(k):
    return 5 * 2 ** k - k - 6


def lev(n):
    k = 0
    while h(k + 1) <= n:
        k += 1
    return k


def f(n):
    k = lev(n)
    return None if n == h(k) else 3 * n - 10 * 2 ** k + 3 * k + 14


def orbit(s, t):
    for _ in range(t):
        s = f(s)
    return s


def astep(M, s, d):
    v, kk, p = s
    p2 = (2 ** d * p) % M
    return ((3 * v + 2 + 5 * p + kk + d + 5 * (M - p2)) % M, (kk + d) % M, p2)


def cls(M, k, n):
    return ((n + k + 6 - 5 * 2 ** k) % M, k % M, pow(2, k, M))


def run(M, s, ds):
    for d in ds:
        s = astep(M, s, d)
    return s


def bfs(M, s0):
    """A shortest list of choices from s0 to v = 0, or None if the reachable set avoids v = 0."""
    if s0[0] == 0:
        return []
    prev = {s0: None}
    q = deque([s0])
    while q:
        s = q.popleft()
        for d in (0, 1):
            t = astep(M, s, d)
            if t in prev:
                continue
            prev[t] = (s, d)
            if t[0] == 0:
                ds = []
                while prev[t] is not None:
                    t, dd = prev[t]
                    ds.append(dd)
                return ds[::-1]
            q.append(t)
    return None


def mitm(M, i, s0, a, b):
    """Meet in the middle for M = 2^j 3^i: a prefix of a choices, a suffix of b >= i choices.  The suffix from
    (v, k, p) ends at 3^b v + S(k, p); with b >= i the 3-part of 3^b v vanishes, so S = 0 mod 3^i and
    v = -S/3^b mod 2^j."""
    two = M // 3 ** i
    inv = pow(3, -b, two) if two > 1 else 0
    need = []
    for sig in range(a + 1):
        st = (0, (s0[1] + sig) % M, (s0[2] * pow(2, sig, M)) % M)
        tab = {}
        for ds in itertools.product((0, 1), repeat=b):
            S = run(M, st, ds)[0]
            if S % 3 ** i == 0:
                tab.setdefault((-S * inv) % two if two > 1 else 0, ds)
        need.append(tab)
    for ds in itertools.product((0, 1), repeat=a):
        s = run(M, s0, ds)
        t = need[sum(ds)].get(s[0] % two if two > 1 else 0)
        if t is not None:
            full = list(ds) + list(t)
            assert run(M, s0, full)[0] == 0
            return full
    return None


def starts():
    for s, name in STARTS:
        n0 = orbit(s, ROUNDS)
        yield s, name, n0, lev(n0)


def period(M):
    """(j, L): 2^(j+L) = 2^j mod M and M | L."""
    j, odd = 0, M
    while odd % 2 == 0:
        odd //= 2
        j += 1
    per, x = 1, 2 % odd if odd > 1 else 1
    while odd > 1 and x != 1:
        x, per = x * 2 % odd, per + 1
    return j, M * per // gcd(M, per)


def main(argv):
    cmd = argv[0] if argv else "check"
    if cmd == "check":
        for n in range(4, 200000):
            k = lev(n)
            if n == h(k):
                continue
            m = f(n)
            k2 = lev(m)
            assert k2 - k in (0, 1, 2)
            v, v2 = n + k + 6 - 5 * 2 ** k, m + k2 + 6 - 5 * 2 ** k2
            assert v2 == 3 * v + 2 + 5 * 2 ** k + k2 - 5 * 2 ** k2
        print("v-form of the step and d in {0,1,2} hold for 4 <= n < 200000")
    elif cmd in ("all", "grid"):
        if cmd == "all":
            Ms = range(2, int(argv[1]) + 1)
        else:
            J, I = int(argv[1]), int(argv[2])
            Ms = sorted(2 ** j * 3 ** i for j in range(J + 1) for i in range(I + 1) if j + i > 0)
        worst = 0
        for s, name, n0, k0 in starts():
            for M in Ms:
                j, _ = period(M)
                assert k0 >= j
                p = bfs(M, cls(M, k0, n0))
                if p is None:
                    print("INVARIANT FOUND: start", name, "modulus", M)
                    continue
                worst = max(worst, len(p))
        print(f"{len(Ms)} moduli, 3 starts: every one reaches v = 0; longest shortest path {worst}")
    elif cmd == "lean":
        J, I, a, b = map(int, argv[1:5])
        M = 2 ** J * 3 ** I
        j, L = period(M)
        for s, name, n0, k0 in starts():
            p = mitm(M, I, cls(M, k0, n0), a, b)
            if p is None:
                print(f"-- start {name}: no path found with a = {a}, b = {b}")
                continue
            print(f"/-- Start {name}: the value after {ROUNDS} steps of the map is {n0}, at level {k0}. -/")
            print(f"theorem start_{name} : fiter {ROUNDS} {s} = some {n0} := by decide +kernel\n")
            print(f"theorem level_{name} : h {k0} ≤ {n0} ∧ {n0} < h {k0 + 1} := by decide +kernel\n")
            print(f"/-- **No congruence invariant mod any divisor of 2^{J}·3^{I} = {M}** for start {name}. -/")
            print(f"theorem no_cong_{name} : ∀ M', M' ∣ {M} → ∀ K P, CongInv M' K P → ¬ P (cls M' {k0} {n0}) :=")
            print(f"  no_inv_cert {M} {j} {L} {k0} {n0}")
            print(f"    {p}".replace("[", "[").replace("]", "]"))
            print("    (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide)")
            print("    (by decide +kernel)\n")


if __name__ == "__main__":
    main(sys.argv[1:])
