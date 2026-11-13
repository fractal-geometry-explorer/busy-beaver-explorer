"""Study of the orbit of 4 under the pass map f of 1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB.

`g` is the map as defined (and proved) in lean/Macro.lean: f(n) = g(n-1, 2).  This script
  1. checks that g agrees with the closed form of orbit.py for n < 200000;
  2. iterates f from 4 for K passes (exact integers) and reports the growth rate, the distribution of
     j = v2(n+2) against the geometric law 2^-(j+1), and the largest j seen;
  3. lists which j a pass must have for its image to halt (the image n' has n'+2 a power of two).

usage: python3 study.py [K]     (K = 200000 by default; about a minute)
"""
import math
import sys
from collections import Counter

sys.path.insert(0, __import__("os").path.dirname(__file__))
from orbit import f as f_closed  # noqa: E402


def g(b, c):
    while True:
        if b == 0:
            return c + 2 if c % 2 == 0 else (3 * c + 9) // 2
        if b % 2 == 0:
            return c + 3 * (b // 2) + 2
        if b == 1:
            return None
        i = (b - 3) // 2
        b, c = i, c + i + 4


def f(n):
    return g(n - 1, 2)


def v2(x):
    return (x & -x).bit_length() - 1


def main(argv):
    K = int(argv[0]) if argv else 200000
    bad = sum(f(n) != f_closed(n) for n in range(1, 200000))
    print(f"g against the closed form, 1 <= n < 200000: {bad} mismatches")

    n, js, logs = 4, Counter(), 0.0
    for i in range(K):
        j = v2(n + 2)
        js[j] += 1
        n2 = f(n)
        if n2 is None:
            print(f"HALT at pass {i}, n = {n}")
            return
        n = n2
    bits = n.bit_length()
    rate = (bits - 3) * math.log(2) / K
    print(f"{K} passes, no halt; n has {bits} bits; mean growth per pass e^{rate:.4f} = {math.exp(rate):.4f}")
    exp = sum(2.0 ** -(j + 1) * math.log(1 + 2.0 ** -(j + 1)) for j in range(60))
    print(f"  predicted for random low bits (P(j) = 2^-(j+1), factor about 1 + 2^-(j+1)): e^{exp:.4f}")
    print("  j counts (observed / expected):",
          ", ".join(f"{j}: {js[j]}/{K * 2.0 ** -(j + 1):.0f}" for j in range(12)), f"; max j = {max(js)}")

    # Which passes can lead to a halt: f(n) + 2 = 2^k.  With n + 2 = 2^j m (m odd, m >= 3):
    #   m >= 5 or (m = 3, j odd): f(n) + 2 = 2^j m + j + (m+3)/2, so 2^(k+1) = m (2^(j+1) + 1) + 2j + 3;
    #   j = 0: 3m + 3 = 2^(k+1) - ... is impossible mod 3; j = 1: 5m + 5 = 2^(k+1) is impossible mod 5.
    print("preimages of halting values n' = 2^k - 2 (k <= 40), by j:")
    pre = Counter()
    for k in range(3, 41):
        for j in range(0, 40):
            q = 2 ** (j + 1) + 1
            r = 2 ** (k + 1) - 2 * j - 3
            if r > 0 and r % q == 0 and (r // q) % 2 == 1 and r // q >= 3:
                m = r // q
                n = 2 ** j * m - 2
                if n >= 1 and f(n) == 2 ** k - 2:
                    pre[j] += 1
    print("  ", dict(sorted(pre.items())), "(none with j = 0 or 1)")


if __name__ == "__main__":
    main(sys.argv[1:])
