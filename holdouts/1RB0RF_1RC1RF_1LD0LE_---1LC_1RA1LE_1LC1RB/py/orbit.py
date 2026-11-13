"""The pass map f of 1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB on block lengths, and its orbit from 4.

P(n) = 0^inf 1^n B> 0^inf.  Write n + 2 = 2^j m, m odd.  The pass from P(n) ends at P(f(n)):
  m = 1:                 halts
  m = 3, j even, j >= 2: f(n) = 9 * 2^(j-1) + 3j/2 + 3
  otherwise:             f(n) = 2^j m + (m + 2j - 1)/2        (odd n: j = 0, f(n) = (3n+5)/2)

usage: python3 orbit.py K            iterate f K times from 4 (the run from blank reaches P(4) at step 9)
       ./passmap 1 3000 | python3 orbit.py --check     compare f with the simulated passes
"""
import sys
from collections import Counter


def f(n):
    N = n + 2
    j = (N & -N).bit_length() - 1
    m = N >> j
    if m == 1:
        return None
    if m == 3 and j % 2 == 0 and j >= 2:
        return 9 * 2 ** (j - 1) + 3 * j // 2 + 3
    return 2 ** j * m + (m + 2 * j - 1) // 2


def main(argv):
    if argv and argv[0] == "--check":
        bad = total = 0
        for line in sys.stdin:
            n, r, _ = line.split()
            want = f(int(n))
            got = None if r == "H" else int(r)
            total += 1
            if want != got:
                bad += 1
                print("mismatch", n, r, want)
        print(f"{total} passes compared, {bad} mismatches")
        return
    K = int(argv[0]) if argv else 1000
    n, js = 4, Counter()
    first = [n]
    for i in range(K):
        N = n + 2
        js[(N & -N).bit_length() - 1] += 1
        n2 = f(n)
        if n2 is None:
            print(f"halts: pass {i} from n = {n}")
            return
        n = n2
        if len(first) < 30:
            first.append(n)
    print("orbit:", " ".join(map(str, first)), "...")
    print(f"{K} passes without a halt; n has {n.bit_length()} bits; j counts {sorted(js.items())[:12]}")


if __name__ == "__main__":
    main(sys.argv[1:])
