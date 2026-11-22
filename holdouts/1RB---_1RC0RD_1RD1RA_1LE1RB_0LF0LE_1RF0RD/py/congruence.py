"""Congruence search for 1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD (lead 27 of the 22 Nov 2026 list).

The machine halts iff the orbit of `phase` meets (m, m + 2, 2^(m+1) + 1) (`halts_iff_family`, Lean).  In event
terms (X = Y - 2, j = d + 1) the event chain inside a phase adds 2^j, 2^(j+1), ..., which keeps X - 2^j + 1 fixed,
so the family is met iff some overflow *leaves* an event with X = 2^j - 1 (the string is j ones), M >= j + 1.

A congruence invariant would be a set of residues of (X mod q, j mod p, M mod p') that contains every overflow
output of the orbit and misses every family point.  Every family point (2^j - 1, j, M) with M > j has the same
residues as an orbit output (X, j, M) with X = 2^j - 1 (mod q).  So such an invariant exists for modulus q only if
no orbit output satisfies X = 2^j - 1 (mod q), and this script counts those outputs: one hit rules out every
residue invariant mod q (with any moduli for j and M).

usage: python3 congruence.py OVERFLOWS QMAX AMAX
  counts, over the first OVERFLOWS overflows of the orbit (the first 5, before the string is shorter than 2^j,
  skipped), the outputs with X = 2^j - 1 (mod q) for every 2 <= q <= QMAX, and those whose low a bits are all ones
  (X = 2^j - 1 mod 2^a) for a <= AMAX; also checks X < 2^j at every output.
"""
import math
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import macro  # noqa: E402


def outputs(n):
    for _, _, _, _, new in macro.phases(0, 2, 1, n):
        if new is None:
            raise SystemExit("the map is stuck: a halt")
        X, M, N = new
        yield X, (N + 2) // 3, M


def main(n, qmax, amax):
    t0 = time.time()
    L = 1
    for q in range(2, qmax + 1):
        L = L * q // math.gcd(L, q)
    hits = [0] * (qmax + 1)
    ones = [0] * (amax + 1)
    count = short = 0
    maxrun = (0, 0)
    for i, (X, j, M) in enumerate(outputs(n)):
        if i < 5:
            continue
        count += 1
        short += X < 2 ** j
        D = (X - (1 << j) + 1) % L
        for q in range(2, qmax + 1):
            if D % q == 0:
                hits[q] += 1
        run = ((X + 1) & -(X + 1)).bit_length() - 1       # trailing ones of X
        for a in range(1, min(run, amax) + 1):
            ones[a] += 1
        if run > maxrun[0]:
            maxrun = (run, j)
    zero = [q for q in range(2, qmax + 1) if hits[q] == 0]
    worst = min(range(2, qmax + 1), key=lambda q: hits[q] * q)
    print(f"{count} overflow outputs (from overflow 6 to {n}), {time.time() - t0:.1f} s")
    print(f"X < 2^j at {short} of them")
    print(f"moduli q <= {qmax} with no output X = 2^j - 1 (mod q): {zero if zero else 'none'}")
    print(f"fewest hits relative to 1/q: q = {worst}, {hits[worst]} hits ({hits[worst] * worst / count:.2f} x expected)")
    print("outputs whose low a bits are all ones:", ", ".join(f"a={a}: {ones[a]}" for a in range(1, amax + 1)))
    print(f"longest run of trailing ones: {maxrun[0]} (j = {maxrun[1]})")


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
