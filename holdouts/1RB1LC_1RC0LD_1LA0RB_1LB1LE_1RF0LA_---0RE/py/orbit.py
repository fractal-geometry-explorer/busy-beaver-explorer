"""Iterate the round map of 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE (the map `next` of lean/Orbit.lean).

A round starts with the head in state D at the left end of the tape 10 1^N.  The doubling phases take (K, m) =
(1, N) to (2K+4, m-2K-6) while m >= 2K+6; with K = 5*2^j - 4 after j doublings, m_j = N + 10 - 10*2^j + 2j.  The
machine halts if the last m_j is 0; otherwise the next round starts at N' = 2K + 3m + 2 = 3N + 24 + 6j - 20*2^j.

usage: python3 py/orbit.py ROUNDS      iterate from N = 22 (the first round from blank tape), report the closest
                                        approach of m_j to 0 (relative to its range 10*2^j)
"""
import sys
import time


def jof(N):
    """The number of doublings: the least j >= 1 with m_j < 10*2^j - 2, i.e. 20*2^j > N + 12 + 2j."""
    j = max(1, (N + 12).bit_length() - 6)
    while j > 1 and 20 * (1 << (j - 1)) > N + 12 + 2 * (j - 1):
        j -= 1
    while not (20 * (1 << j) > N + 12 + 2 * j):
        j += 1
    return j


def step(N):
    """(m, N'): the remainder after the doublings, and the next round's N (None for a halt)."""
    j = jof(N)
    m = N + 10 - 10 * (1 << j) + 2 * j
    return m, (None if m == 0 else 3 * N + 24 + 6 * j - 20 * (1 << j)), j


def main():
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    N, t0, best = 22, time.time(), 2.0
    for i in range(T):
        m, N2, j = step(N)
        if N2 is None:
            print("HALT in round", i, "N =", N)
            return
        rel = m / (10 * (1 << j))
        if rel < best:
            best = rel
            print(f"round {i}: j = {j}, m / (10*2^j) = {rel:.3g}")
        N = N2
    print(f"{T} rounds without a halt; N has {N.bit_length()} bits ({time.time() - t0:.0f} s)")


if __name__ == "__main__":
    main()
