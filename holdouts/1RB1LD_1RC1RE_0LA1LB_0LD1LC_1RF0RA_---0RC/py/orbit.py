"""Iterates the round map of 1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC (lean/Round.lean, `next`) from (8, 1).

  m = 3t   : (m, k) -> (4t+4, k-1)      m = 3t+1 : (m, k) -> (4t+4, k+1)
  m = 3t+2 : (m, k) -> (4t+5, k+1), and the machine halts if k = 0

usage: python3 orbit.py N    prints, every N/20 rounds, the round, k, the least k since the start of the record
part, the counts of each residue, and the number of bits of m.  `check` compares the first rounds with the
round ends of a direct simulation.
"""
import sys

def orbit(N, report=None):
    m, k = 8, 1
    cnt = [0, 0, 0]
    mink = k; mink_after = {}
    for n in range(1, N + 1):
        t, r = divmod(m, 3)
        cnt[r] += 1
        if r == 0:
            m, k = 4 * t + 4, max(k - 1, 0)
        elif r == 1:
            m, k = 4 * t + 4, k + 1
        else:
            if k == 0:
                return ("halt", n, m, k, cnt)
            m, k = 4 * t + 5, k + 1
        if report and n % report == 0:
            print(n, k, cnt, m.bit_length(), flush=True)
    return ("running", N, m, k, cnt)

def mins(N):
    """k at each round and the overall minimum of k after round 10, 100, 1000, ..."""
    m, k = 8, 1
    ks = []
    for n in range(N):
        t, r = divmod(m, 3)
        if r == 0: m, k = 4 * t + 4, max(k - 1, 0)
        elif r == 1: m, k = 4 * t + 4, k + 1
        else:
            if k == 0: return ks, n
            m, k = 4 * t + 5, k + 1
        ks.append(k)
    return ks, None

if __name__ == "__main__":
    N = int(float(sys.argv[1]))
    if len(sys.argv) > 2 and sys.argv[2] == "mins":
        ks, h = mins(N)
        print("halt at round", h) if h is not None else None
        print("first 40 k:", ks[:40])
        for e in range(1, 8):
            a = 10 ** e
            if a < len(ks): print("min k over rounds >= %d: %d (k at %d: %d)" % (a, min(ks[a - 1:]), a, ks[a - 1]))
    else:
        print(orbit(N, report=max(1, N // 20))[:2] if False else orbit(N, report=max(1, N // 20))[0:2])
