"""1RB1RA_1LC0LF_1RA1LD_1LB1LE_0LC0RD_---0RA: how deep does an increment reach?

At every third visit the word of the run is  b a^k b^4 X, and three visits later  b a^(k+1) b^4 X'  with X' of the
same length (trec.py: T^3 = a . increment).  This script follows N increments from visit V with the recursion of
trec.py and prints, for each residue of k mod 8, how far from the front of b^4 X the last changed token lies.
Seen: the increments at k = 1, 2, 3, 5, 6 mod 8 change at most the first 28 tokens; those at k = 4 mod 8 hand one T
on to the rest of the word and reach a depth with a heavy tail.

usage: python3 depth.py WRUN [V [N]]      (WRUN: the compiled c/wrun.c; default V = 50842, N = 1600; one minute)
"""
import sys, threading, collections
from trec import T
from entropy import word


def main():
    wrun = sys.argv[1]
    v = int(sys.argv[2]) if len(sys.argv) > 2 else 50842
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 1600
    w = word(wrun, v)
    assert w[0] == 'b'
    s = w[1:]
    k = 0
    while s.startswith('cbb', 3 * k):
        k += 1
    r = s[3 * k:]
    assert r.startswith('bbbb'), "visit V must be one with the word b a^k b^4 X"
    by = collections.defaultdict(list)
    for _ in range(n):
        r2 = r
        for _ in range(3):
            r2 = T(r2)
        assert r2.startswith('cbbbbbb') and len(r2) == len(r) + 3
        r2 = r2[3:]
        d = len(r)
        while d > 0 and r[d - 1] == r2[d - 1]:
            d -= 1
        by[k % 8].append(d)
        r = r2
        k += 1
    print(f"{n} increments from visit {v}; the word behind the block has {len(r)} tokens")
    for m in range(8):
        ds = sorted(by[m])
        print(f"k = {m} mod 8: {len(ds)} increments, depth of the change: median {ds[len(ds) // 2]}, largest {ds[-1]}")
    ds = sorted(by[4])
    print("k = 4 mod 8, quantiles 10% 25% 50% 75% 90% 95% 99%:",
          ' '.join(str(ds[int(len(ds) * q)]) for q in (0.1, 0.25, 0.5, 0.75, 0.9, 0.95, 0.99)))


if __name__ == "__main__":
    sys.setrecursionlimit(10 ** 7)
    threading.stack_size(1 << 29)
    t = threading.Thread(target=main)
    t.start()
    t.join()
