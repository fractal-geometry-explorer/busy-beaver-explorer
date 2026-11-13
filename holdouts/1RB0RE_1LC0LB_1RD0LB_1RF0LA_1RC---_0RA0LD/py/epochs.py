"""Read the tape at right-end visits (from c/snap.c) and print its three parts: the engine P on the left, the stack of
units U = 10101010101010101011 (20 cells, counted in pairs: N = pairs), and the block of V = 1101110101 on the right.

usage (from the repository root):
  gcc -O2 -o /tmp/snap holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/c/snap.c
  /tmp/snap 1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD 40000000000 300 R | \
      python3 holdouts/1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD/py/epochs.py

Each output line: visit, step, width, length of P, N (units of 40 cells), m (copies of V), length of what follows V.
"""
import sys

U = "1010101010101010101110101010101010101011"
V = "1101110101"

for line in sys.stdin:
    p = line.split()
    if p[0] == "HALT":
        print(line.strip())
        continue
    n, k, w, st, x = p
    i = x.find(U * 2)
    N, j = 0, 0
    if i >= 0:
        j = i
        while x[j:j + 40] == U:
            j += 40
            N += 1
    vi = x.find(V * 3, j)
    m, e = 0, len(x)
    if vi >= 0:
        e = vi
        while x[e:e + 10] == V:
            e += 10
            m += 1
    print(n, k, w, "P", i, "N", N, "m", m, "tail", len(x) - e)
