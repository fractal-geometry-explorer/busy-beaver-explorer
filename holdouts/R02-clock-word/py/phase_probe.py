"""Run one phase from an arbitrary word: the tape `X>0 1^L0 0 W` (blank to the left), exact and accelerated
(clock.Hybrid), until the next visit of the left end that starts a new phase (block not grown by g), a halt, or a
step limit.  Used to see which words can make a phase end halt.

usage: python3 phase_probe.py MACHINE random N SEED [L0]      random words of odd blocks
       python3 phase_probe.py MACHINE word '1^3 0 1 0 1^2' [L0]
"""
import random
import re
import sys
import clockx  # noqa: F401
from clockx import clock


def parse(s):
    out = []
    for x in s.split():
        v, _, n = x.partition("^")
        out += [int(v)] * int(n or 1)
    return bytes(out)


CH = [1, 1, 1, 3, 3, 5, 7, 2, 4]


def phase(m, W, L0=1, limit=10 ** 60, maxvisits=10 ** 5):
    h = clock.Hybrid(m)
    c = h.c
    p = h.pos
    cells = [0] * (h.v) + [1] * L0 + [0] + list(W)
    for i, x in enumerate(cells):
        h.tp[p + 1 + i] = x
    h.hi = p + len(cells)
    h.st = c.X
    h.lo = p
    first = True
    lastL = None
    nv = 0
    for v in h.visits(limit):
        if v[0] == "HALT":
            return ("HALT", v[1])
        t, L, W2 = v
        if first:
            first = False
            lastL = L
            continue
        nv += 1
        if L != lastL + c.g or nv > maxvisits:
            return ("phase", t, L, W2)
        lastL = L
    return ("limit", h.t)


if __name__ == "__main__":
    m, mode = sys.argv[1], sys.argv[2]
    if mode == "word":
        print(phase(m, parse(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 1))
    else:
        N, seed = int(sys.argv[3]), int(sys.argv[4])
        L0 = int(sys.argv[5]) if len(sys.argv) > 5 else 1
        rnd = random.Random(seed)
        halts = 0
        for i in range(N):
            nb = rnd.randint(1, 12)
            W = []
            for j in range(nb):
                W += [1] * rnd.choice(CH) + [0]
            W = bytes(W[:-1])
            r = phase(m, W, L0, limit=10 ** 30)
            if r[0] != "phase":
                print(clock.rle(W), r[:2], flush=True)
                halts += r[0] == "HALT"
        print("halts", halts, "of", N)
