"""Calls per token in one round: for round k (from `0 u_k A>0` to `0 u_(k+1) A>0`), the number of times the head
enters each token of u_k from the right.  Direct simulation.

usage: python3 calls.py MACHINE MAXSTEPS      e.g. calls.py 1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC--- 8e6"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rounds import decode

def table(m):
    T = {}
    for i, g in enumerate(m.split("_")):
        for b in (0, 1):
            e = g[3*b:3*b+3]
            T[(i, b)] = None if e == "---" else (int(e[0]), 1 if e[1] == "R" else -1, "ABCDEF".index(e[2]))
    return T

def main(m, limit):
    T = table(m); N = 1 << 12
    tp = bytearray(2 * N); pos = N; st = 0; lo = hi = pos; last = pos
    cross = {}            # boundary x (between x-1 and x): leftward crossings in this round
    start = None
    for t in range(1, limit + 1):
        w, d, s = T[(st, tp[pos])]
        tp[pos] = w
        if d < 0: cross[pos] = cross.get(pos, 0) + 1
        pos += d; st = s
        lo = min(lo, pos)
        if pos > last and st == 0 and tp[pos] == 0:
            last = pos
            if tp[pos-1] == 0:
                cells = list(tp[lo:pos-1])[::-1]
                while cells and cells[-1] == 0: cells.pop()
                u = decode(cells)
                if start is not None:
                    u0, p0 = start
                    # boundaries of the tokens of u0: token i starts (its right edge) at x_i
                    x = p0 - 1; out = []
                    for ch in u0:
                        out.append(f"{ch}{cross.get(x, 0)}")
                        x -= 4 if ch == "V" else 2
                    out.append(f"|{cross.get(x, 0)}")
                    print(t, " ".join(out)); print("   ->", u, flush=True)
                start = (u, pos); cross = {}

main(sys.argv[1], int(float(sys.argv[2])))
