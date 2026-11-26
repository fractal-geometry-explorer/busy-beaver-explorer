"""Tail-feedback scan: can the tail drag the counter down?  (trust level: computation)

For a "counter plus tail" machine with a remainder-class round map (ctxround.py: A U^m B, m = Q j + r, goes to
A' U'^m' B' with m' affine in j), measure for every class round the growth g in cells and the additive offset
off = cells' - g * cells, and relate the offset to the size of the contexts.  The argument of cryptids pull
request 37 needs the offset bounded below whatever the tail (c >= 0 there).  The output's `buckets` give the
smallest offset seen for contexts of 8-15, 16-31, ... cells: bounded for PR 37's machine (about -9), falling with
the tail for its sibling 1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA.

usage: python3 tailscan.py MACHINE SIDE STATE SYM [N]      (the event of ctxround.py; N contexts, default 300)
"""
import os, sys, json, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'holdouts', '1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---', 'py'))
import ctxround as cr
from collections import deque
from fractions import Fraction as F

def scan(machine, side, state, sym, N, maxlen=300, seconds=600):
    eng = cr.Engine(machine, side, state, sym)
    start, parsed, Q, qs = cr.start_of(eng)
    A0, U0, m0, B0 = start[1]
    qcap = max(Q * 16, max(qs) * 2)
    seen = {(A0, U0, B0): 0}; q = deque([(A0, U0, B0)])
    recs = []; halts = 0; unk = 0; n = 0; T = time.time(); dropped = 0
    while q and n < N and time.time() - T < seconds:
        c = q.popleft(); n += 1
        todo = [(Q, r) for r in range(Q)]
        while todo:
            QQ, r = todo.pop()
            o = eng.rep(c[0], c[1], c[2], QQ, r)
            if o[0] == 'HALT': halts += 1
            elif o[0] == 'ok':
                _, a, b, k0, poly, A2, U2, B2 = o
                g = F(a * len(U2), QQ * len(c[1]))
                cells = len(c[1]) * (QQ * k0 + r)
                off = len(U2) * b - g * cells
                ctx = len(c[0]) + len(c[2]); ctx2 = len(A2) + len(B2)
                recs.append((float(g), float(off), ctx, ctx2, seen[c]))
                c2 = (A2, U2, B2)
                if c2 not in seen:
                    if ctx2 <= maxlen: seen[c2] = seen[c] + 1; q.append(c2)
                    else: dropped += 1
            elif o[0] == 'INCONS' and QQ * 2 <= qcap:
                todo.extend((QQ * 2, r + i * QQ) for i in range(2))
            else: unk += 1
    gs = [x[0] for x in recs]; offs = [x[1] for x in recs]
    # offset per context cell: worst (most negative) off/(ctx+1); and worst off among small vs large contexts
    worst = min(recs, key=lambda x: x[1]) if recs else None
    ratio = min((x[1] / (x[2] + x[3] + 1) for x in recs), default=0)
    big = [x for x in recs if x[2] + x[3] >= 60]; small = [x for x in recs if x[2] + x[3] < 30]
    return dict(machine=machine, expanded=n, seen=len(seen), dropped=dropped, halts=halts, unknown=unk, classes=len(recs),
                gmin=min(gs, default=None), gmax=max(gs, default=None),
                offmin_small=min((x[1] for x in small), default=None), offmin_big=min((x[1] for x in big), default=None),
                worst=worst, worst_ratio=ratio, buckets={b: min((x[1] for x in recs if b <= x[2]+x[3] < 2*b), default=None) for b in (8,16,32,64,128,256,512)}, secs=round(time.time() - T))

if __name__ == '__main__':
    m, s, st, sy = sys.argv[1:5]; N = int(sys.argv[5]) if len(sys.argv) > 5 else 300
    print(json.dumps(scan(m, s, st, sy, N)), flush=True)
