"""Can the left part of 1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE be protected without knowing the engine?

`GoodPair` (lean/Insert_1RB1RF1LC0RF1.lean) needs the head to reach the extra block near the left end only on
regular passes.  This script asks whether that follows from the left part alone, whatever the rest of the tape does.

A boundary is put OFF cells right of the end of the block region (OFF = 0: at the end of the blocks; OFF = 30:
inside the 7-periodic emitter at the start of the engine).  The contents left of the boundary at the moments the
real run crosses it leftwards are collected (passes PASS0..PASS0+40).  Then an adversary may send the head across the
boundary in any state a left move can enter (A, B, C, F) as often as it likes; each visit runs until the head leaves
across the boundary again.  The deep periodic part is cut to KEEP periods after every visit.  The search reports
how many contents it reached, how many visits reached the left end of the tape (only regular passes may), and how
many halted.  A finite closed set without bad visits would prove GoodPair for every right part.

usage: python3 py/shield.py [OFF] [STEPS] [CAP]       e.g.  python3 py/shield.py 30 3e7 3000
"""
import sys
from collections import deque

M = "1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE"
T = []
for g in M.split("_"):
    T.append([None if g[3 * y:3 * y + 3] == "---" else
              (int(g[3 * y]), 1 if g[3 * y + 1] == "R" else -1, "ABCDEF".index(g[3 * y + 2])) for y in (0, 1)])
BLK = [1, 0, 1, 1, 0, 1, 1, 0, 1, 1]
KEEP = 8


def real_contents(off, steps):
    """Left contents (string, state) at the leftward crossings of the boundary in the last 40 passes."""
    N = 1 << 22
    tape = bytearray(N)
    h = lo = hi = N // 2
    s = 0
    x = -1
    passes = []
    cur = []
    for _ in range(int(steps)):
        r = tape[h]
        w, d, ns = T[s][r]
        tape[h] = w
        old = h
        h += d
        s = ns
        if h > hi:
            hi = h
        if x >= 0 and old == x and h == x - 1:
            cur.append(("".join(map(str, tape[lo:x])), s))
        if h < lo:
            lo = h
            passes.append(cur)
            cur = []
            i = lo + 13
            while i + 10 < hi and list(tape[i:i + 10]) == BLK:
                i += 10
            x = i + off
    return [c for p in passes[-40:] for c in p]


def norm(s):
    s = s.lstrip("0")
    start = min(13, len(s))
    e = start
    while e + 10 < len(s) and s[e] == s[e + 10]:
        e += 1
    per = (e + 10 - start) // 10
    return s[:start] + s[start + 10 * max(0, per - KEEP):]


def visit(L, s, maxt=2000000):
    pad = 60
    tape = [0] * pad + [int(c) for c in L]
    n = len(tape)
    h = n - 1
    mind = h
    t = 0
    while h < n:
        if h < 0:
            return ("off",)
        tr = T[s][tape[h]]
        if tr is None:
            return ("halt",)
        tape[h], d, s = tr
        h += d
        t += 1
        mind = min(mind, h)
        if t > maxt:
            return ("loop",)
    return ("exit", "".join(map(str, tape)), mind < pad + 13)


def main():
    off = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    steps = float(sys.argv[2]) if len(sys.argv) > 2 else 3e7
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 3000
    real = {(norm(c), s) for c, s in real_contents(off, steps)}
    init = {c for c, _ in real}
    print(f"boundary {off} cells right of the blocks: {len(real)} distinct real crossings, {len(init)} contents")
    seen, Q = set(init), deque(init)
    deep, halts = set(), 0
    while Q and len(seen) < cap:
        L = Q.popleft()
        for s in (0, 1, 2, 5):
            r = visit(L, s)
            if r[0] != "exit":
                halts += r[0] == "halt"
                continue
            if r[2]:
                deep.add((L, s))
            L2 = norm(r[1])
            if L2 not in seen:
                seen.add(L2)
                Q.append(L2)
    print(f"adversary: {len(seen)} contents{' (cap reached, still growing)' if Q else ' (closed)'}; "
          f"{len(deep)} visits reach the left end, {sum(d in real for d in deep)} of them real; {halts} visits halt")


if __name__ == "__main__":
    main()
