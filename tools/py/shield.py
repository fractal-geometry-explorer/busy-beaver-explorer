"""Is the part of a tape beyond a boundary safe whatever the rest of the tape does?

usage: python3 tools/py/shield.py MACHINE L|R OFF STEPS CAP

The boundary is OFF cells from the left (L) or right (R) end of the tape, measured from the current end.  From the
second half of a run of STEPS steps from blank tape, the contents between that end and the boundary are collected at
every moment the head crosses the boundary towards the end.  Then an adversary may send the head across the
boundary in any state that a move towards the end can enter, as often as it likes; each visit runs until the head
crosses back.  The search prints how many contents it reaches (stopping at CAP) and how many visits halt.  A closed
set without halts would show that the end part is safe for every rest of the tape (the kind of fact `GoodPair` of
tools/lean/TM/Insert.lean needs); a growing set with halts shows that safety must come from the rest of the tape.
holdouts/1RB0LF_1LC0LA_---1RD_1RF1RE_1LF1RD_1LB0RE/py/shield.py is the same search with the periodic block region
of that machine cut to a fixed length.
"""
import sys
from collections import deque


def table(m, mirror):
    t = []
    for g in m.split("_"):
        t.append([None if g[3 * y:3 * y + 3] == "---" else
                  (int(g[3 * y]), (1 if g[3 * y + 1] == "R" else -1) * (-1 if mirror else 1),
                   "ABCDEF".index(g[3 * y + 2])) for y in (0, 1)])
    return t


def main():
    m, side, off, steps, cap = sys.argv[1], sys.argv[2], int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
    T = table(m, side == "R")
    into = sorted({tr[2] for row in T for tr in row if tr and tr[1] < 0})
    N = 1 << 23
    tape = bytearray(N)
    h = lo = N // 2
    s = t = 0
    real = set()
    while t < steps:
        tr = T[s][tape[h]]
        if tr is None:
            print("the machine halts at step", t)
            return
        tape[h] = tr[0]
        old = h
        h += tr[1]
        s = tr[2]
        t += 1
        lo = min(lo, h)
        x = lo + off
        if old == x and h == x - 1 and t > steps / 2:
            real.add("".join(map(str, tape[lo:x])).lstrip("0"))

    def visit(L, s, maxt=10 ** 6):
        pad = 100
        tp = [0] * pad + [int(c) for c in L]
        n = len(tp)
        h = n - 1
        for _ in range(maxt):
            if h >= n:
                return "".join(map(str, tp)).lstrip("0")
            if h < 0:
                return "off"
            tr = T[s][tp[h]]
            if tr is None:
                return "halt"
            tp[h], d, s = tr
            h += d
        return "loop"

    print(f"{len(real)} real contents; the head enters the end part in states {''.join('ABCDEF'[q] for q in into)}")
    seen, Q, halts = set(real), deque(real), 0
    while Q and len(seen) < cap:
        L = Q.popleft()
        for q in into:
            r = visit(L, q)
            if r in ("halt", "off", "loop"):
                halts += r == "halt"
                continue
            if r not in seen:
                seen.add(r)
                Q.append(r)
    print(f"adversary: {len(seen)} contents ({'still growing' if Q else 'closed'}), {halts} visits halt")


if __name__ == "__main__":
    main()
