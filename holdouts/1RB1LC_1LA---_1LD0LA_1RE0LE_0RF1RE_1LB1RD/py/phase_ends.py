"""How far left each phase end of 1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD reads, and what it leaves.

usage: python3 phase_ends.py N     the first N phases (even Q only, as in phases.py)

For each phase of the run (found with the exact simulator tsim.py, rounds skipped by the Lean rule), the tape left of
the block after the rounds is copied and the phase end is simulated cell by cell from
    L 1^5 0 (10)^Q 1^5 E> 0^inf
to the next phase start  L' 10 1^P' 0 (10)^Q' 1^5 E> 0^inf  (Q' even).  Printed: phase, P, P', depth (how many cells
of L the head visited), the last 50 cells of the part of L it visited, and the last 50 cells of L' before the block.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tsim import TRun, parse  # noqa: E402

M = "1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD"
T = parse(M)
PAT = re.compile(r'^(.*)10(1{7,})0((?:10)+)11111$')


def phase_end(left, Q):
    tape = left + '11111' + '0' + '10' * Q + '11111'
    pad = 4 * len(tape) + 1000
    t = bytearray(pad) + bytearray(int(c) for c in tape) + bytearray(4 * len(tape) + 1000)
    off = pad
    p = off + len(tape); q = 4; hi = p - 1; minp = p
    while True:
        tr = T[q][t[p]]
        if tr is None:
            return ('HALT', off + len(left) - minp)
        t[p], mv, q = tr
        p += mv
        minp = min(minp, p)
        if p > hi:
            hi = p
            if q == 4:
                m = PAT.match(''.join(map(str, t[off:hi])))
                if m and (len(m.group(3)) // 2) % 2 == 0:
                    return (len(m.group(2)), off + len(left) - minp, m.group(1))


def main():
    N = int(sys.argv[1])
    r = TRun(M); hi = 0; phases = 0
    while phases < N:
        r.step()
        p = r.pos if r.d == 1 else r.pos - 1
        if p <= hi:
            continue
        hi = p; L = r.L
        if (len(L) >= 5 and L[-1] == [(1,), 5] and L[-2][0] == (1, 0) and L[-3] == [(0,), 1] and L[-4][0] == (1,)
                and L[-4][1] >= 7 and L[-5][0] == (1, 0)):
            P, Q = L[-4][1], L[-2][1]
            if Q % 2:
                continue
            phases += 1
            left = ''.join(''.join(map(str, w)) * c for w, c in L[:-4])
            res = phase_end(left, Q + P - 5)
            if res[0] == 'HALT':
                print(phases, P, 'HALT', res[1], 'of', len(left))
            else:
                print(phases, P, '->', res[0], 'depth', res[1], 'of', len(left), 'read', left[-res[1]:][-50:], 'leaves', res[2][-50:],
                      flush=True)
            k = (P - 5) // 2
            L[-4][1] = P - 2 * k; L[-2][1] = Q + 2 * k; hi += 2 * k; r.pos += 2 * k


if __name__ == '__main__':
    main()
