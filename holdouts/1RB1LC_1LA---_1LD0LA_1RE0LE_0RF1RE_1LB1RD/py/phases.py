"""Phases of 1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD: the exact accelerated simulator tsim.py, with the rounds of a
phase skipped by formula.

usage: python3 phases.py N [EVERY] [-v]  run N phases, print every EVERY-th: phase, P, bits of P, stack entries, the
                                       tape just left of the block; -v also reports the phases with odd Q

A phase starts when the head, in state E, reaches a new cell at the right end of the tape
    L 1 0 1^P 0 (10)^Q 1^5 E> 0^inf      with P >= 7 and Q even >= 2
(with Q odd, which happens only in the first phases, nothing is skipped).
Then k = (P-5)//2 rounds take (P, Q) to (P - 2k, Q + 2k) (Lean: `rounds` in ../lean/Rounds.lean); they are skipped
here (their steps are not counted), the rest of the phase is simulated cell by cell (with tsim's exact crossings).
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tsim import TRun  # noqa: E402

M = "1RB1LC_1LA---_1LD0LA_1RE0LE_0RF1RE_1LB1RD"


def show(st):
    return ' '.join(''.join(map(str, w)) + ('^%d' % c if c > 1 else '') for w, c in st)


def main():
    N = int(sys.argv[1])
    every = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = TRun(M)
    hi = 0
    phases = 0
    while phases < N:
        if not r.step():
            print("HALT after", phases, "phases")
            return
        p = r.pos if r.d == 1 else r.pos - 1
        if p <= hi:
            continue
        hi = p
        L = r.L
        if (len(L) >= 5 and L[-1] == [(1,), 5] and L[-2][0] == (1, 0) and L[-3] == [(0,), 1] and L[-4][0] == (1,)
                and L[-4][1] >= 7 and L[-5][0] == (1, 0)):
            P, Q = L[-4][1], L[-2][1]
            assert r.q == 4 and r.d == 1 and not r.R, r.q
            if Q % 2:
                if "-v" in sys.argv:
                    print("odd Q", P, Q)
                continue    # odd Q: the round rule is not proved for it, simulate cell by cell
            k = (P - 5) // 2
            phases += 1
            if phases % every == 0 or phases <= 3:
                print(phases, P, P.bit_length(), len(L) + len(r.R), show(L[-12:-5]), flush=True)
            L[-4][1] = P - 2 * k
            L[-2][1] = Q + 2 * k
            hi += 2 * k
            r.pos += 2 * k


if __name__ == "__main__":
    main()
