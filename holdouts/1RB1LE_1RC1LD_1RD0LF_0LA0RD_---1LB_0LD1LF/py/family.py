"""The 3-cell-block family (G12 3a): keep lean/Family.lean identical in the three folders, and check the table
facts it rests on against the reference simulator.

usage: python3 holdouts/1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF/py/family.py check   compare the copies, run checks
       python3 holdouts/1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF/py/family.py copy    copy this folder's file to the others
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
HOLD = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(HOLD, "..", "tools", "py"))
from bbtools.machine import Machine  # noqa: E402

T = "1RB1LE_1RC1LD_1RD0LF_0LA0RD_---1LB_0LD1LF"
M1 = "1RB1LB_1RC1LE_1RD0LF_0LA0RD_---1LD_0LD1LF"
M3 = "1RB1LC_1RC0LF_0LD0RC_1RA1LE_---1LA_0LC1LF"
S = "1RB1LE_1RC---_1RD0LF_0LA0RD_---1LG_0LD1LF_---1LD"


def path(m):
    return os.path.join(HOLD, m, "lean", "Family.lean")


def check():
    ref = open(path(T)).read()
    for m in (M1, M3):
        assert open(path(m)).read() == ref, f"{m}/lean/Family.lean differs from {T}'s"
    # M3 is T renamed (A->D, B->A, C->B, D->C): its run from blank is T's run from blank in state B
    ren = {0: 3, 1: 0, 2: 1, 3: 2, 4: 4, 5: 5}
    mt, m3 = Machine.parse(T), Machine.parse(M3)
    for q in range(6):
        for y in (0, 1):
            a, b = mt.table[q][y], m3.table[ren[q]][y]
            assert (a is None) == (b is None) and (a is None or (a[0], a[1], ren[a[2]]) == b)
    # S, M1 and T agree step by step for 10^6 steps; T from B and M3 agree for 10^6 steps
    ms, m1 = Machine.parse(S), Machine.parse(M1)
    phi1, phi2 = [0, 1, 2, 3, 1, 5, 4], [0, 1, 2, 3, 4, 5, 1]
    cfg = [dict(), 0, 0]
    c1, c2 = [dict(), 0, 0], [dict(), 0, 0]
    for k in range(10 ** 6):
        t, h, s = cfg
        tr = ms.table[s][t.get(h, 0)]
        assert tr is not None, f"S stops at step {k + 1}"
        for (mm, c, phi) in ((m1, c1, phi1), (mt, c2, phi2)):
            assert c[1] == h and c[2] == phi[s]
            w, d, ns = mm.table[c[2]][c[0].get(c[1], 0)]
            c[0][c[1]] = w
            c[1] += d
            c[2] = ns
        w, d, ns = tr
        t[h] = w
        cfg[1] = h + d
        cfg[2] = ns
    assert c1[0] == c2[0] == cfg[0]
    print("family checks passed")


if __name__ == "__main__":
    if sys.argv[1:] == ["copy"]:
        ref = open(path(T)).read()
        for m in (M1, M3):
            open(path(m), "w").write(ref)
    else:
        check()
