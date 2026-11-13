"""Checks of the split rule of 1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB on small configurations (plain simulation).

The configuration  ... 1^a E> 0 0 1^M 0 0 1^b 0 ...  (state E reading the first 0 of a gap of two before a block of M ones):
* M odd: one round takes 4 ones from the block, gives 1 to the left neighbour and 3 to the right one, and comes back to
  the same shape: 1^(a+1) E> 0 0 1^(M-4) 0 0 1^(b+3).  Lean proves it for odd M >= 11 (lean/Rules.lean); this script
  checks it for odd M from 5 to 59, and prints what happens for the small and the even M (a halt for M = 0, 2, 4:
  the head meets three 0s in a row in state E, E0 -> C0 -> F0).

usage: python3 holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/py/split.py
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.machine import Machine  # noqa: E402

M = "1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB"
E = 4


def first_e(a, m_, b, limit=200000):
    pad = 40
    cells = [0] * pad + [1] * a + [0, 0] + [1] * m_ + [0, 0] + [1] * b + [0] * pad
    mach = Machine.parse(M)
    tape = dict(enumerate(cells))
    head, st = pad + a, E
    for n in range(1, limit + 1):
        t = mach.table[st][tape.get(head, 0)]
        if t is None:
            return ("halt", n)
        w, d, st = t
        tape[head] = w
        head += d
        if st == E and tape.get(head, 0) == 0 and tape.get(head + 1, 0) == 0 and tape.get(head - 1, 0) == 1:
            lo = min(tape)
            s = "".join(str(tape.get(i, 0)) for i in range(lo, max(tape) + 1)).strip("0")
            return (n, head - pad, s)
    return None


def main():
    bad = 0
    for M_ in range(5, 60, 2):
        for a in (1, 2, 5):
            for b in (1, 4, 7):
                r = first_e(a, M_, b)
                want = "1" * (a + 1) + "00" + "1" * (M_ - 4) + "00" + "1" * (b + 3)
                if not (r and r[0] != "halt" and r[2] == want and r[1] == a + 1):
                    bad += 1
                    print("odd M differs:", a, M_, b, r[:2] if r else r)
    print("odd M in 5..59: rule held in all but", bad, "cases")
    for M_ in (0, 1, 2, 3, 4, 6, 8, 10):
        r = first_e(2, M_, 3)
        print(f"M={M_}: ", r if r is None or r[0] == "halt" else (r[0], r[2]))


if __name__ == "__main__":
    main()
