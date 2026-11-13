"""Print the symbolic pieces of lean/Counter.lean and lean/Counter2.lean (each proved along a symbolic run by tools/py/bbtools/symtm.py).

usage: python3 py/counter.py        (from holdouts/1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---)

lean/Counter.lean contains these theorems verbatim; the definitions (`ccfg`, `grps`, ...) and the inductions over
the groups (`pass_all`, `ret_all`, `conv_all`, `bounce_gen`, `exhaust`, ...) are written by hand around them.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove  # noqa: E402

M = "1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---"

PIECES = [
    # the bounce: right over 0 10 x^n0 1, over passed groups, turn at the digit, back, left end
    ('p_start', '0^inf C> 0 10 (1110)^n 1 R', '0^inf 1 (0101)^n 0 1 0 E> R'),
    ('p_pass', 'L E> (1110)^m+1 1 R', 'L 1 0 1 1 (0101)^m 0 E> R'),
    ('p_turn1', 'L E> 10 R', 'L D> 0 1 R'),
    ('p_turn2', 'L E> 1010 R', 'L D> 0 1 1 0 R'),
    ('p_ret', 'L 1 0 1 1 (0101)^m 0 D> 0 1 R', 'L D> 0 1 1 0 1 0 (1110)^m 1 R'),
    ('p_end', '0^inf 1 (0101)^n 0 1 0 D> 0 1 R', '0^inf C> 0 1 0 1 1 1 0 (1110)^n 1 R'),
    # empty groups at the right end
    ('p_t1', 'L E> 1 0^inf', 'L D> 0 1 0^inf'),
    ('p_t2', 'L E> 1 1 0^inf', 'L D> 0 1 1 1 0^inf'),
    ('p_t3', 'L E> 1 1 1 0^inf', 'L D> 0 1 1 0 1 0^inf'),
    # the end of a round: back from the right end, group by group
    ('p_x1', 'L 1 0 1 1 (0101)^k 0 E> 0^inf', 'L C> 1 1 0 1 1 (1101)^k 1 0^inf'),
    ('p_y', 'L 1 0 1 1 (0101)^m 0 C> 1 R', 'L C> 1 1 0 1 1 1 (1011)^m R'),
    ('p_z', '0^inf 1 (0101)^n 0 1 0 C> 1 R', '0^inf C> 0 1 0 1 1 0 1 1 (1011)^n R'),
    # lean/Counter2.lean: the turn at one / two empty groups in front of a digit >= 2, and a round with no group
    ('p_mx', 'L 1 0 1 1 (0101)^k 0 E> 1 1 0 1 0 R', 'L C> 1 1 0 1 1 1 (1011)^k 1 0 1 1 R'),
    ('p_mz', '0^inf 1 (0101)^n 0 1 0 E> 1 1 0 1 0 R', '0^inf C> 0 1 0 1 1 0 (1110)^n+1 1 1 R'),
    ('p_mx2', 'L 1 0 1 1 (0101)^k 0 E> 1 1 1 0 1 0 R', 'L C> 1 1 0 1 1 1 (1011)^k 1 0 1 1 1 R'),
    ('p_mz2', '0^inf 1 (0101)^n 0 1 0 E> 1 1 1 0 1 0 R', '0^inf C> 0 1 0 1 1 0 (1110)^n+1 1 1 1 R'),
    ('p_e0', '0^inf 1 (0101)^n 0 1 0 E> 0^inf', '0^inf C> 0 1 0 1 1 0 (1110)^n 1 1 0^inf'),
]


def main():
    for name, a, b in PIECES:
        text, _ = prove(M, name, a, b, count_first=True, rotate=True)
        print(text)


if __name__ == "__main__":
    main()
