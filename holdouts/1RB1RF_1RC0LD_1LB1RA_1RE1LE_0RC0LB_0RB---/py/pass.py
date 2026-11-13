"""Print the symbolic pieces of lean/Pass.lean (each proved along a symbolic run by tools/py/bbtools/symtm.py).

usage: python3 py/pass.py        (from holdouts/1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---)

- `z_two`: two bounces of the zig-zag: the marker 0 with 3(m+2) ones between it and the head (in B, on the last 1
  of the tape) moves 8 cells right, the gap drops to 3m and the tape grows by 2 cells;
- `z_c`: the first bounce after a launch with gap 3(m+1)+1 (head in C on the 0 just right of the 1s);
- `l_0`, `l_2`: launches from the left end with no marker, width 3(m+3) and 3(m+3)+2.

lean/Pass.lean contains these theorems verbatim; the induction over the bounces is by hand.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove  # noqa: E402

M = "1RB1RF_1RC0LD_1LB1RA_1RE1LE_0RC0LB_0RB---"

PIECES = [
    ('z_two', 'L 0 (111)^m+2 B> 1 0^inf', 'L 1 1 1 1 1 1 1 1 0 (111)^m B> 1 0^inf'),
    ('z_c', 'L 0 (111)^m+1 1 C> 0 0^inf', 'L 1 1 1 1 0 (111)^m B> 1 0^inf'),
    ('l_0', '0^inf (111)^m+3 C> 0 0^inf', '0^inf 1 0 1 1 0 (111)^m+2 B> 1 0^inf'),
    ('l_2', '0^inf (111)^m+3 1 1 C> 0 0^inf', '0^inf 1 0 1 1 1 1 1 1 0 (111)^m+2 B> 1 0^inf'),
]


def main():
    for name, a, b in PIECES:
        text, _ = prove(M, name, a, b, count_first=True, rotate=True)
        print(text)


if __name__ == "__main__":
    main()
