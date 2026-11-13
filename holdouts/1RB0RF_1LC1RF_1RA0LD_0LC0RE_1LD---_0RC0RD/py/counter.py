"""Print the symbolic pieces of lean/Counter.lean (each proved along a symbolic run by tools/py/bbtools/symtm.py).

usage: python3 py/counter.py        (from holdouts/1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD)

Write the tape right of the head as gap words `0^g 1`.  At a sample point the head is in C on `0 0 1` (the word of
gap 2) with `1 1 1` and blank to its left.  The pieces:

- `c_*`: C sweeps right, carrying `0 0 1`, over a gap-3 word (`blk`, any number), a gap-5 word, the pair of gaps
  (0, 1) (`merge`) or the gaps (0, 0, 3, 3) (`zz`);
- `s_*`: the stops: C reaches the first other gap and turns back, in the normal return state `1 1 1 D> 0` or the
  special return state `1 1 1 C> 1 0 1`;
- `n_*`, `p_*`: the normal and special return states going left over what the sweep left behind, and at the left end;
- `h_*`: the two stops that reach the halting transition (E reads 1).

lean/Counter.lean contains these theorems verbatim; the definitions and the inductions are written by hand.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove  # noqa: E402

M = "1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD"

PIECES = [
    ('c_blk', 'L C> 0 0 1 (0001)^m R', 'L (1110)^m C> 0 0 1 R'),
    ('c_five', 'L C> 0 0 1 0 0 0 0 0 1 R', 'L 1 1 1 1 1 1 C> 0 0 1 R'),
    ('c_merge', 'L C> 0 0 1 1 0 1 R', 'L 1 1 1 C> 0 0 1 R'),
    ('c_zz', 'L C> 0 0 1 1 1 0 0 0 1 0 0 0 1 R', 'L 1 1 1 1 1 1 0 1 0 0 C> 0 0 1 R'),
    ('c_23', 'L C> 0 0 1 0 0 1 0 0 0 1 R', 'L 1 1 1 0 1 0 0 C> 0 0 1 R'),
    ('s_1', 'L C> 0 0 1 0 1 R', 'L 1 1 1 D> 0 0 R'),
    ('s_21', 'L C> 0 0 1 0 0 1 0 1 R', 'L 1 1 1 D> 0 0 0 1 1 R'),
    ('s_2e', 'L C> 0 0 1 0 0 1 0^inf', 'L 1 1 1 D> 0 0 0 0 0 1 0 1 1 0^inf'),
    ('s_0x', 'L C> 0 0 1 1 0 0 R', 'L 1 1 1 D> 0 1 1 R'),
    ('s_0e', 'L C> 0 0 1 1 0^inf', 'L 1 1 1 D> 0 1 1 0^inf'),
    ('s_41x', 'L C> 0 0 1 0 0 0 0 1 0 1 0 0 R', 'L 1 1 1 D> 0 1 0 1 0 1 0 1 1 R'),
    ('s_7x', 'L C> 0 0 1 0 0 0 0 0 0 0 R', 'L 1 1 1 C> 1 0 1 0 1 1 0 R'),
    ('s_4e', 'L C> 0 0 1 0 0 0 0 1 0^inf', 'L 1 1 1 C> 1 0 1 0 1 0 1 0 1 0 1 1 0^inf'),
    ('s_6e', 'L C> 0 0 1 0 0 0 0 0 0 1 0^inf', 'L 1 1 1 C> 1 0 1 0 1 1 1 0^inf'),
    ('s_20e', 'L C> 0 0 1 0 0 1 1 0^inf', 'L 1 1 1 C> 1 0 1 0 0 0 1 1 0^inf'),
    ('n_blk', 'L (1110)^m 1 1 1 D> 0 R', 'L 1 1 1 D> 0 (0010)^m R'),
    ('n_five', 'L 1 1 1 1 1 1 1 1 1 D> 0 R', 'L 1 1 1 D> 0 1 0 1 0 1 0 R'),
    ('n_merge', 'L 1 1 1 1 1 1 D> 0 R', 'L 1 1 1 C> 1 0 1 0 R'),
    ('n_zz', 'L 1 1 1 1 1 1 0 1 0 0 1 1 1 D> 0 R', 'L 1 1 1 C> 1 0 1 0 0 0 1 1 0 1 0 R'),
    ('n_23', 'L 1 1 1 0 1 0 0 1 1 1 D> 0 R', 'L 1 1 1 D> 0 0 0 1 1 0 1 0 R'),
    ('n_end', '0^inf 1 1 1 1 1 1 D> 0 R', '0^inf 1 1 1 C> 0 0 1 0 0 0 1 0 R'),
    ('p_blk', 'L 1 1 1 0 1 1 1 C> 1 0 1 R', 'L 1 1 1 C> 1 0 1 0 0 0 1 R'),
    ('p_five', 'L 1 1 1 1 1 1 1 1 1 C> 1 0 1 R', 'L 1 1 1 C> 1 0 1 0 1 0 1 0 1 R'),
    ('p_merge', 'L 1 1 1 1 1 1 C> 1 0 1 R', 'L 1 1 1 D> 0 1 0 1 0 1 R'),
    ('p_zz', 'L 1 1 1 1 1 1 0 1 0 0 1 1 1 C> 1 0 1 R', 'L 1 1 1 C> 1 0 1 0 0 0 0 0 1 0 0 0 1 R'),
    ('p_23', 'L 1 1 1 0 1 0 0 1 1 1 C> 1 0 1 R', 'L 1 1 1 D> 0 0 0 0 0 1 0 0 0 1 R'),
    ('p_end', '0^inf 1 1 1 1 1 1 C> 1 0 1 R', '0^inf 1 1 1 C> 0 0 1 0 1 0 1 0 1 R'),
    # the two stops that halt: E reads 1
    ('h_000', 'L C> 0 0 1 1 1 1 R', 'L 1 1 1 0 0 E> 1 R'),
    ('h_40', 'L C> 0 0 1 0 0 0 0 1 1 R', 'L 1 1 1 1 1 1 0 0 E> 1 R'),
]


def main():
    for name, a, b in PIECES:
        text, _ = prove(M, name, a, b, count_first=True, rotate=True)
        print(text)


if __name__ == "__main__":
    main()
