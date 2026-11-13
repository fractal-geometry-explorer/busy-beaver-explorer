"""Write ../lean/FoldRules.lean: the fold at the left end and the first steps of the split endings of 1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB, proved for
every count and every tape to the right by bbtools.symtm (Lean checks the traces).  lean/Fold.lean iterates them.

usage: python3 holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/py/fold_rules.py   (then lean/check.sh)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import symtm  # noqa: E402

M = "1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB"

RULES = [
    ("fold_step", "0^inf A> 0 (11)^n+2 0 0 1^m+1 R", "0^inf A> 0 1 1 (11)^n 0 0 1 1 1 (1)^m+1 R",
     "One zig-zag of the fold: at the left end, two 1s leave the first block and three join the block after the gap "
     "of two 0s."),
    ("fold_last", "0^inf A> 0 1 1 0 0 1^m+1 R", "0^inf A> 0 0 0 1 1 1 (1)^m+1 R",
     "The last zig-zag of the fold: the first block is used up."),
    ("fold_open", "0^inf A> 0 0 0 1^m+1 R", "0^inf A> 0 1 1 0 (1)^m+1 R",
     "After the fold: two new 1s at the left end, one 0 before the merged block."),
    ("end1", "L 1 E> 0 0 1 0 0 1 1 R", "L 1 1 0 0 0 0 0 1 A> R",
     "The split ends with M = 1 (and at least two 1s after the gap): the last 1 of the block goes left, two 1s of "
     "the next block become the carrier `0 1`."),
    ("end3", "L 1 E> 0 0 1 1 1 0 0 R", "L 1 1 0 1 0 0 0 1 A> R",
     "The split ends with M = 3: one 1 goes left, a lone 1 stays, the carrier `0 1` starts on the next block."),
    ("carry", "L 0 1 A> (1)^m 0 R", "L (1)^m 0 1 A> 0 R",
     "The carrier `0 1` crosses a block of m ones to the right in 5m steps."),
    ("lsweep", "L (11)^m A> 1 R", "L A> 1 (11)^m R",
     "A runs left over ones, two cells per two steps."),
]


def main():
    th = [symtm.prove(M, n, s, e, doc=d, rotate=True)[0] for n, s, e, d in RULES]
    doc = ("# 1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB: the fold\n\nWritten by `py/fold_rules.py` with `bbtools.symtm` "
           "(a symbolic run, its trace checked by the kernel); every count, every tape R to the right.")
    with open(os.path.join(HERE, "..", "lean", "FoldRules.lean"), "w") as f:
        f.write(symtm.rules_file("Machine", "H170561", th, doc))


if __name__ == "__main__":
    main()
