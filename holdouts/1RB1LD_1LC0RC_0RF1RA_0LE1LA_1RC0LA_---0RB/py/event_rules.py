"""Write ../lean/EventRules.lean: one round of every event of 1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB at the anchor
`D> 0` (D reading the single 0 before a block of 1s), proved for every count and every surrounding tape L, R by
bbtools.symtm (Lean checks the traces).  lean/Events.lean turns them into the event map.

usage: python3 holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/py/event_rules.py   (then lean/check.sh)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import symtm  # noqa: E402

M = "1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB"
NS = "H170561"

RULES = [
    ("r_odd", "L 0 1 (11)^j+1 D> 0 R", "L 1 (11)^j D> 0 1 1 1 R",
     "An odd block of 2j+3 ones left of the head: two of its 1s go, the 0 on its left becomes 1 and three 1s are "
     "written after the head (they join the block to the right)."),
    ("r_shift", "L 0 (11)^j+1 D> 0 R", "L D> 0 1 (11)^j 0 0 R",
     "An even block of 2j+2 ones left of the head: the head erases its last 1 and comes to rest on the 0 on its "
     "left."),
    ("r_split", "L 0 0 (11)^j+2 D> 0 R", "L 1 0 0 (11)^j D> 0 1 1 1 R",
     "An even block of 2j+4 ones with two 0s on its left: one 1 is written before the two 0s, the block loses four "
     "1s and three 1s are written after the head."),
    ("r_zero", "L 0 D> 0 1 1 1 (1)^k R", "L 1 0 0 (1)^k 0 1 A> R",
     "No block left of the head (a 0): the block of k+3 ones on the right gives one 1 to the left, moves left and "
     "the head ends right of it behind a carrier `0 1`."),
    ("r_two", "L 0 0 1 1 D> 0 1 1 (1)^k R", "L 1 0 0 0 0 (1)^k 0 1 A> R",
     "A block of exactly two 1s with two 0s on its left: it is erased, one 1 goes left, and the head crosses the "
     "block on the right."),
    ("r_one", "L 0 0 1 D> 0 1 1 (1)^k R", "L 1 0 1 1 (1)^k 0 1 A> R",
     "A single 1 with two 0s on its left."),
    ("r_oneE", "L 0 (11)^j+1 0 1 D> 0 1 1 (1)^k R", "L 1 (11)^j+1 0 1 1 (1)^k 0 1 A> R",
     "A single 1 with an even block of 2j+2 ones behind one 0 on its left."),
    ("r_oneO", "L 0 1 (11)^j 0 1 D> 0 R", "L D> 0 1 1 1 (11)^j 0 R",
     "A single 1 with an odd block of 2j+1 ones behind one 0 on its left."),
    ("a_end", "L 0 1 A> 0 0 R", "L D> 0 1 1 1 R",
     "The carrier `0 1` meets two 0s: it turns into three 1s and the head stops on the 0 before them."),
    ("a_pass", "L 0 1 A> 0 1 1 (1)^b R", "L 0 1 1 (1)^b 0 1 A> R",
     "The carrier `0 1` passes a block of b+2 ones that follows a single 0."),
]


def main():
    th = [symtm.prove(M, n, s, e, doc=d, rotate=True)[0] for n, s, e, d in RULES]
    doc = ("# 1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB: one round of every event\n\nWritten by `py/event_rules.py` "
           "with `bbtools.symtm` (a symbolic run, its trace checked by the kernel); every count, every tape L, R.")
    with open(os.path.join(HERE, "..", "lean", "EventRules.lean"), "w") as f:
        f.write(symtm.rules_file("Machine", NS, th, doc))


if __name__ == "__main__":
    main()
