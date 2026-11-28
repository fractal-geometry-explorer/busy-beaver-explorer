"""Rewrite ../lean/LeftoverRules.lean: a visit that meets a leftover 100 and passes it (the merge case).

The visits that `py/round_check.py` cannot predict all meet a leftover D_0 = 100, left behind when a wall of a length
divisible by 3 runs out (round_I3 / round_II3).  In the most common case the 100 sits as  S_x S_0 100 1 S_y S_z :
the left sweep passes it, wears the next wall on the left down by three as usual, and on the way back the blocks
around the 100 merge:

  S_x S_0 100 1 S_y S_z   becomes   S_(x+y+3) S_0 S_0 S_(z-1)        (S_(-1) = 1, so z = 0 is included)

and every other block is unchanged.  `py/leftover_check.py` checks this against the run (every such visit with a wall
on its left, 90 of 90 in two windows).  Here symtm proves it for all counts in regime II with one block between the
wall and the 100 and two blocks between the merge and the last block (merge_II), and the same with z = 0
(merge_II_z0).  In the other cases the sweep turns at the 100 instead, and on its way back (in state A rather than in
the right sweep) it leaves every second block it passes as a run of 1s: these are the new walls.

usage: python3 holdouts/MACHINE/py/leftover_rules.py   (from the repository root; then lean/check.sh)
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import symtm  # noqa: E402
from bbtools.machine import Machine  # noqa: E402

M = "1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE"
CTX = "L (1)^a+4 1 (01)^p+1 {loc} 1 (01)^q+1 1 (01)^n+1 (011)^c 0 D> 0^inf"
RULES = [
    ("merge_II", "1 (01)^x+1 1 0 1 1 0 0 1 1 (01)^y+1 1 (01)^z+1",
     "Regime II, a leftover 100 between S_x S_0 and 1 S_y S_(z+1): the wall loses three 1s and the blocks merge into "
     "S_(x+y+3) S_0 S_0 S_z."),
    ("merge_II_z0", "1 (01)^x+1 1 0 1 1 0 0 1 1 (01)^y+1 1 0 1",
     "The same with S_0 after S_y: the merge gives S_(x+y+3) S_0 S_0 1."),
]


def main():
    m = Machine.parse(M)
    symtm.MAX_CARRY = 8
    ths = []
    for name, loc, doc in RULES:
        start = CTX.format(loc=loc)
        cfg = symtm.Config.parse(start)
        fin = symtm.run(m, cfg.copy(), lambda c: isinstance(c.right[0], symtm.Blank) and c.state == 3
                        and c.steps.surely_ge(3), max_moves=20000, rotate=True)
        end = " ".join(map(str, fin.left)) + " D> 0^inf"
        th, fin2 = symtm.prove(m, name, start, end, rotate=True, count_first=True, max_seg=40, doc=doc + " (symtm)")
        ths.append(th)
        print(name, "->", end, "steps", fin2.steps)
    lean = os.path.join(HERE, "..", "lean")
    ns = re.search(r"namespace (\w+)", open(os.path.join(lean, "Machine.lean")).read()).group(1)
    doc = (f"# {M}: visits that pass a leftover 100\n\n" + __doc__.split("\n\nusage")[0].split("\n", 1)[1].strip()
           + "\n\nWritten by the folder's `py/leftover_rules.py`; do not edit by hand.")
    with open(os.path.join(lean, "LeftoverRules.lean"), "w") as f:
        f.write(symtm.rules_file("Machine", ns, ths, doc))


if __name__ == "__main__":
    main()
