"""Rewrite ../lean/RoundRules.lean: one round of the right-end bouncer, for every chamber of blocks.

At rest (when the head comes back to the right end) the tape right of the irregular part is a sequence of S-blocks
S_n = 1 (01)^(n+1).  A run of 1s of length 4 or more in front of them is a *wall*.  A long visit is

  left sweep:   every S_n block between the right end and the wall becomes D_n = 1 (11)^n 00   (sweep_left)
  wall turn:    three 1s of the wall are used up and the first block turns back into S        (wall_turn)
  right sweep:  every D_n block turns back into S_n                                           (sweep_right)

and the right end grows.  There are two right ends.  In regime I the last block S_n is followed by the gadget
101100 (110)^c: the long visit makes it S_(n+3) 101101 (110)^c, and a short visit then makes that
S_(n+3) 101100 (110)^(c+1).  In regime II the right end is S_n (011)^c 0 and every visit is long: S_n becomes
S_(n+1) and two copies of 011 ... (net: (011)^(c+2), the eat visit of VisitRules.lean).  So for every list of blocks
`ms` between the wall and the last block,

  round_I:   L 1^(a+3) S_ms S_n 101100 (110)^(c+2) D>  reaches  L 1^a S_ms S_(n+3) 101101 (110)^(c+2) D>
  short_I:                         101101 (110)^(c+1) D>  reaches              101100 (110)^(c+2) D>
  round_II:  L 1^(a+3) S_ms S_n (011)^c 0 D>          reaches  L 1^a S_ms S_(n+1) S_0^c 10110 D>  (= S_n (011)^(c+2) 0)

and round_I3, round_II3 are the same rounds at a wall 0 111 (01)^(m+1) of exactly three 1s, which becomes 00 1 (01)^m.

The single-block rules are proved by `tools/py/bbtools/symtm.py`; the lists of blocks are handled by induction below.

usage: python3 holdouts/MACHINE/py/round_rules.py   (from the repository root; then lean/check.sh)
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import symtm  # noqa: E402
from bbtools.machine import Machine  # noqa: E402

M = "1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1RE"

RULES = [
    ("sweep_left", "L 1 (01)^n+1 C> 1 R", "L C> 1 1 (11)^n 0 0 R",
     "The left sweep turns S_n = 1 (01)^(n+1) into D_n = 1 (11)^n 00."),
    ("sweep_right", "L 1 B> 1 0 0 1 (11)^n 0 0 R", "L 1 (01)^n+1 1 B> 1 0 0 R",
     "The right sweep turns D_n back into S_n."),
    ("wall_turn", "L (1)^k+3 C> 1 1 (11)^n 0 0 R", "L (1)^k 1 (01)^n+1 1 B> 1 0 0 R",
     "At a wall of 1s the left sweep turns: three 1s are used up and the first block is S_n again."),
    ("wall3_turn", "L 0 1 1 C> 1 1 (11)^n 0 0 R", "L 0 0 1 (01)^n 1 B> 1 0 0 R",
     "At a wall of exactly three 1s (the last of them the first cell of the block) the sweep turns too: the wall "
     "becomes 00 and the first block loses one 01."),
    ("endI_left", "L 1 (01)^n+1 1 0 1 1 0 0 (110)^c+2 D> 0^inf",
     "L C> 1 1 1 (11)^n+1 1 1 1 0 0 1 0 1 0 1 (001)^c 0 0 1 0^inf",
     "Regime I, start of a long visit: the gadget is crossed and the last block S_n becomes D_(n+3)."),
    ("endI_right", "L 1 B> 1 0 0 1 0 1 0 1 (001)^c 0 0 1 0^inf", "L 1 0 1 1 0 1 1 (101)^c 1 0 1 1 0 D> 0^inf",
     "Regime I, end of a long visit."),
    ("shortI", "L 1 1 0 1 1 0 1 (110)^c+1 D> 0^inf", "L 1 1 0 1 1 0 0 1 (101)^c 1 0 1 1 0 D> 0^inf",
     "Regime I, the short visit: it turns inside the gadget."),
    ("endII_left", "L 1 (01)^n+1 (011)^c 0 D> 0^inf", "L C> 1 1 (11)^n+1 0 0 (100)^c 1 0^inf",
     "Regime II, start of a visit: the last block S_n becomes D_(n+1) and each 011 becomes D_0 = 100."),
    ("endII_right", "L 1 B> 1 0 0 1 0^inf", "L 1 0 1 1 0 D> 0^inf",
     "Regime II, end of a visit."),
]

TAIL_FILE = os.path.join(HERE, "round_tail.lean")


def main():
    m = Machine.parse(M)
    symtm.MAX_CARRY = 8
    ths = []
    for name, a, b, doc in RULES:
        th, fin = symtm.prove(m, name, a, b, rotate=True, count_first=True, max_seg=40, doc=doc + " (symtm)")
        ths.append(th)
        print(name, fin.steps)
    lean = os.path.join(HERE, "..", "lean")
    ns = re.search(r"namespace (\w+)", open(os.path.join(lean, "Machine.lean")).read()).group(1)
    doc = (f"# {M}: one round of the right-end bouncer\n\n" + __doc__.split("\n\nusage")[0].split("\n", 1)[1].strip()
           + "\n\nWritten by the folder's `py/round_rules.py` (with `py/round_tail.lean`); do not edit by hand.")
    text = symtm.rules_file("Machine", ns, ths + [open(TAIL_FILE).read()], doc)
    with open(os.path.join(lean, "RoundRules.lean"), "w") as f:
        f.write(text)


if __name__ == "__main__":
    main()
