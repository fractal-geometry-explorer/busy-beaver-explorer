"""Writes lean/Rules.lean: the cell-level rules of 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE, each proved from a
symbolic trace by bbtools.symtm.prove (Lean checks them).  usage: python3 gen_rules.py > ../lean/Rules.lean"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = "1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE"
RULES = [
    ("walk", "F walks left over a unit `1 0`, which reappears on its right", "L (01)^j F> 0 0 R", "L F> 0 (01)^j 0 R"),
    ("round", "one round at a block of at least three: two 1s off each side, two new units",
     "L 1^3 F> 0 0 (10)^k 1^2 1^Y R", "L 1 0 1 0 (10)^k 1 F> 0 0 1^Y R"),
    ("roundz", "the same round with nothing left of the head",
     "0^inf F> 0 0 (10)^k 1^2 1^Y R", "0^inf 1 0 (10)^k 1 F> 0 0 1^Y R"),
    ("merge", "a gap of two 0s: the units and the next block merge into one block, four 1s off the left block",
     "L 1^5 F> 0 0 (10)^k 0 1^Z 0 R", "L 1 F> 0 0 1 1 1 1 1 (11)^k 1^Z 0 R"),
    ("restart", "nothing left of the head and a gap: everything merges into a new left block",
     "0^inf F> 0 0 (10)^k 0 1^Z 0 1 1^W 0 R", "0^inf 1 1 1 1 1 (11)^k 1 1^Z F> 0 0 1^W 0 R"),
    ("restart3", "the same with three 1s left of the head",
     "0^inf 1^3 F> 0 0 (10)^k 0 1^Z 0 1 1^W 0 R", "0^inf 1 1 1 1 1 1 1 (11)^k 1 1^Z F> 0 0 1^W 0 R"),
    ("tail0", "the restart at the right end of the tape (last block empty): C comes back",
     "0^inf F> 0 0 (10)^k 0 0^inf", "0^inf 1 1 1 1 1 (11)^k C> 1 1 1 1 0^inf"),
    ("tail1", "the restart at the right end of the tape (last block Z + 1)",
     "0^inf F> 0 0 (10)^k 0 1^Z 1 0^inf", "0^inf 1 1 1 1 1 (11)^k 1 1^Z C> 1 1 1 1 0^inf"),
    ("tail30", "the same with three 1s left of the head, last block empty",
     "0^inf 1^3 F> 0 0 (10)^k 0 0^inf", "0^inf 1 1 1 1 1 1 1 (11)^k C> 1 1 1 1 0^inf"),
    ("tail31", "the same with three 1s left of the head, last block Z + 1",
     "0^inf 1^3 F> 0 0 (10)^k 0 1^Z 1 0^inf", "0^inf 1 1 1 1 1 1 1 (11)^k 1 1^Z C> 1 1 1 1 0^inf"),
    ("cback", "C at the right end turns into the new start: a block of n + 4 and a block of 3",
     "0^inf 1^n 1^5 C> 1 1 1 1 0^inf", "0^inf 1^n 1^3 1 F> 0 0 1 1 1 0^inf"),
    ("two1", "two 1s left of the head and a unit right of the gap: the unit is cleared, the left block becomes 5",
     "0^inf 1^2 F> 0 0 1 0 R", "0^inf 1 1 1 1 1 F> 0 0 0 R"),
    ("two2", "two 1s left of the head and a block of Y + 2: it loses one 1, the left block becomes 5",
     "0^inf 1^2 F> 0 0 1 1 1^Y 0 R", "0^inf 1 1 1 1 1 F> 0 0 1 1^Y 0 R"),
    ("haltcfg", "four 1s left of the head, units and then blank tape: D comes to read a 0",
     "0^inf 1^4 F> 0 0 (10)^k 0^inf", "0^inf D> 0 0 1 1 1 1 1 (11)^k 1 0^inf"),
]
if __name__ == "__main__":
    thms = []
    for name, doc, a, b in RULES:
        txt, fin = prove(M, name, a, b, doc=doc, rotate=True)
        thms.append(txt)
    print(rules_file("Machine", "H15252", thms,
                     "# 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE: the cell rules\n\nWritten by `py/gen_rules.py` "
                     "(`bbtools.symtm.prove`); every theorem is a chain of `rfl` steps and shift rules."), end="")
