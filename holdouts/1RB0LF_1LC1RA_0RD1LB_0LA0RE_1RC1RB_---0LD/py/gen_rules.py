"""Writes lean/Rules.lean: cell rules of 1RB0LF_1LC1RA_0RD1LB_0LA0RE_1RC1RB_---0LD, each proved from a symbolic trace
by bbtools.symtm.prove (Lean checks them).  usage: python3 gen_rules.py > ../lean/Rules.lean"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = "1RB0LF_1LC1RA_0RD1LB_0LA0RE_1RC1RB_---0LD"
RULES = [
    ("bounce", "one bounce at the right end: the marker `1 0 0 0` moves one unit left, the right end gains two units",
     "L 1 0 0 1 0 0 1 0 0 0 1 0 0 1 0 0 E> 0 0 (100)^m 1 0^inf",
     "L 1 0 0 1 0 0 0 1 0 0 1 0 0 E> 0 0 1 0 0 1 (001)^m 0 0 1 0^inf"),
]
if __name__ == "__main__":
    thms = []
    for name, doc, a, b in RULES:
        txt, fin = prove(M, name, a, b, doc=doc, rotate=True)
        thms.append(txt)
    print(rules_file("Machine", "H69875", thms,
                     "# 1RB0LF_1LC1RA_0RD1LB_0LA0RE_1RC1RB_---0LD: the cell rules\n\nWritten by `py/gen_rules.py` "
                     "(`bbtools.symtm.prove`); every theorem is a chain of `rfl` steps and shift rules."), end="")
