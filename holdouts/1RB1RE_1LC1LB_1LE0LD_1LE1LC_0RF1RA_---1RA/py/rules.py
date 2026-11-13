"""Writes lean/Rules.lean: the two proved moves of 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA at the left end.

Read the tape as runs of 1s separated by single 0s, left to right; `u` is a run of length 1 (a "unit", cells 10).
Every visit of the left end in state B sees  B> 0 1^X 0 ...  and the head only works near the left end:

* `sweep`:   [X, 4, u^(n+2), R]  ->  [X+6, 4, u^n, R]          (X = 2x+2, in 4x+36 steps)
* `convert`: [2x+8, u^(k+2), R]  ->  [6, 4, u^x, 4, u^k, R]    (in 4x+74 steps)

usage: python3 rules.py > ../lean/Rules.lean
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = "1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA"
NS = "H175628"
RULES = [
    ("sweep", "One sweep: the long run at the left grows by 6 and the unit block loses two units.",
     "0^inf B> 0 (11)^x+1 0 1111 0 (10)^n+2 R", "0^inf B> 0 1 1 1 (11)^x 1 1 1 1 1 0 1 1 1 1 0 (10)^n R"),
    ("convert", "The end of an epoch: a run of 2x+8 ones becomes x units (after a new 6 and 4), "
     "and two units of the next block become a 4.",
     "0^inf B> 0 (11)^x+4 0 (10)^k+2 R", "0^inf B> 0 1 1 1 1 1 1 0 1 1 1 (10)^x 1 0 1 1 1 (10)^k 1 0 R"),
]


def main():
    thms = []
    for name, doc, a, b in RULES:
        t, _ = prove(M, name, a, b, doc=doc, max_seg=60)
        thms.append(t)
    print(rules_file("Machine", NS, thms, __doc__.split("\n\n")[0] + " Written by `py/rules.py` with "
                     "`bbtools.symtm.prove`; checked by the kernel."), end="")


if __name__ == "__main__":
    main()
