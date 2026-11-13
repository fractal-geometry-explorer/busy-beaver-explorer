"""Writes lean/Rules.lean: the leftward sweep of 1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC, proved by bbtools.symtm.

At each visit of the right end in state B the tape ends with a block (01011111)^k and 110.  The head then walks left
converting the whole block, word by word, into (11101000)^k (re-bracketed, the 10001110 words of the samples):

    L (01011111)^(n+3) 1 1 B> 0   ->   L D> (11101000)^(n+3) 1 1 0 1        in 38n + 118 steps, for every n and L

usage: python3 rules.py > ../lean/Rules.lean
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = "1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC"
NS = "H151599"
RULES = [
    ("sweep_left", "The leftward sweep: the block of words 01011111 becomes a block of words 11101000.",
     "L (01011111)^n+3 1 1 B> 0 0^inf",
     "L D> (11101000)^n 1 1 1 0 1 0 0 0 1 1 1 0 1 0 0 0 1 1 1 0 1 0 0 0 1 1 0 1 0^inf"),
]


def main():
    thms = [prove(M, name, a, b, doc=doc, rotate=True, max_seg=60)[0] for name, doc, a, b in RULES]
    print(rules_file("Machine", NS, thms, "The leftward sweep of 1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC. Written by `py/rules.py` with "
                     "`bbtools.symtm.prove`; checked by the kernel."), end="")


if __name__ == "__main__":
    main()
