"""Generate Rules.lean: the rounds and the ends of the step of 1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA, proved along
the symbolic run (tools/py/bbtools/symtm.py: single steps by `rfl`, shift rules by `TM.cross_r`/`TM.cross_l`).

usage: python3 rules.py > Rules.lean

Tapes are written left to right: `S>` is the head in state S on the next cell, `(11)^n` is n copies of `11`, `R` is
any tape.  W(x, b, R) is `0^inf A> 1^x 0 1 0 1 1^b R`; the step is made of rounds W(x+2, b+1, R) -> W(x, b+4, R)
and an end at x = 2 or x = 1.
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove, rules_file  # noqa: E402

M = "1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA"

RULES = [
    ("round_e", "0^inf A> 1 1 1 1 (11)^k+1 0 1 0 1 1 (1)^b R", "0^inf A> 1 1 (11)^k+1 0 1 0 1 1 1 1 1 (1)^b R",
     "W(2k+6, b+1, R) -> W(2k+4, b+4, R): a 0 walks through the left block and two of its ones become three."),
    ("round_o", "0^inf A> 1 1 1 (11)^k+1 0 1 0 1 1 (1)^b R", "0^inf A> 1 (11)^k+1 0 1 0 1 1 1 1 1 (1)^b R",
     "W(2k+5, b+1, R) -> W(2k+3, b+4, R)."),
    ("round_4", "0^inf A> 1 1 1 1 0 1 0 1 1 (1)^b R", "0^inf A> 1 1 0 1 0 1 1 1 1 1 (1)^b R",
     "W(4, b+1, R) -> W(2, b+4, R)."),
    ("round_3", "0^inf A> 1 1 1 0 1 0 1 1 (1)^b R", "0^inf A> 1 0 1 0 1 1 1 1 1 (1)^b R",
     "W(3, b+1, R) -> W(1, b+4, R)."),
    ("end_e_e", "0^inf A> 1 1 0 1 0 1 (11)^b+3 0 1 0 1 (01)^c R",
     "0^inf A> 1 1 1 1 (11)^b+3 0 1 0 1 1 1 1 1 1 1 (01)^c R",
     "W(2, 2b+6, (01)^(c+2) R) -> W(2b+10, 6, (01)^c R): the middle block becomes the left block."),
    ("end_e_o", "0^inf A> 1 1 0 1 0 1 1 (11)^b+3 0 1 0 1 (01)^c R",
     "0^inf A> 1 1 1 1 1 (11)^b+3 0 1 0 1 1 1 1 1 1 1 (01)^c R",
     "W(2, 2b+7, (01)^(c+2) R) -> W(2b+11, 6, (01)^c R)."),
    ("end_o_e", "0^inf A> 1 0 1 0 1 (11)^b+3 0 1 0 1 (01)^c R",
     "0^inf A> 1 1 (11)^b+3 0 1 0 1 1 1 1 1 1 1 (01)^c R",
     "W(1, 2b+6, (01)^(c+2) R) -> W(2b+8, 6, (01)^c R)."),
    ("end_o_o", "0^inf A> 1 0 1 0 1 1 (11)^b+3 0 1 0 1 (01)^c R",
     "0^inf A> 1 1 1 (11)^b+3 0 1 0 1 1 1 1 1 1 1 (01)^c R",
     "W(1, 2b+7, (01)^(c+2) R) -> W(2b+9, 6, (01)^c R)."),
    # The resets (Reset.lean): tails T2 = `0 1 1`, T13 = `0 1^4 0 1 1`, T16 = `0 1^7 0 1 1`; found by search over the
    # offsets of the repeat counts, ends as the symbolic run reaches them.
    ("tend2_e_T2", "0^inf A> 1 1 0 1 0 1 (11)^b 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 0 (11)^b 1 1 1 1 0 1 1 0^inf",
     "End of the last step of a phase (tail T): the middle block becomes a block `1^B` behind `1^4 0` or `1^5 0`."),
    ("tend2_o_T2", "0^inf A> 1 1 0 1 0 1 1 (11)^b 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 0 (11)^b 1 1 1 1 1 0 1 1 0^inf",
     "End of the last step of a phase (tail T): the middle block becomes a block `1^B` behind `1^4 0` or `1^5 0`."),
    ("tend1_e_T2", "0^inf A> 1 0 1 0 1 (11)^b 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 1 0 (11)^b 1 0 1 1 0^inf",
     "End of the last step of a phase (tail T): the middle block becomes a block `1^B` behind `1^4 0` or `1^5 0`."),
    ("tend1_o_T2", "0^inf A> 1 0 1 0 1 1 (11)^b 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 1 0 (11)^b 1 1 0 1 1 0^inf",
     "End of the last step of a phase (tail T): the middle block becomes a block `1^B` behind `1^4 0` or `1^5 0`."),
    ("tend2_e_T13", "0^inf A> 1 1 0 1 0 1 (11)^b 0 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 0 (11)^b 1 1 1 1 0 1 1 1 1 0 1 1 0^inf",
     "End of the last step of a phase (tail T): the middle block becomes a block `1^B` behind `1^4 0` or `1^5 0`."),
    ("tend2_o_T13", "0^inf A> 1 1 0 1 0 1 1 (11)^b 0 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 0 (11)^b 1 1 1 1 1 0 1 1 1 1 0 1 1 0^inf",
     "End of the last step of a phase (tail T): the middle block becomes a block `1^B` behind `1^4 0` or `1^5 0`."),
    ("tend1_e_T13", "0^inf A> 1 0 1 0 1 (11)^b 0 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 1 0 (11)^b 1 0 1 1 1 1 0 1 1 0^inf",
     "End of the last step of a phase (tail T): the middle block becomes a block `1^B` behind `1^4 0` or `1^5 0`."),
    ("tend1_o_T13", "0^inf A> 1 0 1 0 1 1 (11)^b 0 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 1 0 (11)^b 1 1 0 1 1 1 1 0 1 1 0^inf",
     "End of the last step of a phase (tail T): the middle block becomes a block `1^B` behind `1^4 0` or `1^5 0`."),
    ("tend2_e_T16", "0^inf A> 1 1 0 1 0 1 (11)^b 0 1 1 1 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 0 (11)^b 1 1 1 1 0 1 1 1 1 1 1 1 0 1 1 0^inf",
     "End of the last step of a phase (tail T): the middle block becomes a block `1^B` behind `1^4 0` or `1^5 0`."),
    ("tend2_o_T16", "0^inf A> 1 1 0 1 0 1 1 (11)^b 0 1 1 1 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 0 (11)^b 1 1 1 1 1 0 1 1 1 1 1 1 1 0 1 1 0^inf",
     "End of the last step of a phase (tail T): the middle block becomes a block `1^B` behind `1^4 0` or `1^5 0`."),
    ("tend1_e_T16", "0^inf A> 1 0 1 0 1 (11)^b 0 1 1 1 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 1 0 (11)^b 1 0 1 1 1 1 1 1 1 0 1 1 0^inf",
     "End of the last step of a phase (tail T): the middle block becomes a block `1^B` behind `1^4 0` or `1^5 0`."),
    ("tend1_o_T16", "0^inf A> 1 0 1 0 1 1 (11)^b 0 1 1 1 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 1 0 (11)^b 1 1 0 1 1 1 1 1 1 1 0 1 1 0^inf",
     "End of the last step of a phase (tail T): the middle block becomes a block `1^B` behind `1^4 0` or `1^5 0`."),
    ("k4_e_T2", "0^inf A> 1 1 1 1 0 (11)^b+2 0 1 1 0^inf",
     "0^inf F> 0 1 0 1 0 1 0 1 1 1 (10)^b 1 1 1 1 0 1 1 0^inf",
     "The conversion from `1^4 0 1^B T`."),
    ("k4_o_T2", "0^inf A> 1 1 1 1 0 1 (11)^b+1 0 1 1 0^inf",
     "0^inf A> 1 (10)^b 1 0 1 0 1 0 1 1 1 1 0 1 1 0^inf",
     "The conversion from `1^4 0 1^B T`."),
    ("k5_e_T2", "0^inf A> 1 1 1 1 1 0 (11)^b+4 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 1 1 0 1 0 1 1 1 1 1 1 (10)^b 1 1 1 1 0 1 1 0^inf",
     "The conversion from `1^5 0 1^B T`."),
    ("k5_o_T2", "0^inf A> 1 1 1 1 1 0 1 (11)^b+1 0 1 1 0^inf",
     "0^inf A> 1 1 (10)^b 1 0 1 0 1 0 1 1 1 1 0 1 1 0^inf",
     "The conversion from `1^5 0 1^B T`."),
    ("k4_e_T13", "0^inf A> 1 1 1 1 0 (11)^b+1 0 1 1 1 1 0 1 1 0^inf",
     "0^inf F> 0 1 0 1 0 1 0 1 1 1 (10)^b 1 1 1 1 1 1 1 0 1 1 0^inf",
     "The conversion from `1^4 0 1^B T`."),
    ("k4_o_T13", "0^inf A> 1 1 1 1 0 1 (11)^b+1 0 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 (10)^b 1 0 1 0 1 0 1 0 1 1 1 1 1 1 1 0 1 1 0^inf",
     "The conversion from `1^4 0 1^B T`."),
    ("k5_e_T13", "0^inf A> 1 1 1 1 1 0 (11)^b+3 0 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 1 1 0 1 0 1 1 1 1 1 1 (10)^b 1 1 1 1 1 1 1 0 1 1 0^inf",
     "The conversion from `1^5 0 1^B T`."),
    ("k5_o_T13", "0^inf A> 1 1 1 1 1 0 1 (11)^b+1 0 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 (10)^b 1 0 1 0 1 0 1 0 1 1 1 1 1 1 1 0 1 1 0^inf",
     "The conversion from `1^5 0 1^B T`."),
    ("k4_e_T16", "0^inf A> 1 1 1 1 0 (11)^b+3 0 1 1 1 1 1 1 1 0 1 1 0^inf",
     "0^inf A> (11)^b 1 1 1 1 1 1 0 1 0 1 1 1 1 0 1 0 1 0 1 1 1 1 0 1 1 0^inf",
     "The conversion from `1^4 0 1^B T`."),
    ("k4_o_T16", "0^inf A> 1 1 1 1 0 1 (11)^b+3 0 1 1 1 1 1 1 1 0 1 1 0^inf",
     "0^inf A> (11)^b 1 1 1 1 1 1 1 0 1 0 1 1 1 1 0 1 0 1 0 1 1 1 1 0 1 1 0^inf",
     "The conversion from `1^4 0 1^B T`."),
    ("k5_e_T16", "0^inf A> 1 1 1 1 1 0 (11)^b+3 0 1 1 1 1 1 1 1 0 1 1 0^inf",
     "0^inf A> (11)^b 1 1 1 1 1 1 1 0 1 0 1 1 1 1 0 1 0 1 0 1 1 1 1 0 1 1 0^inf",
     "The conversion from `1^5 0 1^B T`."),
    ("k5_o_T16", "0^inf A> 1 1 1 1 1 0 1 (11)^b+3 0 1 1 1 1 1 1 1 0 1 1 0^inf",
     "0^inf A> (11)^b 1 1 1 1 1 1 1 1 0 1 0 1 1 1 1 0 1 0 1 0 1 1 1 1 0 1 1 0^inf",
     "The conversion from `1^5 0 1^B T`."),
    ("a2_T3", "0^inf A> 1 1 (01)^k+2 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 0 1 1 1 (10)^k 1 1 1 1 0 1 1 0^inf",
     "Restart from `1^2 (01)^k T`."),
    ("a3_T3", "0^inf A> 1 1 1 (01)^k+2 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 0 1 0 1 1 1 (10)^k 1 1 1 1 0 1 1 0^inf",
     "Restart from `1^3 (01)^k T`."),
    ("a2_T6", "0^inf A> 1 1 (01)^k+2 1 1 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 0 1 1 1 (10)^k 1 1 1 1 1 1 1 0 1 1 0^inf",
     "Restart from `1^2 (01)^k T`."),
    ("a3_T6", "0^inf A> 1 1 1 (01)^k+2 1 1 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 0 1 0 1 1 1 (10)^k 1 1 1 1 1 1 1 0 1 1 0^inf",
     "Restart from `1^3 (01)^k T`."),
    ("b3_T3", "0^inf A> 1 0 1 0 1 1 1 1 (01)^k 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 1 0 1 1 1 (10)^k 1 1 1 1 0 1 1 0^inf",
     "Restart, second part, from `1 (01)^2 1^3 (01)^k T`."),
    ("b3_T6", "0^inf A> 1 0 1 0 1 1 1 1 (01)^k 1 1 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 1 0 1 1 1 (10)^k 1 1 1 1 1 1 1 0 1 1 0^inf",
     "Restart, second part, from `1 (01)^2 1^3 (01)^k T`."),
    ("q4_T3", "0^inf A> 1 1 1 1 0 1 1 1 1 (01)^k+2 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 0 1 0 1 1 1 1 1 1 (10)^k 1 1 1 1 0 1 1 0^inf",
     "Restart, last part: `1^4 0 1^4 (01)^(k+2) T` -> S(4, k)."),
    ("q5_T3", "0^inf A> 1 1 1 1 1 0 1 1 1 1 (01)^k+2 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 1 0 1 0 1 1 1 1 1 1 (10)^k 1 1 1 1 0 1 1 0^inf",
     "Restart, last part: `1^5 0 1^4 (01)^(k+2) T` -> S(5, k)."),
    ("q4_T6", "0^inf A> 1 1 1 1 0 1 1 1 1 (01)^k+2 1 1 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 0 1 0 1 1 1 1 1 1 (10)^k 1 1 1 1 1 1 1 0 1 1 0^inf",
     "Restart, last part: `1^4 0 1^4 (01)^(k+2) T` -> S(4, k)."),
    ("q5_T6", "0^inf A> 1 1 1 1 1 0 1 1 1 1 (01)^k+2 1 1 1 1 1 1 0 1 1 0^inf",
     "0^inf A> 1 1 1 1 1 0 1 0 1 1 1 1 1 1 (10)^k 1 1 1 1 1 1 1 0 1 1 0^inf",
     "Restart, last part: `1^5 0 1^4 (01)^(k+2) T` -> S(5, k)."),
]


def main():
    ths = [prove(M, name, a, b, doc=doc, rotate=True, count_first=True, max_seg=16)[0] for name, a, b, doc in RULES]
    sys.stdout.write(rules_file("Machine", "H130861", ths, f"Rules of {M}, generated by `rules.py`; do not edit by hand."))


if __name__ == "__main__":
    main()
