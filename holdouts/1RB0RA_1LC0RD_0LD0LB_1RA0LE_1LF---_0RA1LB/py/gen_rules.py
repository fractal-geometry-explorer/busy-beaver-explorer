"""Write lean/Rules.lean: the transfer cycle of 1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RA1LB, proved by
bbtools.symtm.prove for every length.  python3 holdouts/<M>/py/gen_rules.py

The gadget G = `0 1 0 1 0 111 0 1 00 1 0 11 0` sits at the left end of the tape (head C on its first cell, blank
tape to the left).  Right of it: (10)^X, the marker 111 0, and the rest R of the tape.  One cycle (three visits of the
left end, fifteen trips of the head to the marker and back) moves the marker 12 pairs to the left and leaves 15 pairs
`10` behind it: G (10)^(X+12) 111 0 R  ->  G (10)^X 111 0 (10)^15 R, for even X.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = "1RB0RA_1LC0RD_0LD0LB_1RA0LE_1LF---_0RA1LB"
G = "0 1 0 1 0 1 1 1 0 1 0 0 1 0 1 1 0"
TEN15 = " ".join(["1 0"] * 15)


def main():
    ths = []
    s = f"0^inf C> {G} (1010)^x+6 1 1 1 0 R"
    e = f"0^inf C> {G} 1 (0101)^x 1 1 0 {TEN15} R"
    ths.append(prove(M, "cycle_cells", s, e, doc="One transfer cycle, as the run writes it: `G (1010)^(x+6) 111 0 R` "
                     "reaches `G 1 (0101)^x 110 (10)^15 R`, which is `G (10)^(2x) 111 0 (10)^15 R`.",
                     max_seg=30, count_first=True, rotate=True)[0])
    out = rules_file("Machine", "H65987", ths, "The transfer cycle of " + M + ", written by `py/gen_rules.py` with "
                     "`bbtools.symtm.prove`.")
    open(os.path.join(HERE, "../lean/Rules.lean"), "w").write(out)
    print("wrote lean/Rules.lean")


if __name__ == "__main__":
    main()
