"""Write lean/Rules.lean: the phase cycle of 1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC for the four parities of
(x, y), proved by bbtools.symtm.prove for every length.  python3 holdouts/<M>/py/gen_rules.py

P x y w R = `A>0 (10)^x 00 (10)^y 110 0 1^w 0 R` (head A on the left end, blank tape to the left).  One cycle (two
visits of the left end) gives P (x+3) (y-1) (w+2) R, in 8x + 4y + 26 steps.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = "1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC"
CASES = [  # name, x as written, y as written, end as the run writes it
    ("cyc_ee", "(1010)^a", "(1010)^b 1 0", "1 0 1 0 1 0 (1010)^a 0 0 1 (0101)^b 1 0 0 1 1 (1)^w 0 R",
     "x = 2a, y = 2b+1"),
    ("cyc_eo", "(1010)^a", "(1010)^b+1", "1 0 1 0 1 0 (1010)^a 0 0 1 0 1 (0101)^b 1 0 0 1 1 (1)^w 0 R",
     "x = 2a, y = 2b+2"),
    ("cyc_oe", "(1010)^a 1 0", "(1010)^b 1 0", "1 0 1 0 1 0 1 0 (1010)^a 0 0 1 (0101)^b 1 0 0 1 1 (1)^w 0 R",
     "x = 2a+1, y = 2b+1"),
    ("cyc_oo", "(1010)^a 1 0", "(1010)^b+1", "1 0 1 0 1 0 1 0 (1010)^a 0 0 1 0 1 (0101)^b 1 0 0 1 1 (1)^w 0 R",
     "x = 2a+1, y = 2b+2"),
]


def main():
    ths = []
    for name, X, Y, E, what in CASES:
        s = f"0^inf A> 0 {X} 0 0 {Y} 1 1 0 0 (1)^w 0 R"
        e = f"0^inf A> 0 {E}"
        ths.append(prove(M, name, s, e, doc=f"One cycle with {what}: `{s}` reaches `{e}`.", max_seg=30,
                         count_first=True, rotate=True)[0])
    out = rules_file("Machine", "H154944", ths, "The phase cycle of " + M + ", written by `py/gen_rules.py` with "
                     "`bbtools.symtm.prove`.")
    open(os.path.join(HERE, "../lean/Rules.lean"), "w").write(out)
    print("wrote lean/Rules.lean")


if __name__ == "__main__":
    main()
