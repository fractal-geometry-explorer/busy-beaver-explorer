"""Write lean/Gap.lean: the rules of 1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC that work at any depth of the tape,
proved by bbtools.symtm.prove for every length and every tape left (`L`) and right (`R`) of the cells shown.
python3 holdouts/<M>/py/gen_gap.py

U x y w = (10)^x 00 (10)^y 110 0 1^w 0   (a unit).
g_cycle  0^6 A>0 U x (y+1) w   ->  A>0 U (x+3) y (w+2)          the cycle with six blank cells to grow into
g_q      1 A>1 U (x+1) (y+1) w  ->  E>0 0 U (x+1) y (w+2)         the cycle against a wall of 1s, all but its last
                                                               step (E0 -> 1LA): two 1s of the wall per cycle
g_turn   0^9 A>0 U x 0 w  ->  1^(2x+9) A>1 1 0 1^(w+4) 0         a unit whose y is 0 turns into a wall and a gap
g_ret    0^4 A>0 (10)^(x+1) 11 000  ->  A>0 U 1 x 2               back at a wall: the old x becomes the new y
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = "1RB0RA_1LC1RA_0LD1LD_0LE0LC_1LA0LF_---1LC"
U = "(10)^{x} 0 0 (10)^{y} 1 1 0 0 (1)^{w} 0 R"
RULES = [
    ("g_cycle", "L 0 0 0 0 0 0 A> 0 (10)^x 0 0 (10)^y+1 1 1 0 0 (1)^w 0 R",
     "L A> 0 1 0 1 0 1 0 (10)^x 0 0 1 (01)^y 1 0 0 1 1 (1)^w 0 R",
     "The cycle with six blank cells to the left."),
    ("g_q", "L 1 A> 1 (10)^x+1 0 0 (10)^y+1 1 1 0 0 (1)^w 0 R",
     "L E> 0 0 1 0 (10)^x 0 0 1 (01)^y 1 0 0 1 1 (1)^w 0 R",
     "The cycle against a wall of 1s, up to its last step (E then writes a 1 and steps left onto the wall)."),
    ("g_turn", "L 0 0 0 0 0 0 0 0 0 A> 0 (10)^x 0 0 1 1 0 0 (1)^w 0 R",
     "L 1 1 1 1 1 1 1 1 1 (11)^x A> 1 1 0 1 1 1 1 (1)^w 0 R",
     "A unit with y = 0 turns into a wall of 1s; its w-block, four longer, is about to be erased."),
    ("g_ret", "L 0 0 0 0 A> 0 (10)^x+1 1 1 0 0 0 R",
     "L A> 0 1 0 0 0 1 (01)^x 1 0 0 1 1 0 R",
     "The return: `(10)^(x+1) 11 000` becomes the unit x = 1, y = x, w = 2."),
]


def main():
    ths = []
    for name, s, e, doc in RULES:
        ths.append(prove(M, name, s, e, doc=f"{doc} `{s}` reaches `{e}`.", max_seg=30, count_first=True,
                         rotate=True)[0])
    out = rules_file("Machine", "H154944", ths, "Rules of " + M + " with any tape on both sides, written by "
                     "`py/gen_gap.py` with `bbtools.symtm.prove`.")
    open(os.path.join(HERE, "../lean/Gap.lean"), "w").write(out)
    print("wrote lean/Gap.lean")


if __name__ == "__main__":
    main()
