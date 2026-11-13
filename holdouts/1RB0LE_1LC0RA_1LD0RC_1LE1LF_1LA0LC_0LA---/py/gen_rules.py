"""Write lean/Rules.lean: the cell-level pieces of one sweep of 1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---, proved by
bbtools.symtm.prove.  Run from anywhere: python3 holdouts/<M>/py/gen_rules.py"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = "1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---"
RULES = [
    # leaving the left end: the fuel block N and its separator
    ("start_s", "0^inf A> 1 (10)^n+1 0 1 1 0 0 R", "0^inf 1 0 (10)^n 1 1 0 1 0 1 0 1 B> R"),
    ("start_z", "0^inf A> 1 0 1 1 0 0 R", "0^inf 1 1 0 1 0 1 0 1 B> R"),
    # going right over a done block w = v+1 and its separator
    ("rb", "L B> (10)^v+1 0 1 1 0 0 R", "L (01)^v 1 0 1 0 1 0 1 B> R"),
    # coming back over a done block, entered in state A or D
    ("lbA", "L 1 (01)^v+3 1 0 1 0 1 0 A> 1 R", "L A> 1 1 0 (10)^v 0 1 1 0 0 1 0 1 0 1 0 R"),
    ("lbD", "L 1 (01)^v+3 1 0 1 0 1 0 D> 1 R", "L A> 1 1 0 (10)^v 0 1 1 0 0 1 0 1 0 0 1 R"),
    ("lb3A", "L 1 0 1 0 1 1 0 1 0 1 0 A> 1 R", "L A> 1 0 1 1 0 0 1 0 1 0 1 0 R"),
    ("lb3D", "L 1 0 1 0 1 1 0 1 0 1 0 D> 1 R", "L A> 1 0 1 1 0 0 1 0 1 0 0 1 R"),
    ("lb2A", "L 1 0 1 1 0 1 0 1 0 A> 1 R", "L D> 1 1 0 0 1 0 1 0 1 0 R"),
    ("lb2D", "L 1 0 1 1 0 1 0 1 0 D> 1 R", "L D> 1 1 0 0 1 0 1 0 0 1 R"),
    # back at the left end
    ("endA_s", "0^inf 1 0 (10)^n+2 1 1 0 1 0 1 0 A> 1 R", "0^inf A> 1 1 0 (10)^n 0 1 1 0 0 1 0 1 0 1 0 R"),
    ("endD_s", "0^inf 1 0 (10)^n+2 1 1 0 1 0 1 0 D> 1 R", "0^inf A> 1 1 0 (10)^n 0 1 1 0 0 1 0 1 0 0 1 R"),
    ("endA_2", "0^inf 1 0 1 0 1 1 0 1 0 1 0 A> 1 R", "0^inf A> 1 0 1 1 0 0 1 0 1 0 1 0 R"),
    ("endD_2", "0^inf 1 0 1 0 1 1 0 1 0 1 0 D> 1 R", "0^inf A> 1 0 1 1 0 0 1 0 1 0 0 1 R"),
    ("endA_0", "0^inf 1 1 0 1 0 1 0 A> 1 R", "0^inf A> 1 1 0 1 0 0 1 0 1 0 1 0 R"),
    ("endD_0", "0^inf 1 1 0 1 0 1 0 D> 1 R", "0^inf A> 1 1 0 1 0 0 1 0 1 0 0 1 R"),
    # the active window, entered in state B with the last cell of the block before it on the left
    ("w_pair_dot", "L 1 B> (10)^x+1 0 (10)^m+2 R", "L A> 1 1 0 (10)^x 1 0 1 (10)^m+1 R"),
    ("w_pair_bang", "L 1 B> (10)^x+1 1 (10)^m+2 R", "L A> 1 1 (01)^x+1 0 0 (10)^m+1 R"),
    ("w_append", "L 1 B> (10)^x+4 0 1 1 0 0 1 0 1 0^inf",
     "L A> 1 1 0 (10)^x 0 1 1 0 0 1 0 1 0 0 1 1 0 0 1 0 1 0^inf"),
    ("w_p1_bd", "L 1 B> (10)^x+1 1 1 0 0 R", "L A> 1 1 0 (10)^x+1 0 0 R"),
    ("w_p1_bb", "L 1 B> (10)^x+1 1 1 0 1 R", "L A> 1 1 0 (10)^x+1 0 1 R"),
    ("w_p1_db", "L 1 B> (10)^x+1 0 1 0 1 R", "L A> 1 1 0 (10)^x 1 0 1 1 R"),
    ("w_p1_dd0", "L 1 B> (10)^x+1 0 1 0 0 (10)^z 0 R", "L A> 1 1 0 (10)^x 1 0 1 0 (10)^z 0 R"),
    ("w_p1_dd1", "L 1 B> (10)^x+1 0 1 0 0 (10)^z 1 R", "L A> 1 1 0 (10)^x 1 0 1 0 (10)^z 1 R"),
    ("w_merge", "L 1 B> (10)^x+1 1 1 (10)^z 0 R", "L A> 1 1 0 (10)^x+1 (10)^z 0 R"),
    ("w_end_db", "L 1 B> (10)^x+1 0 1 0^inf", "L A> 1 1 0 (10)^x 1 0 1 0^inf"),
    ("w_next0", "L 1 B> (10)^x+4 0 0 (10)^z 0 R", "L A> 1 1 0 (10)^x 0 1 1 0 0 1 0 1 (10)^z 0 R"),
    ("w_next1", "L 1 B> (10)^x+4 0 0 (10)^z 1 R", "L A> 1 1 0 (10)^x 0 1 1 0 0 1 0 1 (10)^z 1 R"),
    ("w_end_b", "L 1 B> (10)^x+4 1 0^inf", "L A> 1 1 0 (10)^x+1 0 1 1 0 0 1 0 1 0^inf"),
    ("w_restart2", "L 1 B> (10)^x+4 0 0 0 1 1 0 0 R", "L A> 1 1 0 (10)^x 0 1 1 0 0 1 0 1 0 1 1 0 0 R"),
    # the window is the fuel block itself
    ("own_pair_dot", "0^inf A> 1 (10)^x 0 (10)^y+2 R", "0^inf A> 1 1 0 1 (01)^x 0 1 (10)^y+1 R"),
    ("own_pair_bang", "0^inf A> 1 (10)^x 1 (10)^y+2 R", "0^inf A> 1 1 0 1 (01)^x 0 0 (10)^y+1 R"),
]
ths = []
for name, s, e in RULES:
    ths.append(prove(M, name, s, e, doc=f"`{s}` reaches `{e}`.", rotate=True, max_moves=20000, max_seg=30,
                     count_first=True)[0])
out = rules_file("Machine", "H122192", ths,
                 "Cell-level pieces of a sweep of " + M + ", written by `py/gen_rules.py` with `bbtools.symtm.prove`.")
open(os.path.join(HERE, "../lean/Rules.lean"), "w").write(out)
print("wrote lean/Rules.lean")
