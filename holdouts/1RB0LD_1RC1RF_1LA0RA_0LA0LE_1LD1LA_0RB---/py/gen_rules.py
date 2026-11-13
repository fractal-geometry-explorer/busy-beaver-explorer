"""Write lean/Rules.lean: the cell-level rules of 1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---, proved by
bbtools.symtm.prove.  Run from anywhere: python3 holdouts/<M>/py/gen_rules.py"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = "1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---"
RULES = [
    ("sweep_cells", "0^inf A> 0 (10)^x 0 10 0^z+3 R", "0^inf A> 0 1 0 (10)^x 1 0 0 1 (0)^z+1 R",
     "One sweep: `A>0 (10)^x 0 10 0^(z+3)` becomes `A>0 (10)^(x+2) 0 10 0^z` (written as the run leaves it)."),
]
ENDS = [
    ("end0s", "0^inf A> 0 (10)^x+1 0 10 (10)^y 0 1 0^inf",
     "0^inf A> 0 0 1 0 0 (00)^x+1 1 0 1 0 (10)^y 1 0 1 0 0 1 0^inf"),
    ("end1s", "0^inf A> 0 (10)^x+1 0 10 0 (10)^y+1 0 1 0^inf",
     "0^inf A> 0 0 1 0 0 0 0 (00)^x+1 0 0 1 0 1 0 1 0 (10)^y 1 0 1 0 1 0 1 0 0 1 0^inf"),
    ("end2s", "0^inf A> 0 (10)^x+1 0 10 0 0 (10)^y+1 0 1 0^inf",
     "0^inf A> 0 0 1 0 0 0 0 (00)^x+1 0 0 0 0 0 (10)^y 0 1 0^inf"),
    ("end0z", "0^inf A> 0 0 10 (10)^y 0 1 0^inf", "0^inf A> 0 0 1 0 0 1 0 1 0 (10)^y 1 0 1 0 0 1 0^inf"),
    ("end1z", "0^inf A> 0 0 10 0 (10)^y+1 0 1 0^inf",
     "0^inf A> 0 0 1 0 0 0 0 0 0 1 0 1 0 1 0 (10)^y 1 0 1 0 1 0 1 0 0 1 0^inf"),
    ("end2z", "0^inf A> 0 0 10 0 0 (10)^y+1 0 1 0^inf", "0^inf A> 0 0 1 0 0 0 0 0 0 0 0 0 (10)^y 0 1 0^inf"),
]
ths = []
for name, s, e, doc in RULES:
    ths.append(prove(M, name, s, e, doc=doc)[0])
for name, s, e in ENDS:
    ths.append(prove(M, name, s, e, doc=f"`{s}` reaches `{e}`.", max_moves=10000, max_seg=30, count_first=True)[0])
out = rules_file("Machine", "H141950", ths,
                 "Cell-level rules of " + M + ", written by `py/gen_rules.py` with `bbtools.symtm.prove`.")
open(os.path.join(HERE, "../lean/Rules.lean"), "w").write(out)
print("wrote lean/Rules.lean")
