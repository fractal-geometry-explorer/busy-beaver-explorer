"""Write lean/Rules.lean: the cell-level rules of the moving particle Q of this machine, proved by
bbtools.symtm.prove.  Run from anywhere: python3 holdouts/<M>/py/gen_rules.py"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = os.path.basename(os.path.dirname(HERE))
NS = {"1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---": "H54407",
      "1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RA1LF_0LC---": "H86275"}[M]
RULES = [
    ("bounce0_cells", "0^inf 1 A> 1 0 (10)^a 0 (10)^c+2 R", "0^inf 1 A> 1 0 1 0 1 (01)^a 0 1 (10)^c+1 R",
     "One bounce with Q in its short form: `1 A>1 0 (10)^a 0 (10)^(c+2)` becomes `1 A>1 0 (10)^(a+2) 1 1 0 (10)^c` "
     "(written as the run leaves it)."),
    ("bounce1_cells", "0^inf 1 A> 1 0 (10)^a 1 1 0 (10)^c+1 R", "0^inf 1 A> 1 0 1 0 1 (01)^a 0 0 (10)^c+1 R",
     "One bounce with Q in its long form: `1 A>1 0 (10)^a 1 1 0 (10)^(c+1)` becomes `1 A>1 0 (10)^(a+2) 0 (10)^(c+1)` "
     "(written as the run leaves it)."),
]
ths = [prove(M, name, s, e, doc=doc)[0] for name, s, e, doc in RULES]
out = rules_file("Machine", NS, ths, "Cell-level rules of " + M + ", written by `py/gen_rules.py` with `bbtools.symtm.prove`.")
open(os.path.join(HERE, "../lean/Rules.lean"), "w").write(out)
print("wrote lean/Rules.lean")
