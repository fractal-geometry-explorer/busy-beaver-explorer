"""Write lean/WalkRules.lean: the cell-level bounce rules of the reflector Q of this machine, proved by
bbtools.symtm.prove.  Run from anywhere: python3 holdouts/<M>/py/gen_walk.py

When the last run of pairs is used up, the head bounces between the right end of the tape (blank beyond it, state
E) and a reflector Q, a single extra cell in a background of pairs 01: an extra 0 (short form) or an extra 1 (long
form).  Each bounce moves Q two cells to the left and the right end two cells to the right."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = os.path.basename(os.path.dirname(HERE))
RULES = [
    ("bounce0_cells", "L (01)^c+1 0 (01)^a+1 E> 0^inf", "L (01)^c 1 (01)^a+3 E> 0^inf",
     "One bounce with Q in its short form: `L (01)^(c+1) 0 (01)^(a+1) E>` becomes `L (01)^c 1 (01)^(a+3) E>` "
     "(stated as the run writes it)."),
    ("bounce1_cells", "L (01)^c+1 1 (01)^a+1 E> 0^inf", "L (01)^c 0 (01)^a+3 E> 0^inf",
     "One bounce with Q in its long form: `L (01)^(c+1) 1 (01)^(a+1) E>` becomes `L (01)^c 0 (01)^(a+3) E>` "
     "(stated as the run writes it)."),
]
ths = [prove(M, name, s, e, doc=doc)[0] for name, s, e, doc in RULES]
out = rules_file("Machine", "H71372", ths, "Bounce rules of the reflector Q of " + M +
                 ", written by `py/gen_walk.py` with `bbtools.symtm.prove`.")
open(os.path.join(HERE, "../lean/WalkRules.lean"), "w").write(out)
print("wrote lean/WalkRules.lean")
