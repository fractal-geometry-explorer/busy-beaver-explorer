"""Write lean/Rules.lean: one round trip of the first regime, proved from the trace by tools/py/bbtools/symtm.py.

usage: python3 holdouts/1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC/py/gen_rules.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove, rules_file  # noqa: E402

M = "1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC"
RULES = [
    ("trip1", "0^inf A> (01110)^a+1 0 1 1 1 1 (001)^a+1 0 1 1 1 1 0 1 1 1 1 R",
     "0^inf A> (01110)^a+2 0 1 1 1 1 (001)^a+2 0 1 1 1 1 R"),
    ("cycle3", "0^inf A> (01110)^a+1 0 1 1 1 1 (001)^c+1 1 1 0 0 1 0 0 1 1 1 1 (001)^d+9 1 1 0 0 1 0^inf",
     "0^inf A> (01110)^a+15 0 1 1 1 1 (001)^c+1 1 1 0 0 1 0 0 1 1 1 1 (001)^d+5 1 1 0 0 1 0^inf"),
]
DOC = ("Round trips of " + M + " proved from the trace by `tools/py/bbtools/symtm.py` (`prove`, `rotate=True`) and "
       "checked by the kernel. Regenerate with `py/gen_rules.py`.")

if __name__ == "__main__":
    texts = [prove(M, n, s, e, rotate=True, count_first=True, max_seg=40)[0] for n, s, e in RULES]
    with open(os.path.join(HERE, "..", "lean", "Rules.lean"), "w") as f:
        f.write(rules_file("Machine", "H91503", texts, DOC).replace("open TM\n", "open TM\n\nset_option maxRecDepth 20000\n", 1))
