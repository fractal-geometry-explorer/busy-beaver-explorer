"""Write lean/Rules.lean: the main-regime cycle proved from the trace by tools/py/bbtools/symtm.py.

usage: python3 holdouts/1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD/py/gen_rules.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove, rules_file  # noqa: E402

M = "1RB0LE_1RC---_0RD0RE_1LE0RB_0LA0LF_0RC0LD"
TAIL = "0 1 0 0 0 1 0 1 0 0 0 0 1"
START = f"0^inf F> 0 0 0 0 0 0 (1000)^a 1 0 1 1 1 (0001)^b+3 {TAIL} 0^inf"
END = f"0^inf F> 0 0 0 0 0 0 (1000)^a+6 1 0 1 1 1 (0001)^b+1 {TAIL} 0^inf"
DOC = ("The main-regime cycle of " + M + ": three round trips from "
       "`F>0^6 (1000)^a 1 0 1 1 1 (0001)^(b+3) 0 1 0 0 0 1 0 1 0 0 0 0 1`, written by `tools/py/bbtools/symtm.py` "
       "(`prove`, `rotate=True`) from the trace and checked by the kernel. Regenerate with `py/gen_rules.py`.")

if __name__ == "__main__":
    text, _ = prove(M, "phase3", START, END, rotate=True, count_first=True, max_seg=40)
    with open(os.path.join(HERE, "..", "lean", "Rules.lean"), "w") as f:
        f.write(rules_file("Machine", "H100726", [text], DOC))
