"""Write lean/Rules.lean and lean/CursorRules.lean: the six pieces of one round trip of the right-end regime, proved from the trace by
tools/py/bbtools/symtm.py (L, R are arbitrary tapes).

usage: python3 holdouts/1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---/py/gen_rules.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove, rules_file  # noqa: E402

M = "1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---"
RULES = [
    ("rightEnd", "L (1101010)^m+1 A> 0^inf", "L 1 A> 1 (1001100)^m+1 1 0^inf",
     "At the right end: A crosses the trailing `(1101010)^(m+1)` to the left."),
    ("crossL", "L (10)^k+2 1 A> 1 R", "L A> 1 (10)^k 0 1 1 0 0 R",
     "Moving left over one block `(10)^(k+2) 1`."),
    ("turnL", "0^inf A> 1 R", "0^inf 1 0 A> 0 R",
     "The turn at the left end: one new cell."),
    ("crossR0", "L A> 0 (10)^k R", "L (10)^k A> 0 R",
     "Moving right over the first block."),
    ("crossR", "L A> 0 0 1 1 0 0 (10)^k R", "L 1 1 0 1 0 (10)^k A> 0 R",
     "Moving right over one block, which is restored as `1 (10)^(k+2)`."),
    ("rightEnd2", "L A> 0 0 1 1 0 0 (1001100)^m 1 0^inf", "L 1 (1010101)^m 1 0 1 0 1 0 A> 0^inf",
     "Back at the right end: the trailing part becomes `(1101010)^(m+1)`."),
]
DOC = ("The pieces of one round trip of the right-end regime of " + M + ", written by `tools/py/bbtools/symtm.py` "
       "(`prove`, `rotate=True`) from the trace and checked by the kernel; `lean/Trip.lean` puts them together. "
       "Regenerate with `py/gen_rules.py`.")

CURSOR = [
    ("unitR", "L A> (01)^b 0 0 1 1 0 R", "L (10)^b 1 1 0 1 0 A> R",
     "Left-end phase, moving right over one unit `(01)^b 0 0110`."),
    ("unitL", "L (10)^b+2 1 1 0 1 0 A> 1 R", "L A> 1 (10)^b 0 1 1 0 0 1 0 1 0 R",
     "Left-end phase, moving left over one unit."),
    ("turnC1", "L 1 1 0 1 0 A> (01)^c+2 (10)^d+2 0 1 1 0 R", "L 1 1 0 1 0 A> 1 1 (01)^c+1 0 0 (10)^d+1 0 1 1 0 R",
     "The turn at a cursor `(01)^(c+2) (10)^(d+2) 0110`."),
    ("turnC2", "L 1 1 0 1 0 A> (01)^c+2 0 (01)^d+2 0 0 1 1 0 R",
     "L 1 1 0 1 0 A> 1 1 (01)^c+2 0 1 1 (01)^d 0 0 1 1 0 R",
     "The turn at a cursor `(01)^(c+2) 0 (01)^(d+2) 0 0110`."),
    ("edgeL", "0^inf A> 1 R", "0^inf A> 0 1 0 R", "The turn at the left end in the left-end phase."),
]
CDOC = ("The pieces of one round trip of the left-end (cursor) phase of " + M + ", written by "
        "`tools/py/bbtools/symtm.py` from the trace and checked by the kernel; `lean/Cursor.lean` puts them together. "
        "Regenerate with `py/gen_rules.py`.")


if __name__ == "__main__":
    texts = []
    for name, s, e, doc in RULES:
        text, _ = prove(M, name, s, e, doc=doc, rotate=True, count_first=True, max_seg=40)
        texts.append(text)
    with open(os.path.join(HERE, "..", "lean", "Rules.lean"), "w") as f:
        f.write(rules_file("Machine", "H14847", texts, DOC))
    texts = []
    for name, s, e, doc in CURSOR:
        text, _ = prove(M, name, s, e, doc=doc, rotate=True, count_first=True, max_seg=40)
        texts.append(text)
    with open(os.path.join(HERE, "..", "lean", "CursorRules.lean"), "w") as f:
        f.write(rules_file("Machine", "H14847", texts, CDOC))
