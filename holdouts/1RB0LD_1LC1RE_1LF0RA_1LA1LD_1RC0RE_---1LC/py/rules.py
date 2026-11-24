"""Writes lean/Counter.lean: the counter rules of 1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC, proved with symtm.

The hub model (key and left side) is the one tools/py/bbtools/cjump.py learns at step 9.6e8; see the README.

usage: python3 holdouts/1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC/py/rules.py      (about a minute; then lean/check.sh)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import hubrules  # noqa: E402

text = hubrules.lean_file("1RB0LD_1LC1RE_1LF0RA_1LA1LD_1RC0RE_---1LC", 9.6e8, (-136, 0, 0), (-136, 2, '00', '11', 2, '00', '11'), "H125234")
with open(os.path.join(HERE, "..", "lean", "Counter.lean"), "w") as f:
    f.write(text)
