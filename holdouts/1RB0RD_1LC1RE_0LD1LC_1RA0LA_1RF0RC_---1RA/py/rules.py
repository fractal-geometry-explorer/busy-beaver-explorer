"""Writes lean/Counter.lean: the counter rules of 1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA, proved with symtm.

The hub model (key and left side) is the one tools/py/bbtools/cjump.py learns at step 5.92e9; see the README.

usage: python3 holdouts/1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA/py/rules.py      (about a minute; then lean/check.sh)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import hubrules  # noqa: E402

text = hubrules.lean_file("1RB0RD_1LC1RE_0LD1LC_1RA0LA_1RF0RC_---1RA", 5.92e9, (-125, 0, 1), (-126, 1, '1', '0', 5, '11011', '01011'), "H25604")
with open(os.path.join(HERE, "..", "lean", "Counter.lean"), "w") as f:
    f.write(text)
