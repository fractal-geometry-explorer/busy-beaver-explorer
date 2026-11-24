"""Writes lean/Counter.lean: the counter rules of 1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---, proved with symtm.

The hub model (key and left side) is the one tools/py/bbtools/cjump.py learns at step 1.2e8; see the README.

usage: python3 holdouts/1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---/py/rules.py      (about a minute; then lean/check.sh)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import hubrules  # noqa: E402

text = hubrules.lean_file("1RB0RD_1LC1RE_1LD0LC_0LE0LC_0RA0RF_1RA---", 1.2e8, (87, 4, 0), (87, 2, '10', '01', 4, '1001', '0101'), "H124880")
with open(os.path.join(HERE, "..", "lean", "Counter.lean"), "w") as f:
    f.write(text)
