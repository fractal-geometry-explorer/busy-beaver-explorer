"""Write lean/Rules.lean (or ClockRules.lean) and lean/Clock.lean for the members registered by clockx.py, with
gen_clock.py of the first clock batch (the clock of a renamed table is proved on the member's own table).

usage (from the repository root): python3 holdouts/R02-clock-word/py/gen_clockx.py [MACHINE...]
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
import clockx  # noqa: E402  (registers the members in clock.py before gen_clock reads its tables)
sys.path.insert(0, os.path.join(HERE, "..", "..", "1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE", "py"))
import gen_clock  # noqa: E402

for m in sys.argv[1:] or list(clockx.DERIVED):
    gen_clock.main(m)
