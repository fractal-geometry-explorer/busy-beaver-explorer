"""Top-part forecast for 1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE (21 November 2026, group C).

The method and the code are in holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/forecast.py (reduced model: the top digits of an
exact digit-model state plus zero digits with huge runs, run by the exact condition-macro engine cmacro.py, with
whole overflow cycles of the top part jumped while they are translations).  This file only selects this machine.

    python3 py/forecast.py test [SECONDS]
    python3 py/forecast.py validate PKL P Q PC SECONDS
    python3 py/forecast.py horizon PKL P
    python3 py/forecast.py run PKL P Q CYCLES SECONDS [OUT.pkl]
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA', 'py'))
import forecast  # noqa: E402

if __name__ == '__main__':
    sys.exit(forecast.main(['1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE'] + sys.argv[1:]))
