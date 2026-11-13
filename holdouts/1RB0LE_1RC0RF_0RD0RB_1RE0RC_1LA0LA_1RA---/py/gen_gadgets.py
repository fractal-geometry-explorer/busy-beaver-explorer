"""Writes lean/Gadgets.lean (the fill sweep) with bbtools.symtm.prove."""
import sys, os
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, '../../../tools/py'))
from bbtools import symtm
M = '1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA---'
txt, fin = symtm.prove(M, 'fill_raw', 'L 0^z+4 1 0 1 1 1 0 (10)^m 1 E> 0^inf', 'L 0^z 1 0 1 1 1 0 (10)^m+4 1 E> 0^inf',
                       doc='One fill sweep, with the end written as the run reaches it.')
print(fin, fin.steps, file=sys.stderr)
body = symtm.rules_file('Machine', 'H70977', [txt],
    'The fill sweep of 1RB0LE_1RC0RF_0RD0RB_1RE0RC_1LA0LA_1RA---, written by `py/gen_gadgets.py` (bbtools.symtm.prove).')
open(os.path.join(here, '../lean/Gadgets.lean'), 'w').write(body)
