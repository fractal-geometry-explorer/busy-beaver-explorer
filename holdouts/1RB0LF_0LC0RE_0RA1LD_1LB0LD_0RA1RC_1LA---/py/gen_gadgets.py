"""Writes lean/Gadgets.lean with bbtools.symtm.prove."""
import sys, os
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, '../../../tools/py'))
from bbtools import symtm
M = '1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---'
G = [('short_raw', '0^inf B> 0 (1010)^x+2 1 0 0 0 R', '0^inf B> 0 (1010)^x+2 1 1 0 1 1 0 R',
      'The short sweep at the left end, `1 0^3` after the first block becoming `1^2 0 1^2 0`, as the run writes it.')]
out = []
for name, a, b, doc in G:
    txt, fin = symtm.prove(M, name, a, b, doc=doc)
    print(name, fin, fin.steps, file=sys.stderr)
    out.append(txt)
open(os.path.join(here, '../lean/Gadgets.lean'), 'w').write(symtm.rules_file('Machine', 'H129771', out,
    'Gadgets of 1RB0LF_0LC0RE_0RA1LD_1LB0LD_0RA1RC_1LA---, written by `py/gen_gadgets.py` (bbtools.symtm.prove).'))
