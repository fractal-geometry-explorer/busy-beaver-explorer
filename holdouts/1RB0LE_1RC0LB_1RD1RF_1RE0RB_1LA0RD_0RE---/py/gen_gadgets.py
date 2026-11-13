"""Writes the cell-level gadget lemmas of lean/Gadgets.lean with bbtools.symtm.prove (run from this folder)."""
import sys, os
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, '../../../tools/py'))
from bbtools import symtm
M = '1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---'
G = [
 ('sgad', 'L 0 1 1 0 0 A> 1 R', 'L A> 1 (10)^2 1 R', 'The S-gadget: the leftward signal crosses a separator `01100`, which becomes `(10)^2 1` on its right.'),
 ('turn1', 'L 1 A> 1 (10)^Y 1 R', 'L 0 (10)^Y+1 D> R', 'The turn at a defect `1`: it becomes `0`, the first right block grows by one and `D` starts right.'),
 ('turn0', 'L (10)^x+2 0 A> 1 (10)^Y 1 R', 'L (10)^x 1 (10)^Y+3 D> R', 'The turn at a defect `0` with a block of at least 2 before it.'),
 ('dunit', 'L D> (10)^s+2 1 R', 'L 0 1 1 0 0 (10)^s D> R', 'The rightward `D` unit: `(10)^(s+2) 1` becomes a separator and `(10)^s`.'),
]
out = []
for name, a, b, doc in G:
    txt, fin = symtm.prove(M, name, a, b, doc=doc)
    print(name, fin, fin.steps, file=sys.stderr)
    out.append(txt)
body = symtm.rules_file('Machine', 'H3006', out, 'Cell-level gadgets of 1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---, written by `py/gen_gadgets.py` (bbtools.symtm.prove).')
open(os.path.join(here, '../lean/Gadgets.lean'), 'w').write(body)
