"""Writes lean/RulesTwin1.lean and lean/RulesTwin2.lean: the crossing rules that the block macro machine (blockmm.py) uses on the twin's run
(1RB0RA_0RC0LE_0LD1RA_1LB0RF_0LD1LC_1RD---, which is this table mirrored and started in state D; lean/Twin29537.lean)
in its first N records and that this machine's own first N records do not use (those are in lean/Rules.lean).
Each is a Lean theorem `steps n start = some end` for every value of the word's parameter t and every tape in the
contexts L, R (bbtools.symtm.prove).  usage: python3 gen_rules_twin.py [N]   (default 3e5)"""
import os, sys
import blockmm
from blockmm import macro_step, CFGS, M
from bbtools import symtm
from gen_rules_lib import describe

N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 3 * 10 ** 5
here = os.path.dirname(os.path.abspath(__file__))
cur = ((), 0, [(0, 1), (1, 0)]); rec = 1
while rec < N:
    cur, st, _ = macro_step(*cur); rec += 1
own = set(CFGS)
# the twin's record 6 (lean/Twin29537.lean, twin_reach157): 0^inf B> 0 (10)^3 0 0 (10) 1 (10) 1 (10) 1 (10)
cur = ((), 0, [(3, 0), (0, 0), (1, 1), (1, 1), (1, 1), (1, 0)]); rec = 6
while rec < N:
    cur, st, _ = macro_step(*cur); rec += 1
new = sorted(((k, v) for k, v in CFGS.items() if k not in own), key=lambda kv: repr(kv[0]))
out = []
nr = nl = 0
for key, (a, b, why) in new:
    if key[0] == 'R':
        name = 'twin_right%d' % nr; nr += 1
    else:
        name = 'twin_left%d' % nl; nl += 1
    txt, fin = symtm.prove(M, name, a, b, doc=describe(key, why), max_seg=16)
    out.append(txt)
half = (len(out) + 1) // 2
for part, chunk in ((1, out[:half]), (2, out[half:])):
    txt = symtm.rules_file('Machine', 'H129771', chunk,
                           'Part %d of 2 of the crossing rules of the block macro machine (`py/blockmm.py`) used in the first '
                           '%d left records of the twin run (this table started in state D, `Twin29537.lean`) and not in the '
                           'first %d records of this machine\'s own run (`Rules.lean`), written by `py/gen_rules_twin.py`; '
                           'the two parts hold %d moving right, %d moving left.' % (part, N, N, nr, nl))
    txt = txt.replace('namespace H129771', 'set_option maxRecDepth 20000\n\nnamespace H129771', 1)
    open(os.path.join(here, '../lean/RulesTwin%d.lean' % part), 'w').write(txt)
print('own rules', len(own), 'twin adds', nr, 'right and', nl, 'left rules', file=sys.stderr)
