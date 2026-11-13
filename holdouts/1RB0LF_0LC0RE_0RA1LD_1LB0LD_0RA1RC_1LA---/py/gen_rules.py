"""Writes lean/Rules.lean: every crossing rule the block macro machine (blockmm.py) uses in its first N records,
each a Lean theorem `steps n start = some end` for every value of the word's parameter t and every tape in the
contexts L, R (bbtools.symtm.prove).  usage: python3 gen_rules.py [N]   (default 1e6)"""
import os, sys
import blockmm
from blockmm import macro_step, CFGS, M, ST
from bbtools import symtm

N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 6
here = os.path.dirname(os.path.abspath(__file__))
cur = ((), 0, [(0, 1), (1, 0)]); rec = 1
while rec < N:
    cur, st, _ = macro_step(*cur); rec += 1


def word(toks):
    return ' '.join(str(z) for z in toks)


def describe(key, why):
    if key[0] == 'R':
        sig, kind = key[1], key[2]
        ctx = ('left context ' + ''.join(map(str, sig[2]))) if sig[0] == 'R' else \
            ('blank tape, then ' + (''.join(map(str, sig[2])) or 'nothing'))
        res = {'R': 'it comes out on the right', 'L': 'it turns back left', 'rec': 'the next left record'}[why]
        return 'Moving right in state %s (%s), crossing the word %s: %s.' % (ST[sig[1]], ctx, word(kind), res)
    lam, kind, off = key[1], key[2], key[3]
    res = {'L': 'it comes out on the left', 'R': 'it turns back right', 'rec': 'the next left record'}[why]
    return 'Moving left in state %s (right context %s), crossing the word %s%s: %s.' % (
        ST[lam[1]], ''.join(map(str, lam[2])), word(kind), ' on blank tape' if off is not None else '', res)


out = []
items = sorted(CFGS.items(), key=lambda kv: repr(kv[0]))
nr = nl = 0
for key, (a, b, why) in items:
    if key[0] == 'R':
        name = 'right%d' % nr; nr += 1
    else:
        name = 'left%d' % nl; nl += 1
    txt, fin = symtm.prove(M, name, a, b, doc=describe(key, why), max_seg=16)
    out.append(txt)
txt = symtm.rules_file('Machine', 'H129771', out,
                       'The crossing rules of the block macro machine (`py/blockmm.py`) used in its first %d left records, '
                       'written by `py/gen_rules.py` with bbtools.symtm.prove: %d moving right, %d moving left.' % (N, nr, nl))
txt = txt.replace('namespace H129771', 'set_option maxRecDepth 20000\n\nnamespace H129771', 1)
open(os.path.join(here, '../lean/Rules.lean'), 'w').write(txt)
print('wrote', nr, 'right and', nl, 'left rules', file=sys.stderr)
