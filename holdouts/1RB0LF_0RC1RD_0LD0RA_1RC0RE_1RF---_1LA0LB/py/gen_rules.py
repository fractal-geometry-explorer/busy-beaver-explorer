"""Write lean/Rules.lean: symbolic rules of 1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB proved by bbtools.symtm.

usage: python3 holdouts/1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB/py/gen_rules.py > .../lean/Rules.lean
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..', 'tools', 'py'))
from bbtools.symtm import prove  # noqa: E402

M = '1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB'

RULES = [
    ('sweep_train',
     'One sweep while the head bounces between the right end and a train (the second sea `1110`): the last word '
     '`1110` of the train becomes `1010`, the sea in front of it grows by two words `10`, and the right end grows by '
     'two cells.',
     'L 1 1 1 0 (10)^b+1 1 1 0 1 1 0 (10)^a+1 1 1 C> 0^inf',
     'L (10)^b+3 1 1 0 1 1 0 (10)^a+2 1 1 C> 0^inf'),
]


def main():
    out = ['import Machine', '', '/-!', f'# {M}: symbolic rules',
           '', 'Written by `py/gen_rules.py` with `bbtools.symtm.prove`; each theorem holds for every value of its',
           'variables and every tape in its contexts.', '-/', '', 'namespace H79385', '', 'open TM', '',
           'set_option maxRecDepth 100000', '']
    for name, doc, s, e in RULES:
        txt, _ = prove(M, name, s, e, doc=doc, rotate=True, count_first=True, max_seg=40)
        out.append(txt)
        out.append('')
    out.append('end H79385')
    print('\n'.join(out))


if __name__ == '__main__':
    main()
