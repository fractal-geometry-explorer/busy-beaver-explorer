"""Write lean/Rules.lean: symbolic rules of 1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF proved by bbtools.symtm.

usage: python3 holdouts/1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF/py/gen_rules.py > .../lean/Rules.lean
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..', 'tools', 'py'))
from bbtools.symtm import prove  # noqa: E402

M = '1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF'
G = '0 0 1 0 0 1 0 1 1 1 0'          # the left gadget, phase 0, read from the head

RULES = [
    # (name, doc, start, end)
    ('cycleP',
     'One cycle of the left gadget with a P particle (`0 0 1 0 1 1`) as the first particle: the gadget moves 8 cells '
     'left, the sea between gadget and P loses 4 cells, the sea behind P gains 12 (P moves 12 cells left).',
     f'0^inf F> {G} 0 1 (0101)^x+4 0 0 1 0 1 1 (1010)^y R',
     f'0^inf F> {G} 0 1 (0101)^x+3 0 0 1 0 1 1 (1010)^y+3 R'),
]


def main():
    out = ['import Machine', '', '/-!', f'# {M}: symbolic rules',
           '', 'Written by `py/gen_rules.py` with `bbtools.symtm.prove`; each theorem holds for every value of its',
           'variables and every tape in its contexts.', '-/', '', 'namespace H147837', '', 'open TM', '',
           'set_option maxRecDepth 100000', '']
    for name, doc, s, e in RULES:
        txt, _ = prove(M, name, s, e, doc=doc, rotate=True, count_first=True, max_seg=40)
        out.append(txt)
        out.append('')
    out.append('end H147837')
    print('\n'.join(out))


if __name__ == '__main__':
    main()
