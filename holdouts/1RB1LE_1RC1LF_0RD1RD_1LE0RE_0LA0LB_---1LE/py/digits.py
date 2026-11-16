"""The digit model of 1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE (16 November 2026): an exact simulator at the
left-end visits (one sample per counter round), for blank tape started in state A, or in state B (the question
equivalent to its twin 1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---1LD, proved in the twin's lean/Twin.lean).

The tape is read MIRRORED, so that the generic window engine of
holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/digits.py (class Spec, reused unchanged) applies: we run the
mirror machine 1LB1RE_1LC1RF_0LD1LD_1RE0LE_0RA0RB_---1RE, whose run from blank tape is the original one reflected.
A sample is the head in state E on the blank cell right of the tape (left of it, in the original).  Mirrored, the
tape is then 0^inf, digits `(110)^r W` (a run of r words 110, then a wall W), the last run `(110)^n0`, then the
end cells `11` (or `1` in the rounds just after an overflow).  Walls, as blocks 1^a 0^b: W0 = 1/1, W1 = 3/1,
W2 = 3/1 1/1, W3 = 4/1 (the counter digits 0..3 of the README, mirrored, with the word 110 that follows them in
the README's notation taken into the wall), and X5 = 5/1, X6 = 6/1, which appear briefly after overflows.
`sweep` (Spec.sweep) runs the machine SYMBOLICALLY (tools/py/bbtools/symtm.py) on a window holding the carry
chain (the W3 digits next to the end) and the stop digit, more digits if needed, the whole tape at an overflow
(then the run goes to the far end and back, the "right-end visit"), with long runs as variables, and caches each
rule by its window shape.  Every number is a machine run, not a model guess.

usage: python3 digits.py check FILE [B]     compare with the samples of the C sampler (c/sampb.c) in FILE
"""
import importlib.util
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', '..', '..')
_p = os.path.join(ROOT, 'holdouts', '1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA', 'py', 'digits.py')
_spec = importlib.util.spec_from_file_location('digits_generic_1RB0LF', _p)
G = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(G)
symtm = G.symtm
show = G.show

M = '1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE'
MIRROR = '1LB1RE_1LC1RF_0LD1LD_1RE0LE_0RA0RB_---1RE'
SHAPES = {'W0': [(1, 1)], 'W1': [(3, 1)], 'W2': [(3, 1), (1, 1)], 'W3': [(4, 1)], 'X5': [(5, 1)], 'X6': [(6, 1)]}
class AutoSpec(G.Spec):
    """Spec with one addition: a block 1^a 0^b that is neither a run nor part of a known wall becomes a new wall
    `b<a>_<b>` (a name only, so that more tapes can be read; every rule is still a symbolic run of the machine)."""

    def parse_blocks(self, b):
        for x in b:
            if x[0] != 'R' and not any(x in bl for bl in self.shapes.values()):
                self.shapes['b%d_%d' % x] = [x]
                self.order = sorted(self.shapes.items(), key=lambda kv: -len(kv[1]))
        return G.Spec.parse_blocks(self, b)


SPEC = AutoSpec(MIRROR, (2, 1), SHAPES, None, 'E', 0, pairs=False, ends={'E': '11', 'E1': '1'})
CARRY = ('W3',)


def cells_of(tokens):
    """The mirrored cells of a sampler line (tokens Pn and a/b), as 'B...'."""
    out = ['B']
    for t in tokens:
        if t[0] == 'P':
            out.append('110' * int(t[1:]))
        else:
            a, b = t.split('/')
            out.append('1' * int(a) + '0' * int(b))
    return ''.join(out)


def samples(path):
    """(step, cells) for each 'S' line of a c/sampb.c output."""
    for line in open(path):
        a = line.split()
        if a and a[0] == 'S':
            yield int(a[1]), cells_of(a[2:])
        elif a and a[0] == 'HALT':
            print('direct run HALTS at', a[1])


def parse(cells):
    a = SPEC.parse_cells(cells)
    return None if a is None else (a[0], list(a[1]), a[2], a[3])


def check(path):
    st = T = None
    n = bad = unp = 0
    for step, cells in samples(path):
        a = parse(cells)
        if a is None:
            unp += 1
            print('unparsed sample at', step, cells[:200])
            st = None
            continue
        if st is not None:
            n += 1
            if st != a or T != step:
                bad += 1
                print('MISMATCH at step', step, show(st)[:300], 'expected', show(a)[:300])
        r = SPEC.sweep(a, carry=CARRY)
        if r[0] == 'ok':
            st, T = r[1], step + r[2]
        else:
            print('no rule at', step, r[0], show(a)[:300])
            st = T = None
    print(f'{n} sweeps compared with the direct run: {bad} mismatches, {unp} unparsed samples; '
          f'{len(SPEC.memo)} window rules derived')
    return bad == 0


if __name__ == '__main__':
    if sys.argv[1] == 'check':
        sys.exit(0 if check(sys.argv[2]) else 1)
