"""The digit model of 1RB---_1RC1RF_1LD1RA_1LB0LE_1LF1LF_0RB0LD (16 November 2026): an exact simulator at the
left-end visits in state D (one sample per counter round).

The tape is read MIRRORED, so that the generic window engine of
holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/digits.py (class Spec, reused unchanged) applies: we run the
mirror machine 1LB---_1LC1LF_1RD1LA_1RB0RE_1RF1RF_0LB0RD.  A sample is the head in state D on the blank cell right
of the tape.  Mirrored, the tape is then 0^inf, digits `(100)^r W` (a run of r background words 100, then a wall
W), the last run `(100)^n0`, then the end cells `10`.  Walls, as blocks 1^a 0^b: Q = 2/1 (the README's defect q),
R = 1/4 (r), S = 1/1 1/1 (s), P = 1/3 (p), T = 1/1 (the far end, END, and the clusters it leaves) and X6 = 1/6.
`sweep` (Spec.sweep) runs the machine SYMBOLICALLY (tools/py/bbtools/symtm.py) on a window holding the carry chain
and the stop digit (more digits if the run needs them; the whole tape at an overflow), long runs as variables, and
caches each rule by its window shape.  Every number is a machine run, not a model guess.

usage: python3 digits.py check FILE     compare with the samples of a C sampler output FILE ("S step blocks")
"""
import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', '..', '..')
_p = os.path.join(ROOT, 'holdouts', '1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA', 'py', 'digits.py')
_spec = importlib.util.spec_from_file_location('digits_generic_1RB0LF', _p)
G = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(G)
symtm = G.symtm
show = G.show

M = '1RB---_1RC1RF_1LD1RA_1LB0LE_1LF1LF_0RB0LD'
MIRROR = '1LB---_1LC1LF_1RD1LA_1RB0RE_1RF1RF_0LB0RD'
SHAPES = {'Q': [(2, 1)], 'R': [(1, 4)], 'S': [(1, 1), (1, 1)], 'P': [(1, 3)], 'T': [(1, 1)], 'X6': [(1, 6)]}
class AutoSpec(G.Spec):
    """Spec with one addition: a block 1^a 0^b that is neither a run nor part of a known wall becomes a new wall
    `b<a>_<b>` (a name only, so that more tapes can be read; every rule is still a symbolic run of the machine)."""

    def parse_blocks(self, b):
        for x in b:
            if x[0] != 'R' and not any(x in bl for bl in self.shapes.values()):
                self.shapes['b%d_%d' % x] = [x]
                self.order = sorted(self.shapes.items(), key=lambda kv: -len(kv[1]))
        return G.Spec.parse_blocks(self, b)


SPEC = AutoSpec(MIRROR, (1, 2), SHAPES, None, 'D', 0, pairs=False, ends={'E': '10'})
CARRY = ('S',)


def cells_of(tokens, rw='100'):
    out = ['B']
    for t in tokens:
        if t[0] == 'P':
            out.append(rw * int(t[1:]))
        else:
            a, b = t.split('/')
            out.append('1' * int(a) + '0' * int(b))
    return ''.join(out)


def samples(path):
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
