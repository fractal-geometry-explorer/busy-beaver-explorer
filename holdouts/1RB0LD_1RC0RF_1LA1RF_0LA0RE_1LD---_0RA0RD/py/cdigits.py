"""The digit model of 1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD (c2) and of its mirror image
1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB (c1) at the bouncing end (24 November 2026): an exact simulator from one
sample to the next.

Between the right-end records of c2 the head bounces at the LEFT end of the tape, and each bounce sends a carry
through a ternary counter.  c2 is read MIRRORED (the machine 1LB0RD_1LC0LF_1RA1LF_0RA0LE_1RD---_0LA0LD), so that its
bouncing end is on the right, as it is natively for c1.  A sample is the head on a new rightmost cell in state D
(mirrored c2) or B (c1; c1's B is c2's D).  The tape left of the head is then

    0^inf [digits] (1000)^last 100

and a digit is `(1000)^r W`: a run of r blocks 1000 (block (1,3)), then a wall.  The counter walls are
Z = 10 10 10 (digit 0), O = 10 (digit 1) and T = 100000 (digit 2); any other block is a wall of its own name.
`SPEC.sweep` runs the machine SYMBOLICALLY (tools/py/bbtools/symtm.py) on a window holding the carry chain (the T
digits next to the end) and the stop digit, with long runs as variables, and caches each rule by its window shape.
The engine is the one of holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/digits.py, as used for the b
machines in holdouts/1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---/py/cdigits.py.

usage: CMACH=c2|c1 python3 cdigits.py check STEPS     compare with the direct run at every sample
"""
import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', '..', '..')
sys.path.insert(0, os.path.join(ROOT, 'tools', 'py'))
_p = os.path.join(ROOT, 'holdouts', '1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA', 'py', 'digits.py')
_spec = importlib.util.spec_from_file_location('digits_generic_1RB0LF', _p)
G = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(G)
symtm = G.symtm
show = G.show

M = {'c2': '1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD', 'c1': '1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB'}
RUN = {'c2': '1LB0RD_1LC0LF_1RA1LF_0RA0LE_1RD---_0LA0LD', 'c1': M['c1']}   # the table actually simulated
SAMPLE_STATE = {'c2': 'D', 'c1': 'B'}
SHAPES = {'Z': [(1, 1), (1, 1), (1, 1)], 'O': [(1, 1)], 'T': [(1, 5)]}


class AutoSpec(G.Spec):
    """A block 1^a 0^b that is neither a run nor part of a known wall becomes a new wall `b<a>_<b>`."""

    def parse_blocks(self, b):
        for x in b:
            if x[0] != 'R' and not any(x in bl for bl in self.shapes.values()):
                self.shapes['b%d_%d' % x] = [x]
                self.order = sorted(self.shapes.items(), key=lambda kv: -len(kv[1]))
        return G.Spec.parse_blocks(self, b)

    def sample(self, c):
        """The head in the sample state on a 0 with only 0s to its right, and `100` just left of it.  (In c2 the
        sample state also meets a 0 at the right end with `1011` to its left, which is not a new cell.)"""
        if not G.Spec.sample(self, c):
            return False
        tail = symtm.canon(c.left[-12:])[-3:]     # canon is local: the last tokens decide the last cells
        return tail == [1, 0, 0]


WHICH = os.environ.get('CMACH', 'c2')
SPEC = AutoSpec(RUN[WHICH], (1, 3), dict(SHAPES), None, SAMPLE_STATE[WHICH], 0, pairs=False, ends={'E': '100'})
CARRY = ('T',)


def direct_samples(max_steps, start=0):
    from bbtools.machine import Run
    r = Run(SPEC.m)
    while r.steps < max_steps:
        t = r.tape
        if r.state == SPEC.Q and r.head == t.hi and t.get(r.head) == 0 and r.steps > 0 and r.steps >= start:
            w = ''.join(map(str, t.word(t.lo, r.head - 1)))
            if w.endswith('100'):
                yield r.steps, 'B' + w
        if not r.step():
            raise RuntimeError('halted at step %d' % r.steps)


def parse(cells):
    a = SPEC.parse_cells(cells)
    return None if a is None else (a[0], list(a[1]), a[2], a[3])


def check(max_steps):
    st = T = None
    n = bad = unp = 0
    for step, cells in direct_samples(max_steps):
        a = parse(cells)
        if a is None:
            unp += 1
            if unp < 20:
                print('unparsed sample at', step, cells[-200:])
            st = None
            continue
        if st is not None:
            n += 1
            if st != a or T != step:
                bad += 1
                print('MISMATCH at step', step, T, show(st)[:300], 'expected', show(a)[:300])
        r = SPEC.sweep(a, carry=CARRY)
        if r[0] == 'ok':
            st, T = r[1], step + r[2]
        else:
            print('no rule at', step, r[0], show(a)[:300])
            st = T = None
    print(f'{WHICH}: {n} sweeps compared with the direct run: {bad} mismatches, {unp} unparsed samples; '
          f'{len(SPEC.memo)} window rules derived')
    return bad == 0


if __name__ == '__main__':
    if sys.argv[1] == 'check':
        sys.exit(0 if check(int(float(sys.argv[2]))) else 1)
