"""The digit model of 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA--- (b1) and of its twin 1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---
(b2), at the left end (16 November 2026): an exact simulator from one sample to the next.

Between the right-end events of lawev.py the head bounces at the LEFT end of the tape, and each bounce sends a carry
rightwards through a ternary counter.  A sample is the head, in state A, on a new leftmost cell.  The tape is read
MIRRORED (the machine 1LB0RB_1LC0RA_1RB0LD_1LE1LD_1LB1LF_1RA---, or its twin), so that the generic window engine of
holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/digits.py (class Spec) applies: mirrored, a sample is
0^inf [digits] [last run] 1 0 A> 0^inf (or with no `1 0`).  Digits are `(1000)^r W`: a run of r gaps 3, then a
wall W of other gaps, written as blocks 1^a 0^b.  The walls of the counter are Z = 1/5 (digit 0), O = 1/1 1/1
(digit 1) and T = 3/3 (digit 2); any other block is a wall of its own name (AutoSpec).  `sweep` runs the machine
SYMBOLICALLY (tools/py/bbtools/symtm.py) on a window holding the carry chain and the stop digit, more if needed,
long runs as variables, and caches each rule by its window shape.  Every number is a machine run, not a model guess.

usage: python3 cdigits.py check STEPS [B]     compare with the direct run (mirror machine) at every sample
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
Blank = G.Blank

M = {'b1': '1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---', 'b2': '1RB0LC_1LA0RD_1RA0LA_1RE1RD_1RA1RF_1LC---'}
MIRROR = {'b1': '1LB0RB_1LC0RA_1RB0LD_1LE1LD_1LB1LF_1RA---', 'b2': '1LB0RC_1RA0LD_1LA0RA_1LE1LD_1LA1LF_1RC---'}
SAMPLE_STATE = {'b1': 'A', 'b2': 'C'}       # b2's C is b1's A (b2 = b1 relabelled A->C, B->A, C->B)
SHAPES = {'T': [(3, 3)], 'O': [(1, 1), (1, 1)], 'Z': [(1, 5)], 'b1_1': [(1, 1)]}


class AutoSpec(G.Spec):
    """Spec with one addition: a block 1^a 0^b that is neither a run nor part of a known wall becomes a new wall
    `b<a>_<b>` (a name only; every rule is still a symbolic run of the machine)."""

    def parse_blocks(self, b):
        for x in b:
            if x[0] != 'R' and not any(x in bl for bl in self.shapes.values()):
                self.shapes['b%d_%d' % x] = [x]
                self.order = sorted(self.shapes.items(), key=lambda kv: -len(kv[1]))
        return G.Spec.parse_blocks(self, b)


WHICH = os.environ.get('BMACH', 'b1')
SPEC = AutoSpec(MIRROR[WHICH], (1, 3), dict(SHAPES), None, SAMPLE_STATE[WHICH], 0, pairs=False,
                ends={'E': '10', 'E0': ''})
CARRY = ('T',)


def direct_samples(max_steps, start=0):
    """Direct run of the mirror machine from blank tape: (step, cells 'B...') at each sample point."""
    from bbtools.machine import Run
    r = Run(SPEC.m)
    while r.steps < max_steps:
        t = r.tape
        if r.state == SPEC.Q and r.head == t.hi and t.get(r.head) == 0 and r.steps > 0 and r.steps >= start:
            yield r.steps, 'B' + ''.join(map(str, t.word(t.lo, r.head - 1)))
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
    print(f'{n} sweeps compared with the direct run: {bad} mismatches, {unp} unparsed samples; '
          f'{len(SPEC.memo)} window rules derived')
    return bad == 0


if __name__ == '__main__':
    sys.path.insert(0, os.path.join(ROOT, 'tools', 'py'))
    if sys.argv[1] == 'check':
        sys.exit(0 if check(int(float(sys.argv[2]))) else 1)
