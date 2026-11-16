"""The digit model of 1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD (16 November 2026): an exact simulator at the
sample points of lean/Counter.lean (`cfg`: 0^inf 1 1 1 C> 0 0 1 [0^g 1]... 0^inf, one sample per bounce).

The tape is read MIRRORED, so that the generic window engine of
holdouts/1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA/py/digits.py (class Spec) applies: we run the mirror machine
1LB0LF_1RC1LF_1LA0RD_0RC0LE_1RD---_0LC0LD.  Mirrored, a sample is  0^inf [1 0^gk] ... [1 0^g1] 1 0 C> 0 1 1 1 0^inf:
digits `(1000)^r W` (a run of r gaps 3, then a wall W of other gaps), the last run, then the end cells `10`; the
head reads 0 with `1 1 1` and blank tape to its right (Spec.sample and Spec.head_right are changed for that).
Walls are lists of blocks 1^a 0^b (a gap g is the block 1/g; a gap 0 joins two 1s): T2 = 1/1 1/1 1/1 (the
separator 1 1 1, ternary digit 2), T1 = 1/1 (separator 1, digit 1), T0 = 1/5 (separator 5, digit 0, the borrow
passes it), and any other block becomes a wall of its own name (AutoSpec).  `sweep` runs the machine SYMBOLICALLY
(tools/py/bbtools/symtm.py) on a window holding the borrow chain and the stop digit, more if needed, long runs as
variables, and caches each rule by its window shape.  Every number is a machine run, not a model guess.

usage: python3 digits.py check DUMP     compare with c/gapdump output (every sample)
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

M = '1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD'
MIRROR = '1LB0LF_1RC1LF_1LA0RD_0RC0LE_1RD---_0LC0LD'
SHAPES = {'T2': [(1, 1), (1, 1), (1, 1)], 'T1': [(1, 1)], 'T0': [(1, 5)]}
RIGHT = [0, 1, 1, 1, Blank()]


class AutoSpec(G.Spec):
    """Spec with the sample of this machine, and one addition: a block 1^a 0^b that is neither a run nor part of a
    known wall becomes a new wall `b<a>_<b>` (a name only; every rule is still a symbolic run of the machine)."""

    def parse_blocks(self, b):
        for x in b:
            if x[0] != 'R' and not any(x in bl for bl in self.shapes.values()):
                self.shapes['b%d_%d' % x] = [x]
                self.order = sorted(self.shapes.items(), key=lambda kv: -len(kv[1]))
        return G.Spec.parse_blocks(self, b)

    def sample(self, c):
        if c.steps.is_zero() or c.state != self.Q:
            return False
        return symtm.canon(c.right) == RIGHT

    def head_right(self):
        return list(RIGHT)


SPEC = AutoSpec(MIRROR, (1, 3), SHAPES, None, 'C', 0, pairs=False, ends={'E': '10'})
CARRY = ('T0',)


def samples(path):
    """(step, mirrored cells) for each line 'STEP Z| g^k ... |T' of c/gapdump."""
    for line in open(path):
        if 'HALT' in line:
            print('direct run HALTS:', line.strip())
            continue
        a, rest = line.split(' ', 1)
        z, mid, t = rest.split('|')
        gaps = []
        for tok in mid.split():
            g, k = tok.split('^')
            gaps += [int(g)] * int(k)
        cells = ['B', '0' * int(t)] + ['1' + '0' * g for g in reversed(gaps)] + ['1' + '0' * (int(z) - 1)]
        yield int(a), ''.join(cells)


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
    if sys.argv[1] == 'check':
        sys.exit(0 if check(sys.argv[2]) else 1)
