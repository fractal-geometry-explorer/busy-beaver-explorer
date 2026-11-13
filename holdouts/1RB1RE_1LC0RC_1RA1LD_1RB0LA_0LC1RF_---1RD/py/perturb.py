"""Counter tapes that halt: the shape of the tape alone does not prevent a halt.

At the left end the run from blank tape shows `D> 0 b (ba)^n1 s1 (ba)^n2 s2 ... (ba)^nk sk 1^4` (a = 10, b = 1110,
separators a, b, ab, bb = digits 0..3).  This script starts the machine from tapes of exactly that form with short
blocks and simulates them plainly.  Many halt, e.g.

    D> 0 b (ba)^3 a (ba)^3 a 1^4      halts at step 81,375     (lean/Perturbed.lean, native_decide)
    D> 0 b (ba)^7 a (ba)^4 a 1^4      halts at step 227,426

so a nonhalting proof has to use the block lengths the actual run produces.

usage: python3 perturb.py B STEPS     every tape with at most 2 inner separators, blocks 1..B, end separator a or b,
                                      run STEPS steps (e.g. 4 300000); prints the halting ones
"""
import itertools
import sys

M = "1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD"
SEP = {'a': '10', 'b': '1110', 'ab': '101110', 'bb': '11101110'}


def table(m):
    t = {}
    for i, g in enumerate(m.split('_')):
        for b in (0, 1):
            s = g[3 * b:3 * b + 3]
            t[(i, b)] = None if s[2] == '-' else (int(s[0]), 1 if s[1] == 'R' else -1, ord(s[2]) - 65)
    return t


T = table(M)


def halts(tape, state, maxsteps):
    """The bbchallenge step count of the halt (head on the first cell of `tape`), or None."""
    c = {i: int(x) for i, x in enumerate(tape)}
    h = 0
    for k in range(maxsteps):
        tr = T[(state, c.get(h, 0))]
        if tr is None:
            return k + 1
        c[h], mv, state = tr
        h += mv
    return None


def tape(blocks, seps, end):
    s = '0' + '1110' + '111010' * blocks[0]
    for sp, n in zip(seps, blocks[1:]):
        s += SEP[sp] + '111010' * n
    return s + SEP[end] + '1111'


def main():
    B, steps = int(sys.argv[1]), int(sys.argv[2])
    found = 0
    for k in range(3):
        for blocks in itertools.product(range(1, B + 1), repeat=k + 1):
            for seps in itertools.product(list(SEP), repeat=k):
                for end in ('a', 'b'):
                    h = halts(tape(blocks, seps, end), 3, steps)
                    if h is not None:
                        found += 1
                        print('halts at step %d: blocks %s separators %s end %s' % (h, blocks, seps, end), flush=True)
    print('%d halting tapes' % found)


if __name__ == '__main__':
    main()
