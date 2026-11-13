"""Run 1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA from blank tape with the accelerated simulator and print the tape
at every visit of the left end (state E, head on the blank cell left of the tape), one line per round.

Words: b = 0111, c = 011, a = 01.  The accelerator (genacc.Acc) re-tokenises the tape at every visit of either end
and, when three visits of the same shape have counts in arithmetic progression and steps with constant second
difference, applies the cycle as many times as the decreasing counts allow (keeping them >= 3).  In this machine
the cycles it applies are the drain trips of lean/Rules.lean (one b converted per trip).

usage: python3 run.py 1e400 > rounds.txt      (about 10 minutes for 1e400)
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from genacc import Acc

M = '1RB1RE_1LC1RE_---1LD_1LE0LB_0RF0LD_1RD1RA'
NAMES = {'0111': 'b', '011': 'c', '01': 'a'}


def show(tok):
    return ' '.join((NAMES.get(w, w) if n == 1 else f'{NAMES.get(w, w)}^{n}') for w, n in tok)


def main():
    arg = sys.argv[1] if len(sys.argv) > 1 else '1e100'
    maxsteps = 10 ** int(arg.split('e')[1]) if 'e' in arg else int(arg)
    A = Acc(M, ['0111', '011', '01'])

    def on(a, key, j):
        if key[1] == 'L':
            print(a.s.steps, 'ABCDEF'[a.s.q], show(a.s.tok), flush=True)
    t0 = time.time()
    r = A.run(maxsteps, on)
    print(r, A.s.steps, A.jumps, A.jumped_cycles, round(time.time() - t0, 1))


if __name__ == '__main__':
    main()
