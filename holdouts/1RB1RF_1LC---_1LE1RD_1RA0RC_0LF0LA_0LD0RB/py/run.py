"""Run 1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB from blank tape with the turn-sampled accelerator and print every
epoch start: the head in state A, moving right, on `1 A>0 0 1^N` (the tape is one block of N ones).

usage: python3 run.py 1e300 > epochs.txt        (prints: steps N, then a summary line)
       python3 run.py check 3e8                   (accelerated samples against the plain run-length simulator)
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from turnacc import TurnAcc, check

M = '1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB'
WORDS = ['1', '01', '10']


def is_epoch(s):
    body = [t for t in s.tok if t[0] != '0']
    return s.q == 0 and s.dir == 1 and len(body) == 2 and all(set(w) == {'1'} for w, n in body)


def main():
    if sys.argv[1] == 'check':
        check(M, WORDS, int(float(sys.argv[2])))
        return
    e = sys.argv[1]
    maxsteps = 10 ** int(e.split('e')[1]) if 'e' in e else int(e)
    A = TurnAcc(M, WORDS)
    t0 = time.time()

    def on(a, j):
        if is_epoch(a.s):
            N = sum(n for w, n in a.s.tok if w == '1') - 1
            print(a.s.steps, N, flush=True)
    r = A.run(maxsteps, on)
    print(r, 'steps', len(str(A.s.steps)), 'digits, jumps', A.jumps, round(time.time() - t0), 's')


if __name__ == '__main__':
    main()
