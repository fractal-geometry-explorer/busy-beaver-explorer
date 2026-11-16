"""goodrun.py STEPS [START]: the condition of lean/Lockstep.lean, on the exact run-length simulator rsim.py.

The table of 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC--- started in state START (default 3 = D, the run of
1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE--- mirrored; 0 = A, this machine): the head never reads a 1 in state A or B
with only 0s to its left.  Prints every configuration that breaks it (BAD), then a summary.  1e14 steps: about 7
minutes per run.
"""
import os
import sys
import time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rsim import Sim
N = float(sys.argv[1]); q0 = int(sys.argv[2]) if len(sys.argv) > 2 else 3
s = Sim(); s.st = q0; bad = 0; near = 0; t0 = time.time()
while s.steps < N:
    if s.st <= 1 and s.h == 1:
        L = s.L
        if all(r[0] == 0 and r[1] == 1 for r in L):
            bad += 1
            print('BAD', s.steps, s.st, flush=True)
    if not s.step():
        print('HALT', s.steps); break
print('start', 'ABCDEF'[q0], 'steps', s.steps, 'bad', bad, 'cells', s.hi - s.lo + 1, '%.0f s' % (time.time() - t0))
