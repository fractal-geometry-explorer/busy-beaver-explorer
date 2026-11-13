"""A long exact run of 1RB---_1RC1RF_1LD1RA_1LB0LE_1LF1LF_0RB0LD with the macro simulator (tools/py/bbtools/macro.py,
blocks of 3 cells, whole runs of the background crossed at once; exact step counts and tape).

usage: python3 far.py [STEPS]     (default 1e14: about 1 minute; 1e15: 3 minutes; 3.2e15: 8 minutes)

Prints, at every half decade of steps, whether the machine has halted, the number of macro steps and the tape as
runs of 3-cell words around the head (state and direction).  The last runs before the end of the tape show the
block before END, which loses one period at every overflow of the counter.
"""
import os, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../tools/py'))
from bbtools.macro import MacroRun

M = '1RB---_1RC1RF_1LD1RA_1LB0LE_1LF1LF_0RB0LD'

if __name__ == '__main__':
    lim = float(sys.argv[1]) if len(sys.argv) > 1 else 1e14
    r = MacroRun(M, 3)
    t0 = time.time()
    s = 1e10
    while s <= lim * 1.0001:
        r.run(s)
        print(f'{s:.1e}: steps {r.steps:,}  macro steps {r.msteps:,}  halted {r.halted}  ({time.time() - t0:.0f} s)')
        print('    ' + str(r))
        if r.halted:
            print('HALT at step', r.steps)
            break
        s *= 10 ** 0.5
