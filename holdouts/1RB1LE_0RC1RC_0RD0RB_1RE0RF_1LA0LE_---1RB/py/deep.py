"""Deep exact run of this machine with the shared macro simulator (c/msim.c of the folder
1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---), and its check against the direct simulator.

    python3 deep.py run [SECONDS]     blocks of 6 cells from blank tape; prints the last line (END ... or HALT ...)
    python3 deep.py verify [STEPS]    macro against tools/c/tmrun.c after STEPS steps (default 2e9): state, head, tape
"""
import importlib.util
import os
import subprocess
import sys

M = "1RB1LE_0RC1RC_0RD0RB_1RE0RF_1LA0LE_---1RB"
K = 6
HERE = os.path.dirname(os.path.abspath(__file__))
F06 = os.path.join(HERE, '..', '..', '1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA---')
spec = importlib.util.spec_from_file_location("f06deep", os.path.join(F06, 'py', 'deep.py'))
d = importlib.util.module_from_spec(spec)
spec.loader.exec_module(d)

if __name__ == '__main__':
    msim = d.build(os.path.join(F06, 'c', 'msim.c'), 'msim')
    if sys.argv[1] == 'run':
        secs = sys.argv[2] if len(sys.argv) > 2 else '240'
        out = subprocess.run([msim, M, str(K), '1e36', '-', '0', 'r', secs], capture_output=True, text=True).stdout
        line = out.strip().split('\n')[-1]
        print(line[:200])
        p = line.split()
        if p[0] == 'END' and p[1] != 'cap':
            print("no halt in the first %s steps (%.3e)" % (p[2], float(p[2])))
    else:
        steps = sys.argv[2] if len(sys.argv) > 2 else '2e9'
        tmrun = d.build(os.path.join(d.ROOT, 'tools', 'c', 'tmrun.c'), 'tmrun')
        n = d.verify_one(msim, tmrun, M, K, steps)
        print("macro and direct agree after %d steps" % n if n and n > 0 else "DIFFER or no comparison: %s" % n)
