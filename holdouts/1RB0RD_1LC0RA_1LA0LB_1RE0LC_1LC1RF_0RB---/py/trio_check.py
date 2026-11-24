"""trio_check MACHINE [TARGETS]: run trio.py and compare its tape, state and head with a plain C simulator
(holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/c/at.c) at the step counts reached at or after each target.

    python3 trio_check.py 1RB0RD_1LC0RA_1LA0LB_1RE0LC_1RA1RF_0RB--- 1e6,1e7,1e8,1e9,3e9,1e10     # about 2 minutes
"""
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from trio import Sim  # noqa: E402

AT_SRC = os.path.join(HERE, '..', '..', '1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---', 'c', 'at.c')


def at_binary():
    exe = os.path.join(tempfile.gettempdir(), 'trio_at')
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(AT_SRC):
        subprocess.run(['gcc', '-O2', '-o', exe, AT_SRC], check=True)
    return exe


def main():
    m = sys.argv[1]
    targets = [int(float(x)) for x in (sys.argv[2] if len(sys.argv) > 2 else '1e6,1e7,1e8,1e9').split(',')]
    at = at_binary()
    sim = Sim(m)
    res = []
    for t in targets:
        sim.run(t)
        st, hp, s = sim.norm()
        out = subprocess.run([at, m, str(sim.steps)], capture_output=True, text=True).stdout.split()
        ok = len(out) == 3 and out[0] == st and int(out[1]) == hp and out[2].rstrip('0') == s.rstrip('0')
        res.append({'steps': sim.steps, 'equal': ok, 'jumps': sim.njumps})
        print(json.dumps(res[-1]), flush=True)
        if not ok:
            break
    print(json.dumps({'machine': m, 'checks': res}))
    sys.exit(0 if all(r['equal'] for r in res) else 1)


if __name__ == '__main__':
    main()
