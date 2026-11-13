"""Check accel.py against plain simulation (c/tapeat.c): after each jump (and every 997th event) the flattened tape at the
next event is compared with the C program tapeat (direct simulation).
usage: gcc -O2 -o /tmp/tapeat holdouts/1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---/c/tapeat.c && python3 holdouts/1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---/py/check_accel.py MACHINE MAXSTEPS /tmp/tapeat"""
import subprocess
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import accel  # noqa: E402

M, mx, bin_ = sys.argv[1], int(float(sys.argv[2])), sys.argv[3]
S = accel.Sim(M)
out = []
last = [0]


def ev(s):
    if s.jumps != last[0] or s.nevents % 997 == 0:
        last[0] = s.jumps
        out.append((s.c.steps,) + accel.flatten(s.c))


S.run(mx, ev)
p = subprocess.run([bin_, M], input='\n'.join(str(o[0]) for o in out), capture_output=True, text=True)
bad = 0
for o, line in zip(out, p.stdout.split('\n')):
    k, st, h, t = line.split()
    if (int(k), st, int(h), t) != o:
        bad += 1
        print("MISMATCH at", o[0], o[1:3], line.split()[:3], len(o[3]), len(t), o[3]==t)
print('checked', len(out), 'snapshots up to step', out[-1][0], 'jumps', S.jumps, 'mismatches', bad)
