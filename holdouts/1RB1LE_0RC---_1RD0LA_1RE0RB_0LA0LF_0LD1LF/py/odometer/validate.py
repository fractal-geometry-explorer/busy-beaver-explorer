"""Check the macro against the direct simulator c/rtrips.c.

    python3 validate.py [STEPS]      (default 3e9; 5e10 takes about 10 minutes)

1. Every trip of l1.trip alone, from the first R-instant from blank tape, against every R line of the direct run:
   the same state, tape (as blocks and glyphs) and step count.
2. The full macro (jumps and trips) from the same start: at every visit of the left end, the configuration at the
   next R-instant and its step count, against the direct run."""
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from l1 import trip
from run import run, parse_line, START

N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 3 * 10**9
exe = os.path.join(tempfile.gettempdir(), 'rtrips_174393')
subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(HERE, '..', '..', 'c', 'rtrips.c')], check=True)
out = subprocess.run([exe, str(N)], capture_output=True, text=True).stdout.splitlines()
R = [parse_line(l) for l in out if l.startswith('R ')]
R = R[[x[0] for x in R].index(START[0]):]
assert R[0] == START, (R[0], START)
real = {st: (s, t) for st, s, t in R}
# 1. single trips
step, s, toks = START; bad = 0
for st2, s2, t2 in R[1:]:
    r = trip(s, toks)
    s, toks, step = r[0], r[1], step + r[2]
    if (s, toks, step) != (s2, t2, st2):
        bad += 1; print('trip mismatch at step', st2); s, toks, step = s2, t2, st2
print(f'1. {len(R) - 1} trips of l1.trip: {bad} mismatches')
# 2. macro at left visits
seen = [0, 0]
def log(steps, s, t, trips):
    if steps > R[-1][0]: return
    if real.get(steps) == (s, t): seen[0] += 1
    else: seen[1] += 1; print('macro mismatch at step', steps)
res = run(START[1], START[2], START[0], R[-1][0], log=log)
after = set(); pend = False
for l in out:
    if l.startswith('L '): pend = True
    elif l.startswith('R ') and pend:
        pend = False
        if int(l.split()[1]) > START[0]: after.add(int(l.split()[1]))
nleft = len(after)
print(f'2. macro: {seen[0]} left visits agree, {seen[1]} differ (direct run after step {START[0]}: {nleft} trips that visit the left end); '
      f'{res[3]} trips, {res[4]} single trips, {res[5]} jumps')
sys.exit(1 if bad or seen[1] else 0)
