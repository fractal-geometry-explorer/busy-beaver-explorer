"""longrun MACHINE BUDGET_SEC OUT.jsonl: run rsim; after each decade of steps record digits of steps, time, and the tape near the head."""
import sys, time, json, signal
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rsim import RSim, Halt
m = sys.argv[1]; budget = int(sys.argv[2]); out = open(sys.argv[3], 'w')
sim = RSim(m); sim.KEEP = 32
t0 = time.time()
class TO(Exception): pass
def alarm(*a): raise TO()
signal.signal(signal.SIGALRM, alarm); signal.alarm(budget)
def snap(tag):
    L = [(w, c) for w, c in sim.L[-60:]]; R = [(w, c) for w, c in sim.R[-20:]]
    out.write(json.dumps({'tag': tag, 'digits': len(str(sim.steps)), 'steps': str(sim.steps) if sim.steps < 10**60 else None, 'sec': round(time.time() - t0, 1),
        'state': 'ABCDEF'[sim.s], 'jumps': sim.njumps, 'samples': sim.nsamp, 'nL': len(sim.L), 'nR': len(sim.R), 'L': L, 'buf': ''.join(map(str, sim.buf)), 'head': sim.h, 'R': R}) + '\n'); out.flush()
try:
    e = 6
    while True:
        sim.run(10**e); snap('decade'); e = max(e + 1, len(str(sim.steps)))
except Halt:
    snap('HALT'); print('HALT', len(str(sim.steps)), sim.steps)
except TO:
    snap('timeout'); print('timeout at digits', len(str(sim.steps)))
