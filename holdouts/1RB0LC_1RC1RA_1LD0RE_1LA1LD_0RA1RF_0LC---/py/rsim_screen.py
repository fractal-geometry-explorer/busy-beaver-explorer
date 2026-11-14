"""screen MACHINE BUDGET_SEC: validate rsim against direct simulation at a few points, then run as far as the budget allows."""
import time, json, signal
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
def at_binary():
    """compile c/at.c (plain simulator: state, head offset, tape after N steps) once into the temp folder"""
    exe = os.path.join(tempfile.gettempdir(), 'rsim_at')
    src = os.path.join(HERE, '..', 'c', 'at.c')
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        subprocess.run(['gcc', '-O2', '-o', exe, src], check=True)
    return exe
AT = at_binary()
from rsim import RSim, Halt
m = sys.argv[1]; budget = float(sys.argv[2])
sim = RSim(m); sim.KEEP = 32
t0 = time.time()
res = {'machine': m, 'checks': [], 'halt': None}
class TO(Exception): pass
def alarm(*a): raise TO()
signal.signal(signal.SIGALRM, alarm)
signal.alarm(int(budget))
try:
    for t in [10**6, 10**7, 10**8, 10**9, 3 * 10**9, 10**10]:
        sim.run(t)
        if sim.steps > 4e10: break
        s, hp = sim.tape()
        l = len(s) - len(s.lstrip('0')); l = min(l, hp); body = s[l:].rstrip('0'); hp -= l
        l2 = len(body) - len(body.lstrip('0'))
        signal.alarm(0)
        out = subprocess.run([AT, m, str(sim.steps)], capture_output=True, text=True).stdout.split()
        signal.alarm(max(1, int(budget - (time.time() - t0))))
        good = len(out) > 1 and out[0] == 'ABCDEF'[sim.s] and (out[2] if len(out) > 2 else '').strip('0') == body.strip('0') and int(out[1]) == hp - l2
        res['checks'].append((sim.steps, good))
        if not good: break
    mile = 10**11
    while True:
        sim.run(mile); mile *= 10
        res['reached'] = sim.steps; res['sec'] = round(time.time() - t0, 1)
except Halt:
    res['halt'] = sim.steps
except TO:
    pass
except Exception as e:
    res['error'] = repr(e)[:200]
signal.alarm(0)
res['reached'] = sim.steps; res['sec'] = round(time.time() - t0, 1); res['jumps'] = sim.njumps; res['samples'] = sim.nsamp; res['skipped'] = sim.jumped
res['items'] = len(sim.L) + len(sim.R)
print(json.dumps(res))
