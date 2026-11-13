"""bell_farrun.py M STEPS [out.json [MAXSECONDS]]: run wsim far, log progress, epochs (head at the right end of the tape) and contexts of
the state that precedes the halting transition."""
import sys, json, time, re
import os, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
_sp = importlib.util.spec_from_file_location("bell_wsim", os.path.join(HERE, "bell_wsim.py"))
wsim = importlib.util.module_from_spec(_sp); _sp.loader.exec_module(wsim)

M = sys.argv[1]; N = float(sys.argv[2]); out = sys.argv[3] if len(sys.argv) > 3 else None
MAXT = float(sys.argv[4]) if len(sys.argv) > 4 else 1e18   # stop after this many seconds
s = wsim.WSim(M)
def onesruns(w):
    return [len(x) for x in re.findall('1+', w)]
def describe():
    """R-form description of the tape left of the head: items as run lengths of 1s with multiplicity"""
    parts = []
    for w, n in s.L:
        r = onesruns(w)
        if not r: continue
        if n == 1:
            parts += [str(x) for x in r]
        else:
            if len(r) == 1:
                parts.append('%dx%d' % (r[0], n) if set(w) != {'1'} else '%d' % (len(w) * n))
            else:
                parts.append('[%s]x%d' % (' '.join(map(str, r)), n))
    return ' '.join(parts)
epochs = []
last_epoch_samples = -10 ** 9
nsamp = [0]
orig = s.sample
def samp():
    nsamp[0] += 1
    return orig()
s.sample = samp
t0 = time.time(); nxt = 1e6
res = 'ok'
try:
    while s.steps < N and time.time() - t0 < MAXT:
        pf = s.f
        s.macro()
        if pf == -1 and s.f == 1:
            s.sample()
        if not s.R and s.f == 1 and nsamp[0] - last_epoch_samples > 50:
            last_epoch_samples = nsamp[0]
            epochs.append((s.steps, describe()))
        if s.steps >= nxt:
            print('%.3e steps  %.0fs  jumps %d  items %d  epochs %d' % (s.steps, time.time() - t0, s.jumps, len(s.L) + len(s.R), len(epochs)), flush=True)
            while nxt <= s.steps: nxt *= 10
except wsim.Halt:
    res = 'HALT'
print(res, 'at %d steps' % s.steps if res == 'HALT' else '', '%.3e' % s.steps, 'time %.0fs' % (time.time() - t0))
if out:
    json.dump({'machine': M, 'result': res, 'steps': s.steps, 'jumps': s.jumps, 'epochs': [[str(a), b] for a, b in epochs]}, open(out, 'w'), indent=0)
