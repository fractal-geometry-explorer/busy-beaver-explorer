"""Long exact run of the macro from blank tape, resumable.

    python3 far.py SECONDS [DIR]     (DIR default: ../../data/odometer)

Writes DIR/visits.jsonl (one line per visit of the left end: [step, state, number of walls, the configuration at the
next R-instant with every block over 10^6 words given as its length's number of decimal digits]), DIR/state.json
(the exact configuration reached, to resume from) and DIR/summary.json."""
import gzip, json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from run import run, START

T = float(sys.argv[1])
D = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, '..', '..', 'data', 'odometer')
os.makedirs(D, exist_ok=True)
SP = os.path.join(D, 'state.json')
if os.path.exists(SP):
    st = json.load(open(SP)); step, s, toks, visits = int(st['step']), st['state'], st['toks'], st['visits']
    VP = os.path.join(D, 'visits.jsonl')  # drop visits logged after the saved state (an interrupted chunk)
    if os.path.exists(VP):
        keep = [l for l in open(VP) if int(json.loads(l)[0]) <= step]
        open(VP, 'w').writelines(keep)
        assert len(keep) == visits, (len(keep), visits)
else:
    step, s, toks = START; visits = 0
out = open(os.path.join(D, 'visits.jsonl'), 'a')


def short(t):
    return [x if isinstance(x, str) or x < 10**6 else 'e%d' % (len(str(x)) - 1) for x in t]


def log(steps, s, t, trips):
    global visits
    visits += 1
    out.write(json.dumps([str(steps), s, (len(t) - 3) // 2, short(t)]) + '\n')


t0 = time.time()
while time.time() - t0 < T:
    r = run(s, toks, step, 10**10**6, maxtime=min(60, T - (time.time() - t0)), log=log)
    if r[0] == 'HALT':
        json.dump({'halt': str(r[1])}, open(os.path.join(D, 'HALT.json'), 'w')); print('HALT', r[1]); break
    s, toks, step = r[0], r[1], r[2]
    out.flush()
    json.dump({'step': str(step), 'state': s, 'toks': toks, 'visits': visits}, open(SP, 'w'))
json.dump({'step': str(step), 'digits': len(str(step)), 'visits': visits, 'walls': (len(toks) - 3) // 2},
          open(os.path.join(D, 'summary.json'), 'w'))
print('step 10^%d' % (len(str(step)) - 1), 'visits', visits)
