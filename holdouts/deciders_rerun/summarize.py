"""Writes results.json from the raw sweep outputs (kept outside the repo):
python3 summarize.py RAWDIR  (RAWDIR holds bkr.out, tc.out, rw.out, ng.jsonl.gz)."""
import json, sys, gzip, os
raw = sys.argv[1]
here = os.path.dirname(os.path.abspath(__file__))
fam = json.load(open(os.path.join(here, '..', 'families.json')))
ms = [x['m'] for f in fam['residual'] for x in f['machines']]
old = {x['m']: f['id'] for f in fam['residual'] for x in f['machines']}
R = {m: {'machine': m, 'old': old[m]} for m in ms}
for l in open(os.path.join(raw, 'bkr.out')):
    m, *r = l.split()
    R[m]['backward'] = 'chain of length 3000 exists' if r[0] == 'FAIL' else 'frontier grows exponentially (no depth bound found)'
for l in open(os.path.join(raw, 'tc.out')):
    m, r, n = l.split()
    R[m]['cycler'] = 'none to %d steps' % int(n) if r == 'NONE' else r
for l in open(os.path.join(raw, 'rw.out')):
    m, r, *cells = l.split()
    assert r == 'none'
    unk = [c.split(':')[0] for c in cells if c.endswith('UNKNOWN')]
    R[m]['repwl'] = {'decided': False, 'runs': len(cells), 'halt_reached': len(unk),
                     'budget': len(cells) - len(unk),
                     'max_len_halt_reached': max([int(c.split(',')[0]) for c in unk], default=0)}
for l in gzip.open(os.path.join(raw, 'ng.jsonl.gz'), 'rt'):
    d = json.loads(l); out = {}
    assert not d['decided']
    for name, runs in d['log']:
        w = [r[0] for r in runs if r[1] == 'UNKNOWN']
        lim = [r[0] for r in runs if r[1] != 'UNKNOWN']
        out[name] = {'halt_reached_up_to': w[-1] if w else None, 'stopped_at': lim[0] if lim else None}
    R[d['m']]['ngramcps'] = out
res = {'asof': '21 November 2026', 'machines': len(ms), 'decided': 0,
       'note': 'No machine was decided. "halt_reached" runs are real failures of the decider at those parameters '
               '(its abstraction reaches a halting configuration); "budget" runs stopped at the configuration or time limit.',
       'results': [R[m] for m in ms]}
rows = res.pop('results')
with open(os.path.join(here, 'results.json'), 'w') as f:
    f.write(json.dumps(res)[:-1] + ', "results": [\n')
    f.write(',\n'.join(json.dumps(r, separators=(',', ':')) for r in rows) + '\n]}\n')
print(len(ms))
