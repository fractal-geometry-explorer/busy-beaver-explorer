"""n-gram CPS sweep: python3 ngsweep.py MACHINES.txt OUT.jsonl. For each machine and each mode, widths are raised
until the decider succeeds (NONHALT) or runs out of budget (LIMIT at 8,000,000 configurations, or 40 s)."""
import subprocess, sys, json, os
from multiprocessing import Pool
NG = os.environ.get('NGRAMCPS', './ngramcps')  # gcc -O2 -I tools/c -o ngramcps tools/c/ngramcps.c
def run(m, args, t):
    try:
        out = subprocess.run([NG, m] + args + ['-m', '8000000'], capture_output=True, text=True, timeout=t).stdout
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', None
    kv = dict(l.split(' ', 1) for l in out.splitlines() if ' ' in l)
    return kv.get('result', 'ERR'), kv
def series(m, mk, ws, t):
    res = []
    for w in ws:
        a = mk(w); r, kv = run(m, a, t)
        res.append((' '.join(a), r, kv and kv.get('configs')))
        if r == 'NONHALT': return res, True
        if r in ('TIMEOUT', 'LIMIT', 'ERR'): break
    return res, False
def one(m):
    log = []; won = None
    plans = [('plain', lambda w: [str(w)], range(1, 31)),
             ('H1', lambda w: [str(w), '-H', '1'], range(1, 21)),
             ('H2', lambda w: [str(w), '-H', '2'], range(1, 16)),
             ('H3', lambda w: [str(w), '-H', '3'], range(1, 12)),
             ('LRU', lambda w: [str(w), '-U'], range(1, 12))]
    for nl in range(1, 13):
        plans.append((f'asymL{nl}', (lambda nl: lambda w: [str(nl), str(w)])(nl), [w for w in range(1, 17) if w != nl]))
    for name, mk, ws, in plans:
        r, ok = series(m, mk, ws, 40)
        log.append((name, r))
        if ok: won = r[-1][0]; break
    return m, won, log
if __name__ == '__main__':
    ms = [l.strip() for l in open(sys.argv[1]) if l.strip()]
    with Pool(4) as p, open(sys.argv[2], 'a') as f:
        for m, won, log in p.imap_unordered(one, ms):
            f.write(json.dumps({'m': m, 'decided': won, 'log': log}) + '\n'); f.flush()
            print(m, won, flush=True)
