#!/usr/bin/env python3
"""Return-shape analysis as a decider over many machines: both orientations, a few settings each."""
import sys, os, subprocess, signal, time, collections, multiprocessing as mp, shutil
from sba import *

CONFIGS = [(1, 2, 2), (1, 2, 0), (2, 2, 1), (1, 1, 1)]   # (L, J, j)
TMO = int(os.environ.get('TMO', '8'))

def sample(tm, mir, steps='1e7', n=3000):
    out = subprocess.run(['./sampler', tm, str(mir), steps, str(n), '0'], capture_output=True, text=True).stdout
    sm = collections.defaultdict(list)
    for ln in out.split('\n'):
        if not ln or ln.startswith('HALT'): continue
        a, b = ln.split(':'); toks = tuple(int(x) for x in b.split())
        if not toks: continue
        _, st, gap = a.split()
        sm[(ord(st) - 65, int(gap), toks[0])].append(toks)
    return sm

class TO(Exception): pass
def onalarm(*a): raise TO()

def job(tm):
    res = []
    signal.signal(signal.SIGALRM, onalarm)
    for mir in (0, 1):
        sm = sample(tm, mir)
        if not sm: res.append((tm, mir, 'no end turns')); continue
        typ = max(sm, key=lambda t: len(sm[t])); lists = sm[typ]
        if len(lists) < 60: res.append((tm, mir, 'few end turns %d' % len(lists))); continue
        seed = lists[min(100, len(lists) // 2)]
        if len(seed) > 400: res.append((tm, mir, 'seed too long %d' % len(seed))); continue
        T = parse_tm(tm, bool(mir))
        for (L, J, j) in CONFIGS:
            signal.alarm(TMO)
            try:
                A, status = attempt(T, typ, seed, L, J, j, maxnt=30000, fuel=100000, maxword=2000, maxshapes=4000)
                signal.alarm(0)
                res.append((tm, mir, '%s,%d,%d' % (chr(65 + typ[0]), typ[1], typ[2]), len(seed), 'L%d J%d j%d' % (L, J, j), status,
                            '%.1fs' % A.time, len(A.prods), len(A.C)))
            except TO:
                res.append((tm, mir, 'L%d J%d j%d' % (L, J, j), 'TIMEOUT'))
            except BaseException as e:
                signal.alarm(0)
                res.append((tm, mir, 'L%d J%d j%d' % (L, J, j), 'EXC ' + type(e).__name__))
    return res

if __name__ == '__main__':
    machines = [l.split()[0] for l in open(sys.argv[1]) if l.strip()]
    out = sys.argv[2]; pub = sys.argv[3] if len(sys.argv) > 3 else None
    done = set()
    if os.path.exists(out):
        for l in open(out): done.add(l.split()[0])
    machines = [m for m in machines if m not in done]
    last = time.time()
    with mp.Pool(4, maxtasksperchild=4) as p, open(out, 'a') as f:
        for res in p.imap_unordered(job, machines):
            for r in res: f.write(' '.join(map(str, r)) + '\n')
            f.flush()
            if pub and time.time() - last > 300:
                shutil.copy(out, pub + '.tmp'); os.replace(pub + '.tmp', pub); last = time.time()
    if pub: shutil.copy(out, pub + '.tmp'); os.replace(pub + '.tmp', pub)
