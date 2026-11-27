#!/usr/bin/env python3
"""Run contractsat on a list of (machine, direction) pairs.
usage: screen.py LIST n W shard nshards out.tsv [tlimit]
LIST: tsv whose first two columns are machine and rightward|leftward (direction of the trips; the window is at
the other end).  Appends one line per pair: machine, direction, n, W, result, rounds, window configs, seconds."""
import sys, time, json, os
import contractsat as cs, check
lst, n, W, sh, nsh, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
tl = float(sys.argv[7]) if len(sys.argv) > 7 else 100
pairs = []
for l in open(lst):
    f = l.split()
    if len(f) >= 2 and f[1] in ('rightward', 'leftward'):
        pairs.append((f[0], f[1]))
done = set()
if os.path.exists(out):
    for l in open(out):
        f = l.split('\t')
        done.add((f[0], f[1]))
with open(out, 'a') as fo:
    for i, (m, d) in enumerate(pairs):
        if i % nsh != sh or (m, d) in done:
            continue
        t0 = time.time()
        e = cs.Enc(m, d == 'leftward', n, W, sym=True, verbose=False)
        c = e.solve(tlimit=tl)
        if isinstance(c, dict):
            check.check(json.loads(json.dumps(c)))
            json.dump(c, open(out + '.%s.%s.json' % (m, d), 'w'))
            r = 'CERT'
        else:
            r = 'NONE' if c is None else 'TIMEOUT'
        fo.write('\t'.join(map(str, [m, d, n, W, r, len(e.expanded), '%.1f' % (time.time() - t0)])) + '\n')
        fo.flush()
