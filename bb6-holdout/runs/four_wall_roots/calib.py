"""How many of the run's own loop entries (W > 2^41, from the sample) are values of an entry class of the tree:
calibrates match_forms.py.  usage: calib.py forms.txt entries_all.txt [limit]"""
import sys, collections
from match_forms import parse
ev = lambda f, x: f[0] + sum(c * xi for c, xi in zip(f[1:], x))
cls = parse(sys.argv[1]); lim = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
idx = collections.defaultdict(list)
for D, fs, ts in cls: idx[fs[3][1]].append((D, fs, ts))   # by W's coefficient of the first variable
tot = hit = 0; byround = collections.Counter(); hround = collections.Counter()
for l in open(sys.argv[2]):
    n, rd, b, W, R = map(int, l.split())
    if W <= 2 ** 41: continue
    tot += 1; byround[rd] += 1; c = W - R - 1
    found = False
    for D, (fa, fb, fc, fW), ts in cls:
        if fW[2] or fb[2] or fc[2] or fW[1] == 0 or (W - fW[0]) % fW[1]: continue
        x = [(W - fW[0]) // fW[1], 0]
        if ev(fb, x) == b and ev(fc, x) == c and all(ev(t, x) >= 0 for t in ts): found = True; break
    if found: hit += 1; hround[rd] += 1
    if tot >= lim: break
print('entries', tot, 'matched', hit)
for rd, v in byround.most_common(12): print('  round', rd, v, 'matched', hround[rd])
