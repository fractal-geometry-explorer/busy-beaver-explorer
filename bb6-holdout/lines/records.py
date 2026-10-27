"""Smallest known clean tape coming within 2^-x of the end, for each x: on every line with high reach, the smallest
member of the classes with h >= x (MINT), run directly to confirm.  usage: records.py reachfile minreach cut"""
import subprocess, sys, math
D = '../'
rf, minr, cut = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
cls = {}
for l in open(D + 'lines/mlines34x.txt'):
    p = l.split(); cls.setdefault(tuple(map(int, p[1:6])), []).append((int(p[8]), int(p[9])))
sel = [tuple(map(int, l.split()[1:6])) for l in open(rf) if l.startswith('R ') and float(l.split()[7]) >= minr]
inp = ''.join('L %d %d %d %d %d 0\n' % k for k in sel)
out = subprocess.run(['nice', '-n', '10', D + 'csearch/lined_mk', str(cut)], input=inp, capture_output=True, text=True, env={'MINT': '1'}).stdout
cand = set()
for l in out.split('\n'):
    if 'mint' not in l: continue
    p = l.split(); key = tuple(map(int, p[1:6]))
    for tok in p[p.index('mint') + 1:]:
        x, k, t0 = tok.split(':')
        for (nx0, B) in cls[key]:
            for y in (0, 1): cand.add(nx0 + B * (int(t0) + (1 << int(k)) * y))
cand = sorted(cand)
r = subprocess.run([D + 'csearch/lined', 'n'], input='\n'.join(map(str, cand)) + '\n', capture_output=True, text=True).stdout.strip().split('\n')
res = []
for n, line in zip(cand, r):
    h = float(line.split('closest end meeting ')[1].split()[0]); ch = int(line.split('longest chain ')[1].split(',')[0])
    res.append((n, h, ch))
print(len(sel), 'lines,', len(res), 'candidates run')
print('smallest known n coming within 2^-x:')
for x in range(10, 26):
    ok = [t for t in res if t[1] >= x]
    if not ok: break
    n, h, ch = min(ok)
    print('  x=%2d: n = %d (%d digits, log2 %.2f), %.2f halvings, chain %d' % (x, n, n.bit_length(), math.log2(n), h, ch))
best = {}
for n, h, ch in res:
    b = n.bit_length()
    if b not in best or h > best[b][1]: best[b] = (n, h, ch)
print('best found per binary length:')
for b in sorted(best):
    if b >= 40: print('  %d digits: %.2f halvings (chain %d), n = %d' % (b, best[b][1], best[b][2], best[b][0]))
