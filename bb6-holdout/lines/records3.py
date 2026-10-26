"""Records from predicted-lucky lines: take lines whose line-up prediction is at least P (from a KAPPA file), run the
full one-segment tree to CUT digits, collect the smallest member of the classes reaching each threshold (MINT) and the
shallowest classes (MINK), run each candidate directly, and certify the best with the real-machine macro simulation.
usage: records2.py kappafile minpred cut [more kappa files...]"""
import subprocess, sys, math, os
D = '../'
files = [sys.argv[1]] + sys.argv[4:]; minp = float(sys.argv[2]); cut = int(sys.argv[3])
sel = []
for f in files:
    for l in open(f):
        p = l.split()
        if p[0] == 'R' and 'pred' in p and float(p[p.index('pred') + 1]) >= minp: sel.append(tuple(map(int, p[1:6])))
want = set(sel); cls = {}
for l in open(D + 'lines/mlines36x.txt'):
    p = l.split(); k = tuple(map(int, p[1:6]))
    if k in want: cls.setdefault(k, []).append((int(p[8]), int(p[9])))
print(len(sel), 'lines selected', flush=True)
inp = ''.join('L %d %d %d %d %d 0\n' % k for k in sel)
out = subprocess.run(['nice', '-n', '10', D + 'csearch/lined_mk', str(cut)], input=inp, capture_output=True, text=True,
                     env=dict(os.environ, MINT='1', MINK='1')).stdout
cand = set(); reach = []
for l in out.split('\n'):
    if not l.startswith('R '): continue
    p = l.split(); key = tuple(map(int, p[1:6])); reach.append(float(p[7]))
    for tag in ('mint', 'mink'):
        if tag not in p: continue
        i = p.index(tag) + 1
        while i < len(p) and ':' in p[i]:
            x, k, t0 = p[i].split(':'); i += 1
            for (nx0, B) in cls[key]:
                for y in (0, 1): cand.add(nx0 + B * (int(t0) + (1 << int(k)) * y))
print('true reach of the selected lines: max %.2f; %d with >= 20, %d with >= 22' % (max(reach), sum(r >= 20 for r in reach), sum(r >= 22 for r in reach)), flush=True)
cand = sorted(cand)
r = subprocess.run([D + 'csearch/lined', 'n'], input='\n'.join(map(str, cand)) + '\n', capture_output=True, text=True).stdout.strip().split('\n')
res = []
for n, line in zip(cand, r):
    if 'closest end meeting' not in line: print('PROBLEM', n, n.bit_length(), line); continue
    h = float(line.split('closest end meeting ')[1].split()[0]); ch = int(line.split('longest chain ')[1].split(',')[0])
    jm = int(line.split("n' - n = ")[1]); rd = int(line.split('rounds ')[1].split(',')[0])
    res.append((n, h, ch, jm, rd))
print(len(res), 'candidates run directly')
import json
json.dump(res, open(D + 'lines/records3_out.json', 'w'))
print('smallest known n coming within 2^-x:')
front = {}
for x in range(10, 40):
    ok = [t for t in res if t[1] >= x]
    if not ok: break
    front[x] = min(ok)
best = {}
for t in res:
    b = t[0].bit_length()
    if b not in best or t[1] > best[b][1]: best[b] = t
todo = sorted({t[0] for t in front.values()} | {t[0] for b, t in best.items() if b >= 50})
sys.path.insert(0, D + 'rec'); os.chdir(D + 'rec')
import cycles
cert = {}
for n in todo:
    c = cycles.cycle(n); t = [u for u in res if u[0] == n][0]
    cert[n] = c[0] == 'clean' and c[1] - n == t[3] and c[2] == t[4]
for x, t in front.items():
    print('  x=%2d: n = %d (%d digits), %.2f halvings, chain %d, certified %s' % (x, t[0], t[0].bit_length(), t[1], t[2], cert.get(t[0])))
print('best found per binary length (50 digits and up):')
for b in sorted(best):
    if b >= 50: t = best[b]; print('  %d digits: %.2f halvings (chain %d), n = %d, certified %s, ratio %.3f' % (b, t[1], t[2], t[0], cert.get(t[0]), t[1] / math.log2(t[0])))
