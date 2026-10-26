"""Frontier from lucky lines: for lines (with their n-class) whose one-segment reach is high, the shallowest class
reaching each threshold x, the explicit smallest members, and a direct run of each.
usage: frontier.py reachfile minreach cut"""
import subprocess, sys, collections
D = '../'
rf, minr, cut = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
cls = {}
for l in open(D + 'lines/mlines30x.txt'):
    p = l.split(); cls.setdefault(tuple(map(int, p[1:6])), []).append((int(p[8]), int(p[9])))
sel = []
for l in open(rf):
    p = l.split()
    if p[0] == 'R' and float(p[7]) >= minr: sel.append(tuple(map(int, p[1:6])))
inp = ''.join('L %d %d %d %d %d 0\n' % k for k in sel)
out = subprocess.run(['nice', '-n', '5', D + 'csearch/lined_mk', str(cut)], input=inp, capture_output=True, text=True, env={'MINK': '1'}).stdout
best = {}   # x -> (total depth, n candidates)
for l in out.split('\n'):
    if not l.startswith('R '): continue
    p = l.split(); key = tuple(map(int, p[1:6]))
    if 'mink' not in p: continue
    for tok in p[p.index('mink') + 1:]:
        x, k, x0 = map(int, tok.split(':'))
        for (nx0, B) in cls[key]:
            tot = key[0] + k
            # members n = nx0 + B*(x0 + 2^k y); smallest with y = 0 and y = 1
            ns = [nx0 + B * (x0 + (1 << k) * y) for y in (0, 1)]
            if x not in best or tot < best[x][0] or (tot == best[x][0] and min(ns) < min(best[x][1])):
                best[x] = (tot, ns, key)
todo = sorted({n for x in best for n in best[x][1]})
res = {}
r = subprocess.run([D + 'csearch/lined', 'n'], input='\n'.join(map(str, todo)) + '\n', capture_output=True, text=True).stdout.strip().split('\n')
for n, line in zip(todo, r):
    h = float(line.split('closest end meeting ')[1].split()[0]); ch = int(line.split('longest chain ')[1].split(',')[0]); res[n] = (h, ch)
print('x   shallowest class found (digits)   smallest members: bits, direct-run halvings, chain')
for x in sorted(best):
    tot, ns, key = best[x]
    print('%2d  %d (line depth %d)   ' % (x, tot, key[0]) + '   '.join('%d bits: %.2f, %d' % (n.bit_length(), *res[n]) for n in ns))
    print('      n =', ns[0])
