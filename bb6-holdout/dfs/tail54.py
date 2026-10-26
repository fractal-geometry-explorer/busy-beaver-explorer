"""Tail of the machine's own family from the depth-first run's settled classes (all n, asymptotic h per class)."""
import glob, math, re
D = '../dfs/K54/'
B = {}; openm = 0.0
for f in glob.glob(D + 'part_*.txt'):
    for l in open(f):
        if l.startswith('hbin'): _, h, v = l.split(); B[float(h)] = B.get(float(h), 0) + float(v)
        if l.startswith('open measure'): openm += float(l.split(':')[1])
R = {}
for l in open('../rtree1d_48.txt'):
    m = re.match(r'tail h>=(\d+) (\S+)', l)
    if m: R[int(m.group(1))] = float(m.group(2))
print('open measure after level 54 (all n): %.3e' % openm)
print(' x   all-n share (54 digits)   x2 = even-n share   rtree1d 48 digits (even n)')
for x in range(2, 19):
    t = sum(v for h, v in B.items() if h >= x - 1e-9)
    print('%2d  %.4e   %.4e   %s' % (x, t, 2 * t, '%.4e' % R[x] if x in R else '-'))
