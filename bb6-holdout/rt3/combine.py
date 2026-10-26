import re, sys
C = sys.argv[1]
tot = {}; cnt = {}; meas = 0; top = 0; lost = 0; hmax = 0
for f in (f's{C}_0.err', f's{C}_1.err'):
    t = open(f).read()
    lost += float(re.search(r'lost ([0-9.e+-]+)', t).group(1))
    m = re.search(r'phase-0 plain entries: measure ([0-9.e+-]+), largest sigma ceiling ([0-9.]+); measure by sigma ceiling \(floor\):(.*)', t)
    meas += float(m.group(1)); top = max(top, float(m.group(2)))
    for b, ms, n in re.findall(r' (\d+):([0-9.e+-]+)/(\d+)', m.group(3)):
        tot[int(b)] = tot.get(int(b), 0) + float(ms); cnt[int(b)] = cnt.get(int(b), 0) + int(n)
    hmax = max(hmax, float(re.search(r'in any run before it reaches G W W W: ([0-9.]+)', t).group(1)))
print(f'{C} bits: entry measure {meas:.4e}, undecided {lost:.3e}, largest ceiling {top:.2f}, most halvings in a run before G W W W {hmax:.2f}')
tail = 0; out = []
for b in sorted(tot, reverse=True):
    tail += tot[b]
    if b >= 20: out.append(f'>={b}:{tail:.2e}')
print('  ceiling tail:', ' '.join(out))
