import re, subprocess, sys
import os
HC = os.environ.get('HALTCLASSES', './haltclasses')
def roundstarts(a, b, W, R, n):
    out = subprocess.run([HC, 'trace', str(n + 1), str(a), str(b), str(W), str(R)], capture_output=True, text=True, timeout=600).stdout
    res = []
    for line in out.splitlines():
        m = re.match(r'W=(\d+) (.*?)  meets', line)
        if not m: continue
        W_ = int(m.group(1)); ms = [(t[0], W_ - int(t[1:])) for t in m.group(2).split()]
        res.append((W_, ms))
    return res
ok = bad = 0
for fn in sys.argv[1:]:
    mem = {}
    for line in open(fn.replace('.cls', '.tsv')):
        f = line.split('\t'); mem[f[1]] = (int(f[2]), int(f[3]), int(f[4]))
    cur = None
    for line in open(fn):
        if not line.startswith(' '): cur = mem[line.split()[1]]; continue
        steps = re.findall(r'(full|half)<-(?:entry)?\(E=(\d+),R=(\d+),b=(\d+),a1=(\d+)\)', line)
        tgt = (cur[0], cur[1], cur[2], None)  # R, b, W
        # verify each step from its predecessor (first wall 449) to its landing
        land = (cur[1], cur[2], cur[0])
        for k, E, R0, b0, a1 in steps:
            E, R0, b0, a1 = map(int, (E, R0, b0, a1))
            n = 2 if k == 'half' else 8
            rs = roundstarts(449, b0, E, R0, n)
            W_, ms = rs[n]
            want = [('W', a1), ('W', land[0]), ('W', land[1] - land[2] - 1)]
            good = W_ == land[1] and ms == want
            # also no three-wall round start in between (other than the start)
            mid = [r for r in rs[1:n] if len(r[1]) == 3 and all(t == 'W' for t, _ in r[1])]
            if good and not mid: ok += 1
            else: bad += 1; print('BAD', fn, k, E, R0, b0, W_, ms, want, len(mid))
            land = (b0, E, R0)
print('ok', ok, 'bad', bad)
