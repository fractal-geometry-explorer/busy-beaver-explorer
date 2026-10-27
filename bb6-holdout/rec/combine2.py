"""Combine route-ceiling parts. Entries emitted before the split depth are found by every part, so the shallow tree
(cut = split - 1) is subtracted nparts - 1 times."""
import re, sys
def hist(f):
    t = open(f).read()
    m = re.search(r'phase-0 plain entries: measure ([0-9.e+-]+), largest sigma ceiling ([0-9.]+); measure by sigma ceiling \(floor\):(.*)', t)
    h = {}
    for b, ms, n in re.findall(r' (\d+):([0-9.e+-]+)/(\d+)', m.group(3)): h[int(b)] = (float(ms), int(n))
    lost = float(re.search(r'lost ([0-9.e+-]+)', t).group(1))
    hm = float(re.search(r'in any run before it reaches G W W W: ([0-9.]+)', t).group(1))
    return float(m.group(1)), float(m.group(2)), h, lost, hm
def combine(files, shallow):
    meas = 0; top = 0; H = {}; lost = 0; hm = 0
    for f in files:
        a, b, h, l, x = hist(f); meas += a; top = max(top, b); lost += l; hm = max(hm, x)
        for k, (ms, n) in h.items(): H[k] = (H.get(k, (0, 0))[0] + ms, H.get(k, (0, 0))[1] + n)
    a, b, h, l, x = hist(shallow); k1 = len(files) - 1
    meas -= k1 * a
    for k, (ms, n) in h.items(): H[k] = (H[k][0] - k1 * ms, H[k][1] - k1 * n)
    return meas, top, H, lost, hm
if __name__ == '__main__':
    files = sys.argv[2:]; meas, top, H, lost, hm = combine(files, sys.argv[1])
    print(f'entry measure {meas:.6e}, undecided {lost:.3e}, largest ceiling {top:.3f}, most halvings before G W W W {hm:.2f}')
    tail = 0; out = []
    for b in sorted(H, reverse=True):
        tail += H[b][0]
        if b >= 15: out.append(f'>={b}:{tail:.3e}')
    print('  tail:', ' '.join(out))
