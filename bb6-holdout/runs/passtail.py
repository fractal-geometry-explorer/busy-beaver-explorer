"""Extra-wall pass counts along the routes of the route tree's entries.
Reads S lines (stdin), counts complete extra-wall passes (the 8-round words P and Q of the one-extra-wall loop, and the
family's longer words with more walls are counted by their G W W W W-type rounds), and tabulates the measure 2^-bits of
the entries by that count and by ceiling.  usage: passtail.py [min_ceiling] < S-lines"""
import sys, re, math
from collections import defaultdict
P = 'GBWW GWWWW GBWW GMBW GMWWW GMBW GMWWW GWWWW'.split()
Q = 'GBWW GMMWW GMWWW GMBW GMWWW GMBW GMWWW GWWWW'.split()
mc = float(sys.argv[1]) if len(sys.argv) > 1 else 0
pat = re.compile(r'^S (\S+) t=\S+ bits (\d+) .*\| (.*)$')
bycount = defaultdict(float); bycount_n = defaultdict(int)
bybin = defaultdict(lambda: defaultdict(float)); bybin_n = defaultdict(lambda: defaultdict(int))
maxc = defaultdict(float)     # highest ceiling by extra-wall pass count
words = defaultdict(float)
XW = set(P) | set(Q)
byxw = defaultdict(float); byxw_n = defaultdict(int); maxcx = defaultdict(float)
n = 0
for line in sys.stdin:
    m = pat.match(line)
    if not m: continue
    c = float(m.group(1)); bits = int(m.group(2)); route = m.group(3).split()
    if c < mc: continue
    n += 1; w = 2.0 ** -bits
    # count P / Q words greedily, non-overlapping
    k = 0; i = 0; word = []
    while i + 8 <= len(route):
        seg = route[i:i + 8]
        if seg == P: k += 1; word.append('P'); i += 8
        elif seg == Q: k += 1; word.append('Q'); i += 8
        else: i += 1
    bycount[k] += w; bycount_n[k] += 1
    b = int(c // 4) * 4
    bybin[b][k] += w; bybin_n[b][k] += 1
    if c > maxc[k]: maxc[k] = c
    words[''.join(word) or '-'] += w
    xw = sum(1 for r in route if r in XW)
    byxw[xw] += w; byxw_n[xw] += 1
    if c > maxcx[xw]: maxcx[xw] = c
print('entries', n)
print('measure by number of complete extra-wall passes (P or Q words) on the route:')
for k in sorted(bycount): print('  %d passes: measure %.3e (%d entries), highest ceiling %.2f' % (k, bycount[k], bycount_n[k], maxc[k]))
print('by ceiling bin (measure, then entries):')
ks = sorted(bycount)
print('  bin   ' + ' '.join('%10d' % k for k in ks))
for b in sorted(bybin):
    print('  %3d-%-3d' % (b, b + 4) + ' '.join('%10.2e' % bybin[b].get(k, 0) for k in ks))
    print('         ' + ' '.join('%10d' % bybin_n[b].get(k, 0) for k in ks))
print('pass words by measure:')
for wd, m in sorted(words.items(), key=lambda x: -x[1])[:20]: print('  %-8s %.3e' % (wd, m))
print('measure by number of extra-wall-loop rounds (any of the P/Q round shapes) on the route:')
for k in sorted(byxw): print('  %2d rounds: measure %.3e (%d entries), highest ceiling %.2f' % (k, byxw[k], byxw_n[k], maxcx[k]))
