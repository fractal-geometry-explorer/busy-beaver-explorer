"""Statistics of the defect over a long run, from the record file of c/toksim.cpp.

usage: python3 py/rounds_stats.py RECORD_FILE [FIRST=100]

For each round the record holds k, |Z| (digit-only end at the round's start), e (where the defect died minus where
Z started; e >= 0: it got into Z and ate e words, Z then loses e + 2) and the kind of death. Prints how often the
defect gets into Z (and whether that depends on the round before), the distribution of e, the largest loss in a
window of W rounds for several W (the lemma needs the average loss to stay below about 3 words per round over
every stretch from the start; Z gains 4), the smallest |Z| / k, and the smallest margin |Z| - (k + 2 log2 k + 20).
"""
import math
import struct
import sys
from collections import Counter

path = sys.argv[1]; FIRST = int(sys.argv[2]) if len(sys.argv) > 2 else 100
data = open(path, 'rb').read()
n = len(data) // 16
K = []; Zl = []; E = []; KIND = []
for i in range(n):
    k, z, e, kind = struct.unpack_from('<iiii', data, 16 * i)
    if k < FIRST: continue
    K.append(k); Zl.append(z); E.append(e); KIND.append(kind)
N = len(K)
odd = [i for i in range(N) if KIND[i] != 0]
print('rounds %d..%d (%d rounds); rounds whose defect did not end at 1 I O -> O L: %d' % (K[0], K[-1], N, len(odd)))
reach = [1 if e >= 0 else 0 for e in E]
p = sum(reach) / N
print('defect gets into Z: %d of %d rounds (%.4f)' % (sum(reach), N, p))
for ctx in ['1', '0', '11', '00', '111']:
    m = h = 0
    L = len(ctx)
    s = ''.join(map(str, reach))
    i = s.find(ctx)
    while i != -1 and i + L < N:
        m += 1; h += reach[i + L]; i = s.find(ctx, i + 1)
    print('  after %-3s: %.4f (%d cases)' % (ctx, h / m if m else float('nan'), m))
es = [e for e in E if e >= 0]
c = Counter(es)
mx = max(es); kmx = K[E.index(mx)]
print('e when it gets in: mean %.3f, largest %d (round %d); tail ratio (count e+1)/(count e), e = 0..20:' % (sum(es) / len(es), mx, kmx))
print('  ' + ' '.join('%.2f' % (c[i + 1] / c[i]) if c[i] else '-' for i in range(21)))
loss = [e + 2 if e >= 0 else 0 for e in E]
print('mean loss of Z per round: %.4f (gain 4)' % (sum(loss) / N))
for W in [10, 100, 1000, 10000, 100000]:
    if W > N: break
    s = sum(loss[:W]); best = s; at = 0
    for i in range(W, N):
        s += loss[i] - loss[i - W]
        if s > best: best = s; at = i - W + 1
    print('  largest mean loss over %6d rounds in a row: %.3f (from round %d)' % (W, best / W, K[at]))
r = [(Zl[i] / K[i], K[i]) for i in range(N) if K[i] >= 1000]
print('smallest |Z|/k from round 1000: %.4f (round %d); |Z|/k at the end: %.4f' % (min(r) + (Zl[-1] / K[-1],)))
mg = [(Zl[i] - (K[i] + 2 * math.log2(K[i]) + 20), K[i]) for i in range(N)]
print('smallest |Z| - (k + 2 log2 k + 20): %.0f (round %d); from round 1000: %.0f' % (min(mg) + (min(m for m, k in mg if k >= 1000),)))
