"""How often the round's defect reaches the digit-only end Z of the tape, and how far it gets there.

usage: python3 py/reach.py ROUNDS [FIRST=100]

Runs the token rules (py/tokz.py). Z is the longest suffix of the round's starting tape made of digits O, I only.
e = (word where the defect disappears) - (first word of Z), in the round's own numbering: e >= 0 means the defect
got into Z and ate e words of it (Z then starts e + 2 words further on), e < 0 that it disappeared before Z.
Prints the share of rounds with e >= 0, whether that share depends on the previous rounds, the distribution of e
when e >= 0, the mean number of words Z loses per round (it gains 4), and the smallest |Z| / k.
"""
import sys
from collections import Counter
import tokz
from tokz import T

R = int(sys.argv[1]); FIRST = int(sys.argv[2]) if len(sys.argv) > 2 else 100
T[:] = list('LLLzLLOLOI')
rows = []
for k in range(6, R + 1):
    zs = len(T)
    while zs > 0 and T[zs - 1] in 'OI': zs -= 1
    zlen = len(T) - zs
    tokz.stats['die'] = []
    tokz.An(1, 0); T.insert(0, 'x'); tokz.norm()
    while T and T[-1] == 'O': T.pop()
    d = tokz.stats['die']
    if len(d) != 1 or d[0][0] != 'IO': print('round', k, 'unusual end of the defect:', d)
    if not d: print('round', k, 'the defect survived the round'); continue
    if k >= FIRST: rows.append((k, zlen, d[0][2] - zs))
reach = ''.join('1' if e >= 0 else '0' for _, _, e in rows)
n = len(rows); p = reach.count('1') / n
es = [e for _, _, e in rows if e >= 0]
print('rounds %d..%d: defect reaches Z in %d of %d rounds (%.3f)' % (FIRST, R, len(es), n, p))
for ctx in ['1', '0', '11', '00', '000']:
    m = h = 0
    for i in range(len(ctx), n):
        if reach[i - len(ctx):i] == ctx: m += 1; h += reach[i] == '1'
    print('  after rounds %-4s (reach = 1): share reaching %.3f (%d cases)' % (ctx, h / m, m))
c = Counter(es)
print('e when it reaches Z: mean %.2f, largest %d; counts for e = 0..15:' % (sum(es) / len(es), max(es)),
      [c[i] for i in range(16)])
print('loss of Z per round (e + 2 when it reaches Z): mean %.3f (gain 4)' % (sum(e + 2 for e in es) / n))
print('smallest |Z|/k: %.3f; |Z|/k at round %d: %.3f' % (min(z / k for k, z, _ in rows), rows[-1][0], rows[-1][1] / rows[-1][0]))
