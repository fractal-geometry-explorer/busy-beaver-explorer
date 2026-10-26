"""GMM-born chains on bare families: for every entry family with an extra-wall cap >= 1 (from entrycaps), try
word + progress-keeping drop (U, V, T) + p plain passes; report the longest chains the position map allows."""
import json, re, collections
from fractions import Fraction as F
from lattice import Coset as LCoset
import mixdrop as MD
from capdepth import fam_of
P5 = {}
def conds(word):
    if word not in P5:
        m, err = MD.forced(word, F(2) ** (4 * len(word) + 120))
        P5[word] = None if m is None else m.cong
    return P5[word]
def consistent(fam, word):
    cs = conds(word)
    if cs is None: return False
    C = LCoset(2)
    for form5, res, mod in cs:
        f = [F(0)] * 3
        for i in range(5):
            for j in range(3): f[j] += form5.f[i] * fam[i][j]
        f[2] += form5.f[5]
        den = max(q.denominator for q in f)
        if not C.impose([int(q * den) for q in f[:2]], den * res - int(f[2] * den), den * mod, reduce=False): return False
    return True
fams = []
for l in open('../entrycaps.txt'):
    m = re.match(r"route (\d+) \+ (\d+) passes \+ entry (\d+): words (\[.*\])", l)
    if m: fams.append((int(m.group(1)), int(m.group(2)), int(m.group(3)), eval(m.group(4))))
print(len(fams), "families with a cap of 2 or more listed in the log")
best = []
for ri, p, si, words in fams:
    fam = fam_of(ri, p, si)
    for w in words:
        for k in range(1, len(w) + 1):
            pre = w[:k]
            for d in 'UVT':
                if not consistent(fam, pre + d): continue
                q = 0
                while q < 8 and consistent(fam, pre + d + 'L' * (q + 1)): q += 1
                best.append((4 * len(pre) + 4 * q, ri, p, si, pre + d + 'L' * q))
best.sort(reverse=True)
for b in best[:15]: print(b)
print(len(best), 'consistent drop continuations')
