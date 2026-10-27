import random, collections
from conc import Model
def segment(m, E, maxr=3000):
    md = Model(0); md.W = md.const(E); md.add('G', md.const(1)); md.add('M', md.const(m)); md.add('M', md.W - 2)
    for r in range(maxr):
        md.do_round()
        if md.halted or md.bad: return ('stop', None)
        mk = md.marks()
        if len(mk) == 2 and mk[1][0] == 'M' and mk[1][1].v == md.W.v - 2: return ('clean', md.W.v)
        if len(mk) == 3 and mk[1][0] == 'M' and mk[2][0] == 'M' and mk[2][1].v == md.W.v - 2: return ('gmm', (mk[1][1].v, md.W.v))
    return ('long', None)
random.seed(1)
cnt = collections.Counter()
for it in range(6000):
    E = random.randrange(10**6, 2 * 10**6) | 1; m = random.randrange(4, E - 7) & ~1
    kind, x = segment(m, E)
    if kind == 'gmm': cnt[("E", E % 3, x[1] % 3)] += 1
    if kind == 'clean': cnt[("E", E % 3, "clean", x % 3)] += 1
for k, v in sorted(cnt.items(), key=str): print(k, v)
