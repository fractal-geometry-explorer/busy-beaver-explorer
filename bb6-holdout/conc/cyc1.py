import sys
from conc import *
names = ['r', 'R', 'E']
for line in open('cyc_starts.txt').read().split('\n')[:3]:
    E, r, R = map(int, line.split())
    m = Model(3); m.W = m.var(2, E); m.add('G', m.const(1)); m.add('B', m.var(0, r)); m.add('W', m.var(1, R))
    print("start E, r, R =", E, r, R)
    nc = 0
    for rd in range(1, 11):
        m.do_round()
        path = ' '.join(m.path); m.path = []
        print(f" round {rd}: {m.shape():6s} path: {path}")
        for t, p in m.marks()[1:]: print(f"      {t} {fmt(p, names)}")
        print(f"      end {fmt(m.W, names)}")
        for d, res, mod in m.cong[nc:]: print(f"      test: {fmt(d, names)} = {res} mod {mod}")
        nc = len(m.cong)
    print()
