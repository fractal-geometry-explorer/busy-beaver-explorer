"""The exact linear relations of the run's loop entries in rounds 10, 15, 17, 18 and 20 (found by rel.py), checked on
every entry of the sample, and the 113 EntryFar roots against them.  usage: entry_rel.py entries_all.txt
(entries_all.txt: n, round, b, W, R of every E row of sample.tsv.gz)"""
import sys, re, collections
from classify import origins
REL = {10: [(466, -298, 635, 0), (-1024, 167, 0, 2540)], 15: [(56714, -39819, 89191, 0), (-32768, 4855, 0, 178382)],
       20: [(271624, -227771, 612032, 0), (-65536, 16155, 0, 153008)], 17: [(16, -11, 24, 4)], 18: [(16, -11, 24, 4)]}
on = lambda rs, b, W, R: all(x * b + y * W + z * R + w == 0 for x, y, z, w in rs)
cnt, bad, tot = collections.Counter(), collections.Counter(), 0
for l in open(sys.argv[1]):
    n, rd, b, W, R = map(int, l.split()); tot += 1
    if rd in REL:
        cnt[rd] += 1; bad[rd] += not on(REL[rd], b, W, R)
print('entries', tot, 'in rounds with a relation', dict(cnt), 'violations', dict(bad))
def entry_far(b, W, R): D = W - b; return 15 * W <= 64 * D and 15 * W + 26 <= 32 * (D + R)
roots = []
for fn in ['n4.tsv', 'n5.tsv']:
    for line in open(fn):
        f = line.split('\t'); R, b, W = int(f[2]), int(f[3]), int(f[4])
        if W % 6 != 2: continue
        for o in origins(b, W, R):
            if o == ['entry']: rt = (b, W, R)
            else:
                m = re.findall(r'E=(\d+),R=(\d+),b=(\d+)', ' '.join(o))[-1]; rt = (int(m[2]), int(m[0]), int(m[1]))
            if entry_far(*rt): roots.append(rt)
print('EntryFar roots', len(roots))
for rd in (10, 15, 17, 20):
    print(f'round {rd}: roots on its relation {sum(on(REL[rd], *r) for r in roots)}')
