"""Test the macro machine py/mac14.py against the real machine (py/tmsweep.py) on random lists, one sweep each.
The lists have the shape the run has: fuel, done blocks, a window, more entries, and a right end `... ! 0`.
usage: check_rules.py COUNT [SEED [WINDOW]]   WINDOW: mid, mid0, fold, fold2, merge!! (forces that window shape)"""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tmsweep import sweep
from mac14 import step, Unknown, trim
D = ['.', 0, '!', 1, '.']
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
only = sys.argv[3] if len(sys.argv) > 3 else None


def rnd_rest():
    out = []
    for _ in range(random.randint(0, 4)):
        if random.random() < 0.4: out += D + [random.randint(2, 9)]
        else: out += [random.choice('.!'), random.randint(1, 6)]
    return out + random.choice([D + [1, '!', 0], ['!', 0], ['.', 1, '!', 0]])


cnt = {}; bad = 0
for t in range(int(sys.argv[1])):
    N = random.choice([random.randint(2, 12), 0, 1])
    ds = []
    for _ in range(random.randint(0, 3)): ds += D + [random.randint(2, 8)]
    x = random.randint(1, 9)
    W = {'mid': [x, '.', 0, '!', random.randint(2, 7)],
         'fold': [x, '.', 0, '!', 0, '!', 1, '.', random.randint(0, 6)],
         'fold2': [x, '!', 0, '.', random.randint(0, 6)],
         'mid0': [x, '.', 0, '!', 0, random.choice('.!'), random.randint(1, 6)],
         'merge!!': [x, '!', 0, '!', random.randint(0, 6), '!', random.randint(1, 5)]}.get(only, [x])
    L = trim([N] + ds + D + W + rnd_rest())
    try: P, r = step(L)
    except Unknown: continue
    if only and only not in r: continue
    n, R = sweep(L)
    key = r.split('+')[0] if '/N1' not in r else 'fuel-1 visit'
    cnt[key] = cnt.get(key, 0) + 1
    if R != P:
        bad += 1
        if bad < 6: print('MISMATCH', r, L, '\n machine', R, '\n macro  ', P)
print(bad, 'mismatches;', sum(cnt.values()), 'sweeps tested:', sorted(cnt.items()))
