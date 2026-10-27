"""Random well-formed round starts (the marks after the gap at 1 and the width), as in ../lean/Test3b.lean: the
stripe before a mark of value v has odd length exactly when the cell before it has value v, and the last stripe
(before the width) has odd length exactly when the last mark has value 0.  About half the starts end in a short last
stripe, which is where the trailing-wall sequence starts.
usage: python3 gen.py N SEED [MAXBASE] > starts"""
import random, sys
VAL = {'M': 1, 'W': 0, 'B': 1}; LEN = {'M': 2, 'W': 2, 'B': 3}
n, seed = int(sys.argv[1]), int(sys.argv[2]); mb = int(sys.argv[3]) if len(sys.argv) > 3 else 6
rng = random.Random(seed)
for _ in range(n):
    q, u, ms = 4, 0, []
    for _ in range(rng.randrange(7)):
        t = rng.choice('MWB'); base = rng.randrange(mb)
        ln = 2 * base + 1 if u == VAL[t] else 2 * base
        ms.append((t, q + ln)); q += ln + LEN[t]; u = VAL[t]
    base = 0 if rng.random() < 0.5 else rng.randrange(mb)
    ln = 2 * base + 1 if u == 0 else 2 * base
    print(' '.join([str(q + ln)] + ['%s %d' % m for m in ms]))
