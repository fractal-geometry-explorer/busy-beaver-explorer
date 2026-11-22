"""P-steps of 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB from arbitrary words, the head confined to the right of
the region `0^3 1 1 A> W`: count halts, returns (`E> 1^4 0 W'` at the region start) and exits (the head steps left
of the region), with the exit state and the first cells of the region at the exit.

usage: python3 pstep_probe.py N SEED LIMIT"""
import random
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from clockx import clock

M = "1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB"
T = clock.table(M)
N, seed, LIMIT = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rnd = random.Random(seed)
out = {}
for it in range(N):
    W = [int(rnd.random() < rnd.choice([0.3, 0.6, 0.8])) for _ in range(rnd.randint(0, 40))]
    tp = dict(enumerate([0, 0, 0, 1, 1] + W))
    pos, st = 5, 0
    res = "limit"
    for t in range(LIMIT):
        if pos == 0 and st == 4 and [tp.get(i, 0) for i in range(6)] == [1, 1, 1, 1, 0, tp.get(5, 0)] and tp.get(4) == 0:
            res = "return"
            break
        if pos < 0:
            res = "exit " + "ABCDEF"[st] + " " + "".join(str(tp.get(i, 0)) for i in range(6))
            break
        tr = T[(st, tp.get(pos, 0))]
        if tr is None:
            res = "HALT"
            break
        tp[pos], d, st = tr
        pos += d
    out[res] = out.get(res, 0) + 1
for k, v in sorted(out.items(), key=lambda x: -x[1]):
    print(v, k)
