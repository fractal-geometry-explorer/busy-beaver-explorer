"""Phase ends from arbitrary recursion stacks (machine 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB, g = 3).

During tick recursion the tape left of a P-step is `0^inf [1 1 1 0^(3 c_1)] ... [1 1 1 0^(3 c_d)] 0^3 1 1 A> W`.
Start there with random d, c_i and W, run cell by cell, and report halts; a run is stopped when the head is in
state E on a 0 with only 0s to its left (a visit of the left end) or after LIMIT steps.

usage: python3 stack_probe.py N SEED LIMIT"""
import random
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import clockx  # noqa: F401
from clockx import clock

M = "1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB"
T = clock.table(M)
N, seed, LIMIT = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rnd = random.Random(seed)
out = {}
for it in range(N):
    left = []
    for _ in range(rnd.randint(0, 6)):
        left += [1, 1, 1] + [0] * (3 * rnd.randint(0, 5))
    left += [0, 0, 0, 1, 1]
    W = [int(rnd.random() < 0.6) for _ in range(rnd.randint(0, 25))]
    tp = dict(enumerate([0] * 4 + left + W))
    pos, st = 4 + len(left), 0
    lo = 0
    res = "limit"
    for t in range(LIMIT):
        if st == 4 and tp.get(pos, 0) == 0 and all(tp.get(i, 0) == 0 for i in range(min(lo, pos) - 1, pos)):
            res = "visit"
            break
        tr = T[(st, tp.get(pos, 0))]
        if tr is None:
            res = "HALT"
            break
        tp[pos], d, st = tr
        pos += d
        lo = min(lo, pos)
    out[res] = out.get(res, 0) + 1
    if res == "HALT" and out[res] <= 5:
        print("HALT", clock.rle(bytes(left)), "|", clock.rle(bytes(W)), t)
print(out)
