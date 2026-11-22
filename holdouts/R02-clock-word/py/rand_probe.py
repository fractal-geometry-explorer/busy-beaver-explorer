"""Random words (arbitrary bits, density p of 1s) and starting blocks L0, one phase each (phase_probe.phase).

usage: python3 rand_probe.py MACHINE N SEED MAXLEN P L0S"""
import random
import sys
import phase_probe as pp
from clockx import clock
m, N, seed, ml, p = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5])
L0s = [int(x) for x in sys.argv[6].split(",")]
rnd = random.Random(seed)
res = {}
for i in range(N):
    W = bytes(int(rnd.random() < p) for _ in range(rnd.randint(1, ml)))
    L0 = rnd.choice(L0s)
    r = pp.phase(m, W, L0, limit=10 ** 25, maxvisits=200)
    res[r[0]] = res.get(r[0], 0) + 1
    if r[0] == "HALT" and res["HALT"] <= 5:
        print("HALT", L0, clock.rle(W), r[1], flush=True)
print(res)
