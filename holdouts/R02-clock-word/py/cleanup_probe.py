"""Phase ends of 1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB from the exits of a P-step (pstep_probe.py): the tape
`0^inf S s< r X` with S a recursion stack (a block `1^(4+3k)`-built tick: `[1 1 1 0^(3c)]*`), s and r an exit state
and the region cells at the exit, X arbitrary.  Reports halts, how far right of the region the head goes, and
whether the run reaches a tick start `0^3 E> 1^(4+3k) 0` with only 0s to its left.

usage: python3 cleanup_probe.py N SEED LIMIT"""
import random
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from clockx import clock

M = "1RB0LE_0LC0RB_1RD1LD_1RA1LF_0LB1LE_---1LB"
T = clock.table(M)
EXITS = [("B", "011011"), ("B", "111011"), ("E", "111111"), ("B", "111001"), ("E", "111110")]
N, seed, LIMIT = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rnd = random.Random(seed)
out = {}
far = 0
for it in range(N):
    S = []
    for _ in range(rnd.randint(0, 6)):
        S += [1, 1, 1] + [0] * (3 * rnd.randint(0, 5))
    s, r = rnd.choice(EXITS)
    X = [int(rnd.random() < 0.6) for _ in range(rnd.randint(0, 30))]
    base = 8 + len(S)                         # index of the region's first cell
    tp = dict(enumerate([0] * 8 + S + [int(c) for c in r] + X))
    pos, st = base - 1, "ABCDEF".index(s)
    res = "limit"
    mx = 0
    for t in range(LIMIT):
        mx = max(mx, pos - base)
        if st == 4 and tp.get(pos, 0) == 1 and all(tp.get(pos - i, 0) == 0 for i in range(1, 12)) \
                and all(tp.get(i, 0) == 0 for i in range(min(tp), pos)):
            L = 0
            while tp.get(pos + L, 0) == 1:
                L += 1
            res = "tick start L=%d (mod 3: %d)" % (L, L % 3)
            break
        tr = T[(st, tp.get(pos, 0))]
        if tr is None:
            res = "HALT"
            break
        tp[pos], d, st = tr
        pos += d
    far = max(far, mx)
    key = (res, s + r, "right of region: %d" % min(mx, 7))
    out[key] = out.get(key, 0) + 1
for k, v in sorted(out.items(), key=lambda x: -x[1]):
    print(v, *k)
print("max cells right of the region start", far)
