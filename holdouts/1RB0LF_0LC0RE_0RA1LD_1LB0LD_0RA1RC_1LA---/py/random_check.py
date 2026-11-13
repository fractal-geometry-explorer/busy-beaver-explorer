"""Runs one macro step from random block lists and reports halts.

usage: python3 random_check.py SEED COUNT
Lists are drawn with block sizes 0..11, 20..23, 30, 31, 40, 41 and either separator, with the record head
0^inf B> 0 (or 0^inf 1 B> 1 with first block (0,0), the form seen right after a reset).  Lists in the language `in_lang`
(the pattern every record of the run shows) are counted apart from the others."""
import random, sys
from blockmm import macro_step, Fail

def in_lang(ell, c, bl):
    """The pattern every record of the run shows (checked on the first 10^6 records by stats.py): no block (0,1)
    after the first; after a block ending in 0 the next block (D, x) has D + x even; the first block has D + x odd
    (head 0^inf B> 0), or the head is 0^inf 1 B> 1, the first block (0,0) and the second has D + x odd."""
    k0 = 0
    if (ell, c) == ((1,), 1):
        if not bl or bl[0] != (0, 0):
            return False
        k0 = 1
    elif (ell, c) != ((), 0):
        return False
    if len(bl) > k0 and (bl[k0][0] + bl[k0][1]) % 2 != 1:
        return False
    for k in range(k0 + 1, len(bl)):
        if bl[k] == (0, 1):
            return False
        if bl[k - 1][1] == 0 and (bl[k][0] + bl[k][1]) % 2 == 1:
            return False
    return True


rng = random.Random(int(sys.argv[1]))
Ds = list(range(0, 12)) + [20, 21, 22, 23, 30, 31, 40, 41]
res = {}
for trial in range(int(sys.argv[2])):
    reset = rng.random() < 0.2
    ell, c = ((1,), 1) if reset else ((), 0)
    bl = [(0, 0)] if reset else []
    want = rng.random() < 0.7          # draw from the language, or anything
    n = rng.randint(1, 14)
    while len(bl) < n + reset:
        b = (rng.choice(Ds), rng.randint(0, 1))
        if not want or in_lang(ell, c, bl + [b]):
            bl.append(b)
    canon = in_lang(ell, c, bl)
    try:
        r = macro_step(ell, c, bl)
        out = 'halt' if r[0] is None else 'ok'
    except Fail as e:
        out = 'stuck'
    key = ('canonical' if canon else 'other', out)
    res[key] = res.get(key, 0) + 1
    if out == 'halt' and canon:
        print('HALT on a canonical list', ell, c, bl, r[2], flush=True)
print(res)
