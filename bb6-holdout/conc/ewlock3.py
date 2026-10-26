import random, collections, sys
from ewlock2 import consistent, family
random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 3)
nvar = int(sys.argv[1]); LMAX = 5
hist = collections.Counter()
for trial in range(int(sys.argv[3]) if len(sys.argv) > 3 else 40):
    fam = family(nvar); frontier = ['']; longest = 0; count = 0
    for L in range(1, LMAX + 1):
        nxt = [w + x for w in frontier for x in 'PQ' if consistent(fam, nvar, w + x)]
        if not nxt: break
        longest = L; count = len(nxt); frontier = nxt
    hist[(longest, count if longest == LMAX else None)] += 1
print(f"{nvar}-parameter families: (longest consistent P/Q word up to {LMAX}, number at max length) -> {dict(sorted(hist.items(), key=str))}")
