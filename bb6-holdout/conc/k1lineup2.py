import sys
from k1lineup import *
words = ['P' * m for m in range(1, 6)] + ['Q', 'PQ', 'QP', 'PPQ', 'PQP', 'QPP', 'PQPP']
for l in open(sys.argv[1]):
    if not l.strip(): continue
    n0, kset = map(int, l.split()[:2])
    sts, hist = k1states(n0, kset)
    for (r, forms, vals) in sts[:1]:
        e = entry_line(n0, r)
        if e is None: print(n0, "no entry depth"); continue
        k, fm, vv = e
        alpha = [a for a, b in fm]; beta = [b for a, b in fm]
        res = {}
        for w in words:
            cg = forced_cong(w, vv)
            if cg is None: res[w] = 'geo'; continue
            Jm = solve1d(cg, alpha, beta)
            res[w] = '-' if Jm is None else f"{Jm.bit_length() - 1}"
        print(n0, f"entry depth {k} (settles at {kset}) round {r} |", ' '.join(f"{w}:{v}" for w, v in res.items()), flush=True)
