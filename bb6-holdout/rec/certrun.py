"""Run the machine from a blank tape with the symbolic simulator (single steps + proven cycle lemmas) and
report every clean tape, to check the simulator against the plain step-by-step run."""
import json, sys
from symtm import *

def clean_n(cfg):
    if cfg.state != "A" or canon(cfg.left) != [Blank()]: return None
    r = canon(cfg.right)
    if r[:2] != [1, 1]: return None
    k, rest = count_pairs(r[2:], (1, 0))
    if canon(rest) == [1, 1, Blank()] and k.is_const(): return k.k
    return None

def certified_cleans(max_steps):
    cfg = Config([Blank()], "A", [Blank()])
    found = []
    while cfg.steps.k < max_steps:
        if not try_lemma(cfg):
            step(cfg)
        else:
            n = clean_n(cfg)
            if n is not None: found.append((cfg.steps.k - 1, n))
        # keep the token lists compact
        if len(cfg.left) > 40: cfg.left = compact(cfg.left)
        if len(cfg.right) > 40: cfg.right = compact(cfg.right)
    return found

def compact(seq):
    """Merge adjacent literal 10/01 pairs into repeats (pure bookkeeping, the tape is unchanged)."""
    out = canon(seq)
    res = []
    for t in out:
        res.append(t)
        # fold "1 0" literal pairs into a following/preceding repeat of 10
        while len(res) >= 3 and isinstance(res[-1], int) and isinstance(res[-2], int) and isinstance(res[-3], Rep) and res[-3].word == (res[-2], res[-1]):
            r = res[-3]; res[-3:] = [Rep(r.word, r.n + 1)]
    # fold long literal runs of a 2-cycle into repeats
    final = []; i = 0
    while i < len(res):
        if isinstance(res[i], int) and i + 3 < len(res) and all(isinstance(res[j], int) for j in range(i, i + 4)) and res[i] == res[i + 2] and res[i + 1] == res[i + 3] and res[i] != res[i + 1]:
            w = (res[i], res[i + 1]); k = 0
            while i + 1 < len(res) and isinstance(res[i], int) and isinstance(res[i + 1], int) and (res[i], res[i + 1]) == w:
                k += 1; i += 2
            final.append(Rep(w, Lin(k)))
        else:
            final.append(res[i]); i += 1
    return final

if __name__ == "__main__":
    N = int(sys.argv[1])
    found = certified_cleans(N)
    known = [tuple(x[:2]) for x in json.load(open('../m2/clean3e9.json')) if x[0] <= N]
    print(len(found), len(known), found == known)
    print(found[:8])
