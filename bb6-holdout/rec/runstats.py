"""Collect the run-token windows that occur in the certified run (for choosing adjacency rules)."""
import sys, collections
import proofs, casesim
from symtm import Config, Blank, Rep, try_lemma, step
from inv import config_string

def cells_of(seq, cap=4):
    out = []
    for t in seq:
        if isinstance(t, tuple):
            w, n = t; out.extend(list(w) * min(n, cap))
        else: out.append(t)
    return out

def run_tokens(cells):
    """Tokens (sym, len, where) and 'A'/'e' head info, from a cell string with e / A symbols (no blanks)."""
    # trim blank zeros
    s = list(cells)
    while s and s[0] == "0": s.pop(0)
    while s and s[-1] == "0": s.pop()
    toks = []; head_seen = False; i = 0
    cur = None  # [sym, len, where]
    for c in s:
        if c == "A":
            head_seen = True
            if cur and cur[0] == 1: cur[2] = "H"
            else:
                if cur: toks.append(tuple(cur)); cur = None
                toks.append(("A",))
            continue
        val = 0 if c in "0e" else 1
        if cur and cur[0] == val:
            cur[1] += 1
            if c == "e": cur[2] = "H"; head_seen = True
        else:
            if cur: toks.append(tuple(cur))
            cur = [val, 1, "R" if head_seen else "L"]
            if c == "e": cur[2] = "H"; head_seen = True
    if cur: toks.append(tuple(cur))
    return toks

def collect(rounds):
    cfg = Config([Blank()], "A", [Blank()])
    while not proofs.is_pass_position(cfg):
        if not try_lemma(cfg): step(cfg)
    stats = collections.Counter(); phase = "gap"; r = 0; ncfg = 0
    def add(cfg):
        toks = run_tokens(cells_of(config_string(cfg)))
        ph = cfg.state
        # windows of 2 and 3 runs; the packet A is kept as an extra token inside the window
        idx = [i for i, t in enumerate(toks) if t != ("A",)]
        for k in (2, 3):
            for a in range(len(idx) - k + 1):
                stats[(ph,) + tuple(toks[idx[a]:idx[a + k - 1] + 1])] += 1
    add(cfg)
    while r < rounds:
        if phase == "gap":
            cfg = casesim.gap_phase(cfg); phase = "gap" if proofs.is_pass_position(cfg) else "packet"
        else:
            cfg, kind = casesim.packet_phase(cfg)
            if kind == "round": r += 1
            phase = "packet" if kind == "packet" else "gap"
        add(cfg); ncfg += 1
    return stats, ncfg

if __name__ == "__main__":
    import pickle
    stats, n = collect(int(sys.argv[1]))
    pickle.dump(stats, open("runstats.pkl", "wb"))
    print("configurations:", n, "distinct windows:", len(stats))
