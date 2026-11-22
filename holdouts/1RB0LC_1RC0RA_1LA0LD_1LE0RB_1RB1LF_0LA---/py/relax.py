"""The relaxed run of 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA---: the budget may run out early.

In the real run a cursor stalls when the first run (the budget) is used up.  Here, at a round start, the first run
may in addition be cut (to a smaller value, or removed), so cursors stall at places the real run never chooses.
Every real tape is a relaxed tape, so a proof that the relaxed run never halts would settle the machine without
knowing how large the budgets are.

usage: python3 relax.py cuts SEEDS ROUNDS [KEEP]   random cuts; KEEP = 0: remove the first run (any stall),
                                                     KEEP = 2, 4, 8: cut to a value with the same residue mod KEEP
       python3 relax.py words SEEDS ROUNDS P        which cursor words occur, and which sit right before a separator
       python3 relax.py route                       the halting route: an odd arrival at a stalled | 1 "110" |, a stall
                                                     three rounds later, and an even arrival

Each line of `cuts`: seed, halted or not, rounds, cuts, and the number of round starts with 1111 on the tape.
"""
import random, sys
from tok import Sim, cells, show, round_
from scan import segs, parse


def hot(t):
    """The moving cursor is near a separator or another cursor, or is not a plain 0 or 1."""
    g = segs(t)
    ci = [i for i, x in enumerate(g) if type(x) is str and x[0] == '"']
    if not ci: return False
    i = ci[0]
    if g[i] not in ('"0"', '"1"'): return True
    nxt = g[i + 1:i + 2]
    return not nxt or type(nxt[0]) is str or nxt[0] <= 2


def relaxed(seed, R, keep, p=0.005, q=0.3, watch=None):
    rng = random.Random(seed); s = Sim(); cuts = n1111 = 0
    while not s.halted and s.rounds < R and len(s.toks) < 3000:
        t = s.toks
        if watch: watch(t)
        if '1111' in cells(t): n1111 += 1
        if t and type(t[0]) is list and len(t) > 1 and rng.random() < (q if hot(t) else p):
            m = t[0][0]
            v = 0 if not keep else m % keep + keep * rng.randrange(2)
            if v < m:
                cuts += 1
                if v: t[0][0] = v
                else: t.pop(0)
        if not s.jump_if(): s.explicit()
    return s, cuts, n1111


def cmd_cuts(seeds, R, keep):
    bad = 0
    for seed in seeds:
        s, cuts, n1111 = relaxed(seed, R, keep)
        print(seed, 'HALT' if s.halted else 'no halt', s.rounds, 'rounds', cuts, 'cuts', n1111, 'with 1111', flush=True)
        bad += s.halted
    return 1 if bad else 0


def cmd_words(seeds, R, p):
    W = {}; B = {}
    def watch(t):
        g = segs(t)
        for i, x in enumerate(g):
            if type(x) is str and x[0] == '"':
                W[x] = W.get(x, 0) + 1
                if i + 1 < len(g) and g[i + 1] == '|': B[x] = B.get(x, 0) + 1
    for seed in seeds:
        relaxed(seed, R, 0, p=p, q=p, watch=watch)
    print('cursor words:', W)
    print('right before a separator:', B)
    return 1 if any(w.endswith('110"') for w in B) else 0


def rounds(s, n):
    t = parse(s); out = [s]
    for _ in range(n):
        t, _ = round_(t)
        if t is None: out.append('HALT'); break
        out.append(show(t))
    return out


def cmd_route():
    print('odd arrival at a stalled | 1 "110" | (four 1s, after a separator):')
    for x in rounds('20 | 9 "0" 1 | 1 "110" | 9 | 9', 4): print('   ', x)
    print('if the budget runs out at  | 1 "1110" |, an even arrival halts:')
    ok = True
    for c in ('"0"', '"0" 2', '"0" 4'):
        r = rounds(f'40 | 9 {c} | 1 "1110" | 9 | 9', 10)
        for x in r: print('   ', x)
        ok &= r[-1] == 'HALT'
    return 0 if ok else 1


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'route'
    if cmd == 'route': sys.exit(cmd_route())
    a, b = map(int, sys.argv[2].split('-')) if '-' in sys.argv[2] else (int(sys.argv[2]), int(sys.argv[2]))
    seeds = range(a, b + 1); R = int(sys.argv[3])
    if cmd == 'cuts': sys.exit(cmd_cuts(seeds, R, int(sys.argv[4]) if len(sys.argv) > 4 else 0))
    if cmd == 'words': sys.exit(cmd_words(seeds, R, float(sys.argv[4])))
