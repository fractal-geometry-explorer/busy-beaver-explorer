"""A pushdown reduction for 1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA (trusted Python; c/pds.c is the fast port).

The left side of the tape is abstracted by a DFA delta (read from the far blank end toward the head, delta(0,0) = 0
so leading blanks are free); the right side is kept exactly, as the stack of a pushdown system whose control states
are (DFA state, machine state).  A right move pushes the written symbol into the DFA (deterministic) and pops the
stack; a left move pops the DFA (every (q', x) with delta(q', x) = q, an over-approximation) and pushes x, b.  The
stack bottom BOT stands for the blank right end.  The reachable configurations of a pushdown system form a regular
set, computed exactly by post* saturation (Schwoon); if no halting transition is reachable, the machine never halts.

Mirroring the machine (`mirror`) puts the DFA on the right side instead.

usage: python3 py/pds.py N [L|R] [N0]   try every DFA with N0..N states on the left (L) or right (R) side
"""
import sys, itertools
TEXT = "1RB0LF_1RC0LB_1RD1RB_1RE1RF_1LA---_0RC1LA"

def parse(text):
    tab = []
    for part in text.split('_'):
        row = []
        for i in (0, 3):
            t = part[i:i+3]
            row.append(None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65))
        tab.append(row)
    return tab

def mirror(tab):
    return [[None if t is None else (t[0], -t[1], t[2]) for t in row] for row in tab]

BOT = 2

def post_star(tab, delta, n, want_witness=False):
    """delta[q][x].  Returns (halt reachable?, number of transitions)."""
    S = len(tab)
    pred = {}
    for q in range(n):
        for x in (0, 1):
            pred.setdefault(delta[q][x], []).append((q, x))
    # rules[(p, g)] = list of (p2, word)
    rules = {}
    for q in range(n):
        for s in range(S):
            p = q * S + s
            for a in (0, 1):
                t = tab[s][a]
                if t is None: continue
                b, d, s2 = t
                gs = [a] + ([BOT] if a == 0 else [])
                for g in gs:
                    tail = [BOT] if g == BOT else []
                    if d == 1:
                        rules.setdefault((p, g), []).append((delta[q][b] * S + s2, tuple(tail)))
                    else:
                        for q2, x in pred.get(q, ()):
                            rules.setdefault((p, g), []).append((q2 * S + s2, (x, b) + tuple(tail)))
    P = n * S
    FIN = P
    nxt = [P + 1]
    trans = set()        # (u, g, v) with g in 0,1,BOT or None (eps)
    out = {}             # (u) -> set of (g, v)
    mids = {}
    work = []
    def add(t):
        if t not in trans:
            trans.add(t); work.append(t); out.setdefault(t[0], set()).add((t[1], t[2]))
    def mid(key):
        if key not in mids:
            mids[key] = nxt[0]; nxt[0] += 1
        return mids[key]
    start = 0 * S + 0
    add((start, BOT, FIN))
    eps_into = {}  # v -> set of u with (u, eps, v): when v gets a g-transition, u gets one too
    while work:
        u, g, v = work.pop()
        if g is None:
            # u -eps-> v: every v -g-> w gives u -g-> w (u is a control state)
            eps_into.setdefault(v, set()).add(u)
            for g2, w in list(out.get(v, ())):
                if g2 is not None: add((u, g2, w))
            continue
        for u0 in list(eps_into.get(u, ())):
            add((u0, g, v))
        if u >= P: continue
        for p2, w in rules.get((u, g), ()):
            if len(w) == 0:
                add((p2, None, v))
            elif len(w) == 1:
                add((p2, w[0], v))
            else:
                # chain p2 -w0-> m1 -w1-> ... -> v ; mids keyed by (p2, w0) etc. (Schwoon: per (p', gamma1))
                cur = p2
                for i in range(len(w) - 1):
                    m = mid((p2,) + w[:i + 1])
                    add((cur, w[i], m)); cur = m
                add((cur, w[-1], v))
    halt = False
    for q in range(n):
        for s in range(S):
            for a in (0, 1):
                if tab[s][a] is None:
                    for g2, w in out.get(q * S + s, ()):
                        if g2 == a or (a == 0 and g2 == BOT): halt = True
    return halt, len(trans)

def dfas(n):
    """DFAs with delta[0][0]=0, all states reachable, canonical BFS numbering."""
    slots = [(q, x) for q in range(n) for x in (0, 1)]
    def rec(i, d, maxs):
        if i == len(slots):
            if maxs == n - 1: yield [row[:] for row in d]
            return
        q, x = slots[i]
        if q > maxs: return
        lo = 0
        for v in range(0, min(maxs + 2, n)):
            if i == 0 and v != 0: continue
            d[q][x] = v
            yield from rec(i + 1, d, max(maxs, v))
    yield from rec(0, [[0, 0] for _ in range(n)], 0)

if __name__ == '__main__':
    tab = parse(TEXT)
    side = sys.argv[2] if len(sys.argv) > 2 else 'L'
    if side == 'R': tab = mirror(tab)
    for n in range(int(sys.argv[3]) if len(sys.argv) > 3 else 1, int(sys.argv[1]) + 1):
        cnt = 0
        for d in dfas(n):
            cnt += 1
            h, nt = post_star(tab, d, n)
            if not h:
                print('NONHALT with', n, d, nt); sys.exit(0)
        print('n', n, 'tried', cnt, flush=True)
