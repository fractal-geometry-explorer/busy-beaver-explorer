"""FAR (finite automata reduction) with a given DFA.  far(machine, mirror, dfa) -> (ok, info)
DFA reads the left part of the tape from the far left to the cell left of the head.  The NFA (states (q,s) and TOP)
reads the head cell and the cells right of it; it accepts the configurations that may halt (closed under predecessor).
ok = the blank start configuration is not accepted.

Result for this machine: no certificate with DFA = (parity, last k cells), k <= 6, on either side.
usage: python3 holdouts/1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---/py/far.py"""
import sys, numpy as np

def table(m, mirror=False):
    T = {}
    for s, part in enumerate(m.split('_')):
        for b in range(2):
            t = part[3*b:3*b+3]
            if t[2] == '-': T[(s, b)] = None
            else:
                d = 1 if t[1] == 'R' else -1
                T[(s, b)] = (int(t[0]), -d if mirror else d, ord(t[2]) - 65)
    return T

def far(T, delta, q0=0, maxit=10000, verbose=False):
    n = len(delta); N = 6*n + 1; TOP = N - 1
    Tm = [np.zeros((N, N), dtype=bool) for _ in range(2)]
    for b in range(2): Tm[b][TOP, TOP] = True
    lefts = []
    for s in range(6):
        for b in range(2):
            tr = T[(s, b)]
            for q in range(n):
                if tr is None: Tm[b][q*6+s, TOP] = True
                elif tr[1] == 1: Tm[b][q*6+s, delta[q][tr[0]]*6+tr[2]] = True
            if tr is not None and tr[1] == -1: lefts.append((s, b, tr[0], tr[2]))
    d0 = np.array([delta[q][0] for q in range(n)]); d1 = np.array([delta[q][1] for q in range(n)])
    dd = [d0, d1]
    it = 0
    while True:
        it += 1
        changed = False
        F = [Tm[b].astype(np.float32) for b in range(2)]
        P = {}
        for (s, b, w, s2) in lefts:
            for c in range(2):
                if (c, w) not in P: P[(c, w)] = (F[c] @ F[w]) > 0
                rows = P[(c, w)][np.arange(n)*6 + s2]            # n x N
                tgt = dd[c]*6 + s
                before = Tm[b].sum()
                np.logical_or.at(Tm[b], tgt, rows)
                if Tm[b].sum() != before: changed = True
        # early exit: start accepted?
        if not changed or it >= maxit: break
        if accepts_blank(Tm, q0, TOP): return False, dict(it=it, N=N)
    ok = not accepts_blank(Tm, q0, TOP)
    return ok, dict(it=it, N=N, T=Tm)

def accepts_blank(Tm, q0, TOP):
    seen = np.zeros(Tm[0].shape[0], dtype=bool); seen[q0*6+0] = True
    while True:
        new = seen | (Tm[0][seen].any(axis=0))
        if new[TOP]: return True
        if (new == seen).all(): return False
        seen = new

def dfa_gen(step, start=('Z',)):
    """DFA from a successor function on hashable states; returns (delta, names)."""
    idx = {start: 0}; todo = [start]; delta = []
    i = 0
    while i < len(todo):
        st = todo[i]; i += 1; row = []
        for b in range(2):
            nx = step(st, b)
            if nx not in idx: idx[nx] = len(idx); todo.append(nx)
            row.append(idx[nx])
        delta.append(row)
    return delta, todo

def win_step(k, par=2):
    """state: ('Z',) only zeros; ('S', cells since the first 1) while fewer than k cells; then (parity, last k cells)."""
    def step(st, b):
        if st == ('Z',):
            return ('Z',) if b == 0 else (('S', (1,)) if k > 1 else (1 % par, (1,)[:k]))
        if st[0] == 'S':
            w = st[1] + (b,)
            if len(w) < k: return ('S', w)
            return (len(w) % par, w)
        p, w = st
        return ((p + 1) % par, (w + (b,))[1:])
    return step

def dfa_window(k, par=2):
    return dfa_gen(win_step(k, par))[0]

if __name__ == '__main__':
    M = "1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---"
    for mirror in (True, False):
        for par in (1, 2):
            for k in range(0, 7):
                d = dfa_window(k, par)
                ok, info = far(table(M, mirror), d)
                print('mirror', mirror, 'par', par, 'k', k, 'dfa', len(d), 'ok', ok, 'it', info['it']); sys.stdout.flush()
                if ok: break
