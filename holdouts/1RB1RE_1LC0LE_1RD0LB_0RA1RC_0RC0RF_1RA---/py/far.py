"""A negative result: no finite-automaton certificate with a "last k cells" automaton on one side.

Direct FAR (finite automata reduction): fix a deterministic automaton on the left tape, here the one that remembers
the last k cells; the smallest nondeterministic automaton on the rest of the configuration that accepts every
halting configuration and is closed under predecessors is then computed by saturation.  If it rejects the start,
the machine never halts.  For this machine it accepts the start for every k tried, on either side (mirror = the
automaton remembers the first k cells right of the head instead).

usage: python3 far.py [KMAX]      # default 6; k = 8 takes a few minutes
"""
import sys

M = "1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---"


def parse(m):
    T = {}
    for i, row in enumerate(m.split('_')):
        for s in range(2):
            t = row[3 * s:3 * s + 3]
            T[(i, s)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return T


def far(m, delta, mirror=False):
    """delta[q][b]: the left automaton (state 0 = blank tape, delta[0][0] == 0).  True if the start is rejected."""
    T = parse(m); nq = len(delta); NS = 6 * nq + 1; TOP = NS - 1
    sid = lambda q, f: q * 6 + f
    Tr = [[0] * NS for _ in range(2)]            # Tr[b][s]: bitset of successors of s on reading b
    Tr[0][TOP] = Tr[1][TOP] = 1 << TOP
    lefts = []
    for (f, r), t in T.items():
        if t is None:
            for q in range(nq): Tr[r][sid(q, f)] |= 1 << TOP
            continue
        w, d, t2 = t
        if mirror: d = -d
        if d == 1:
            for q in range(nq): Tr[r][sid(q, f)] |= 1 << sid(delta[q][w], t2)
        else:
            lefts.append((f, r, w, t2))

    def img(b, bits):
        out = 0; row = Tr[b]
        while bits:
            low = bits & -bits; out |= row[low.bit_length() - 1]; bits ^= low
        return out
    changed = True
    while changed:
        changed = False
        for (f, r, w, t2) in lefts:
            for q in range(nq):
                for b in range(2):
                    src = Tr[b][sid(q, t2)]
                    if not src: continue
                    add = img(w, src); tgt = sid(delta[q][b], f)
                    if add & ~Tr[r][tgt]:
                        Tr[r][tgt] |= add; changed = True
    acc = 1 << TOP; ch = True
    while ch:
        ch = False
        for s in range(NS):
            if not (acc >> s) & 1 and Tr[0][s] & acc: acc |= 1 << s; ch = True
    return not (acc >> sid(0, 0)) & 1


def last_cells(k):
    n = 1 << k
    return [[(q * 2 + b) % n for b in range(2)] for q in range(n)]


if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    found = False
    for k in range(kmax + 1):
        for mir in (False, True):
            ok = far(M, last_cells(k), mir)
            found |= ok
            print('k = %d, automaton on the %s: %s' % (k, 'right' if mir else 'left', 'CERTIFICATE' if ok else 'no certificate'), flush=True)
    sys.exit(0 if not found else 3)
