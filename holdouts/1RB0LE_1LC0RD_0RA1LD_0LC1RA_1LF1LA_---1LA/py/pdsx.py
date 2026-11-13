"""Pushdown reduction with any DFA on one side, and its conversion to a TM.CTL certificate (trusted Python).

The left side of the tape is abstracted by a DFA `delta` (read from the far blank end toward the head,
delta[0][0] = 0); the right side is kept exactly as the stack of a pushdown system whose control states are
(DFA state, machine state).  post* saturation (Schwoon) gives the exact set of reachable abstract configurations;
if no halting transition is reachable the machine never halts.  This is the method of
`bb6-1RB0LF_1RC0LB/py/pds.py`, extended to (1) any DFA, not only small enumerated ones, and (2) an export of the
saturated automaton as the closed tape language of `tools/lean/TM/CTL.lean`, checked by `bbtools.ctl.check` here
and by `decide` in Lean.

    left automaton  = the DFA read backwards (outward from the head): edge (delta[q][x], x, q)
    right automaton = the saturated P-automaton without its final state; a state accepts blank when it had a
                      bottom-of-stack edge
    S               = the abstract configurations reachable under the TM.CTL step semantics, the left move
                      always taking the control node (machine state, new DFA state) as its new right state

usage (from this folder):
    python3 pdsx.py try MACHINE L|R FAMILY ARGS...     post* with one DFA family member
    python3 pdsx.py lean MACHINE L|R FAMILY ARGS NS IMPORT > F.lean
FAMILY: mod  K P      last K cells and (number of 1s) mod P
        pos  K P      last K cells and (number of cells) mod P (cells counted from the first 1)
        learn T K     classes of left words seen in a run of T steps, merged by their last K cells (see learn)
"""
import sys, os
from collections import deque
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools import ctl  # noqa: E402

BOT = 2


def parse(text):
    tab = []
    for part in text.split('_'):
        row = []
        for i in (0, 3):
            t = part[i:i + 3]
            row.append(None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65))
        tab.append(row)
    return tab


def mirror_text(text):
    out = []
    for part in text.split('_'):
        g = ''
        for i in (0, 3):
            t = part[i:i + 3]
            g += t if t[0] == '-' else t[0] + ('L' if t[1] == 'R' else 'R') + t[2]
        out.append(g)
    return '_'.join(out)


def post_star(tab, delta):
    """Saturate.  Returns (halts, out, P, FIN): out[u] = set of (g, v), g in 0, 1, BOT; controls u = q*S + s."""
    n = len(delta)
    S = len(tab)
    pred = {}
    for q in range(n):
        for x in (0, 1):
            pred.setdefault(delta[q][x], []).append((q, x))
    P = n * S
    FIN = P
    nxt = [P + 1]
    trans = set()
    out = {}
    mids = {}
    work = []

    def add(t):
        if t not in trans:
            trans.add(t)
            work.append(t)
            out.setdefault(t[0], set()).add((t[1], t[2]))

    def mid(key):
        if key not in mids:
            mids[key] = nxt[0]
            nxt[0] += 1
        return mids[key]

    add((0, BOT, FIN))
    eps_into = {}
    while work:
        u, g, v = work.pop()
        if g is None:
            eps_into.setdefault(v, set()).add(u)
            for g2, w in list(out.get(v, ())):
                if g2 is not None:
                    add((u, g2, w))
            continue
        for u0 in list(eps_into.get(u, ())):
            add((u0, g, v))
        if u >= P:
            continue
        q, s = divmod(u, S)
        a = 0 if g == BOT else g
        t = tab[s][a]
        if t is None:
            continue
        b, d, s2 = t
        tail = (BOT,) if g == BOT else ()
        if d == 1:
            p2 = delta[q][b] * S + s2
            if tail:
                add((p2, BOT, v))
            else:
                add((p2, None, v))
        else:
            for q2, x in pred.get(q, ()):
                p2 = q2 * S + s2
                w = (x, b) + tail
                cur = p2
                for i in range(len(w) - 1):
                    m = mid((p2,) + w[:i + 1])
                    add((cur, w[i], m))
                    cur = m
                add((cur, w[-1], v))
    halts = False
    for q in range(n):
        for s in range(S):
            for a in (0, 1):
                if tab[s][a] is None:
                    for g2, w in out.get(q * S + s, ()):
                        if g2 == a or (a == 0 and g2 == BOT):
                            halts = True
    return halts, out, P, FIN


class A:
    """An automaton in the form `bbtools.ctl` uses (windows are only labels here)."""

    def __init__(self, labels, edges, acc):
        self.windows = labels
        self.edges = sorted(set(edges))
        self.acc = sorted(set(acc))
        self._pops = {}
        for (a, x, b) in self.edges:
            self._pops.setdefault(a, []).append((x, b))

    def pops(self, q):
        return self._pops.get(q, []) + ([(0, q)] if q in self.acc else [])

    def preds(self, q, x):
        return [a for (a, y, b) in self.edges if b == q and y == x]

    def after(self, q, word):
        qs = [q]
        for x in word:
            qs = [q2 for q1 in qs for (y, q2) in self.pops(q1) if y == x]
        return qs

    def blank_only(self):
        B = set(range(len(self.windows)))
        changed = True
        while changed:
            changed = False
            for (q1, x, q2) in self.edges:
                if q1 in B and (x == 1 or q2 not in B):
                    B.discard(q1)
                    changed = True
        return sorted(B)


def certificate(text, delta):
    """(AL, AR, S) for TM.CTL, or None if post* reaches a halt.  States renumbered densely."""
    tab = parse(text)
    halts, out, P, FIN = post_star(tab, delta)
    if halts:
        return None
    Sn = len(tab)
    n = len(delta)
    # right automaton: drop FIN; BOT edges become acceptance
    used = set(range(P)) | {v for u in out for (g, v) in out[u] if v != FIN} | set(out)
    used.discard(FIN)
    ids = {u: i for i, u in enumerate(sorted(used))}
    redges, racc = [], []
    for u in out:
        for g, v in out[u]:
            if g == BOT:
                racc.append(ids[u])
            else:
                redges.append((ids[u], g, ids[v]))
    def lab(u):
        if u < P:
            q, s = divmod(u, Sn)
            return f"{chr(65 + s)}{q}"
        return f"m{u}"
    AR = A([lab(u) for u in sorted(used)], redges, racc)
    AL = A([f"q{q}" for q in range(n)], [(delta[q][x], x, q) for q in range(n) for x in (0, 1)], [0])
    start = (0, 0, ids[0])
    seen = {start}
    todo = deque([start])
    while todo:
        s, ql, qr = todo.popleft()
        for x, qr2 in AR.pops(qr):
            t = tab[s][x]
            if t is None:
                return None
            w, d, s2 = t
            if d == 1:
                nxts = [(s2, delta[ql][w], qr2)]
            else:
                nxts = [(s2, ql2, ids[ql2 * Sn + s2]) for y, ql2 in AL.pops(ql)]
            for c in nxts:
                if c not in seen:
                    seen.add(c)
                    todo.append(c)
    S = sorted(seen)
    # drop unused right states? keep all (simple); check closure exactly as Lean
    if not ctl.check(text, AL, AR, S):
        raise RuntimeError("closure check failed")
    if ctl.halting(text, AR, S):
        raise RuntimeError("halting configuration in set")
    return AL, AR, S


def minimize(delta):
    """Reachable part of a DFA, Moore-minimized; state 0 first."""
    n = len(delta)
    reach = [0]
    seen = {0}
    for q in reach:
        for x in (0, 1):
            if delta[q][x] not in seen:
                seen.add(delta[q][x])
                reach.append(delta[q][x])
    return [[reach.index(delta[q][x]) for x in (0, 1)] for q in reach]


def dfa_mod(K, P, count_pos=False):
    """States (last K cells, counter mod P) once a 1 has been read, and one blank state before that.  The counter
    counts the 1s (or, with count_pos, the cells from the first 1 on) modulo P."""
    states = {}
    order = []

    def get(st):
        if st not in states:
            states[st] = len(order)
            order.append(st)
        return states[st]
    get(None)
    delta = []
    i = 0
    while i < len(order):
        st = order[i]
        row = []
        for x in (0, 1):
            if st is None:
                row.append(0 if x == 0 else get((((0,) * K + (1,))[1:] if K else (), 1 % P)))
                continue
            w, c = st
            w2 = (w + (x,))[1:] if K else ()
            c2 = (c + 1) % P if count_pos else (c + x) % P
            row.append(get((w2, c2)))
        delta.append(row)
        i += 1
    return delta


def runs_left(text, T, mirror=False):
    """Left words (far end to head) at every step of a run of T steps."""
    tab = parse(mirror_text(text) if mirror else text)
    tape = {}
    pos = 0
    st = 0
    lo = 0
    words = set()
    for _ in range(T):
        y = tape.get(pos, 0)
        t = tab[st][y]
        if t is None:
            break
        w, d, s2 = t
        tape[pos] = w
        pos += d
        st = s2
        lo = min(lo, pos)
        words.add(tuple(tape.get(i, 0) for i in range(lo, pos)))
    return words


def dfa_learn(words, K):
    """A DFA from sampled left words: states are the last-K-cell windows of prefixes seen, plus a sink-free
    completion (unseen windows go to the canonical window).  Equivalent to dfa_mod(K, 1) restricted; kept
    for experiments."""
    return dfa_mod(K, 1)


def family(name, args):
    if name == "mod":
        return dfa_mod(int(args[0]), int(args[1]))
    if name == "pos":
        return dfa_mod(int(args[0]), int(args[1]), count_pos=True)
    if name == "table":   # explicit: "00,12,..." rows
        return [[int(c) for c in row] for row in args[0].split(",")]
    raise ValueError(name)


def main(argv):
    cmd, text, side, fam = argv[:4]
    m = mirror_text(text) if side == "R" else text
    if cmd == "try":
        delta = minimize(family(fam, argv[4:]))
        h, out, P, FIN = post_star(parse(m), delta)
        print(f"{len(delta)} DFA states: {'HALT reachable' if h else 'NO HALT'}")
        if not h:
            AL, AR, S = certificate(m, delta)
            print(f"certificate: left {len(AL.windows)}, right {len(AR.windows)} states, {len(S)} configs; closed")
    elif cmd == "lean":
        nargs = {"mod": 2, "pos": 2, "table": 1}[fam]
        delta = minimize(family(fam, argv[4:4 + nargs]))
        ns, imp = argv[4 + nargs:6 + nargs]
        AL, AR, S = certificate(m, delta)
        sys.stdout.write(ctl.lean_data(AL, AR, S, ns))


if __name__ == "__main__":
    main(sys.argv[1:])
