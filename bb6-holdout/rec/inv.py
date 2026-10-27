"""A regular invariant for 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE, and an exact closure check.

Configurations are written as strings over  < > 0 1 e A :
  <  and  >  stand for the blank tape on each side (zeros next to them are blank tape too),
  e  is the head in state E reading a 0,
  A  is the head in state A reading a packet '1 1'; the packet's two cells are left out of the string
     (so A sits between cells, and CARRY  1 0 A -> A 1 0  leaves the string's cells unchanged).

The invariant INV is defined by a finite-state scanner (below), so it is a regular language. The checks:
  closure   for every proven theorem  L u R -> L v R  and every value of its variables:
            x u y in INV  implies  x v y in INV, for all strings x, y.
  dispatch  every string in INV (with 4 blank zeros written at each end) contains the start of some theorem.
  start     the configuration reached from the blank tape after 17 steps is in INV.
Both checks are exact: they work on the minimal automaton, and the variables are handled by the eventual
periodicity of  w^n  acting on the automaton's states, so they cover all values, not just small ones.
Together they prove that the machine never halts: every theorem takes at least one step and none halts.
"""
import itertools, sys
from collections import deque
from symtm import tokens, Lin, Rep, Ctx, Blank
import proofs

SIG = ("<", ">", "0", "1", "e", "A")

# ---------------------------------------------------------------- the scanner
# runs are recorded as (symbol, length, where) with where = L (left of the head), H (contains the head), R (right)
HN = 4                     # how many recent runs/head tokens the scanner remembers for the adjacency rules

# Adjacency rule. A mark is a run of length >= 2 (W wall, G gap, M marker, B block; the head's 0000 counts as G
# on its left side and as W on its right side). Between two neighbouring marks lie s single cells (stripes).
#   marks of different symbols (s even):  s = 0 only for  M G  and  G M
#   marks of the same symbol   (s odd):   s = 1 only for  G 1 W
# The packet (A) is transparent.
NAME = {(0, 2): "W", (0, 3): "G", (1, 2): "M", (1, 3): "B"}
ALLOW0 = {("M", "G"), ("G", "M")}
ALLOW1 = {("G", "W")}
USE_ADJ = True


def mark(tok, side):
    if tok[0] == 0 and tok[1] == 4: return "G" if side == "left" else "W"
    return NAME.get(tok[:2])


def x_ok(hist):
    if not USE_ADJ: return True
    h = [t for t in hist if t != ("A",)]
    if not h or len(h[-1]) < 3 or h[-1][1] < 2: return True
    y = mark(h[-1], "left")
    if len(h) >= 2 and h[-2][1] >= 2:
        return (mark(h[-2], "right"), y) in ALLOW0
    if len(h) >= 3 and h[-2][1] == 1 and h[-3][1] >= 2:
        return (mark(h[-3], "right"), y) in ALLOW1
    return True


def push(hist, tok):
    h = (hist + (tok,))[-HN:] if HN else ()
    full = hist + (tok,)
    return h if x_ok(full[-max(HN, 1):]) else None


def close1(rl, rw, hist):
    if rl == 3 and rw in ("L", "H"): return None          # J: no block left of the head
    return push(hist, (1, rl, rw))


def close0(rl, rw, inE, hist):
    """A run of zeros ended by a 1."""
    if inE:
        if rl not in (3, 4): return None
        return push(hist, (0, rl, "H"))
    if rl > 3: return None
    if rl == 3 and rw == "R": return None                  # K: no gap right of the head
    return push(hist, (0, rl, rw))


def delta(s, c):
    if s is None: return None
    st, rs, rl, rw, head, inE, need1, hist = s
    if st == "S":
        return ("L", None, 0, None, None, False, False, ()) if c == "<" else None
    if st == "Z": return None
    if need1 and c != "1": return None
    if st == "L":                                          # left blank, no cell of the content yet
        if c == "0": return s
        if c == "1": return ("B", 1, 1, "R" if head else "L", head, False, False, hist)
        if c == "A" and not head:
            h = push(hist, ("A",))
            return None if h is None else ("L", None, 0, None, "A", False, True, h)
        return None
    # st == "B"
    if c == "1":
        if rs == 1:
            return None if rl >= 3 else ("B", 1, rl + 1, rw, head, False, False, hist)
        if rs == 0:
            h = close0(rl, rw, inE, hist)
            if h is None: return None
        else:
            h = hist
        return ("B", 1, 1, "R" if head else "L", head, False, False, h)
    if c == "0":
        if rs == 0: return ("B", 0, min(rl + 1, 5), rw, head, inE, False, hist)
        h = close1(rl, rw, hist)
        if h is None: return None
        return ("B", 0, 1, "R" if head else "L", head, False, False, h)
    if c == "e":
        if head or rs != 0 or rl != 2: return None
        return ("B", 0, 3, "H", "e", True, False, hist)
    if c == "A":
        if head: return None
        if rs == 1:
            return ("B", 1, rl, "H", "A", False, True, hist)
        h = close0(rl, rw, inE, hist)                      # the next cell is a 1, so this zero run ends here
        if h is None: return None
        h = push(h, ("A",))
        if h is None: return None
        return ("B", None, 0, None, "A", False, True, h)
    if c == ">":
        if not head or need1: return None
        if rs == 1:
            h = close1(rl, rw, hist)
        elif inE:
            h = push(hist, (0, 3, "H"))                     # the head's gap at the right end
        else:
            h = hist                                        # trailing zeros are blank tape
        if h is None: return None
        return ("Z", None, 0, None, head, False, False, ())
    return None


def build():
    start = ("S", None, 0, None, None, False, False, ())
    idx = {start: 0}; states = [start]; trans = []
    q = deque([start])
    while q:
        s = q.popleft(); row = []
        for c in SIG:
            t = delta(s, c)
            if t not in idx:
                idx[t] = len(states); states.append(t); q.append(t)
            row.append(idx[t])
        trans.append((idx[s], row))
    n = len(states)
    T = [None] * n
    for i, row in trans: T[i] = row
    for i in range(n):
        if T[i] is None: T[i] = [idx[None]] * len(SIG)     # the dead state loops
    acc = [s is not None and s[0] == "Z" for s in states]
    return minimize(T, acc, 0)


def minimize(T, acc, start):
    """Moore partition refinement on the reachable part; returns (T, acc, start)."""
    n = len(T)
    part = [1 if a else 0 for a in acc]
    while True:
        sig = {}
        new = []
        for i in range(n):
            key = (part[i],) + tuple(part[T[i][c]] for c in range(len(SIG)))
            new.append(sig.setdefault(key, len(sig)))
        if len(sig) == len(set(part)): part = new; break
        part = new
    m = max(part) + 1
    T2 = [None] * m; acc2 = [False] * m
    for i in range(n):
        T2[part[i]] = [part[T[i][c]] for c in range(len(SIG))]; acc2[part[i]] = acc[i]
    return T2, acc2, part[start]


class DFA:
    def __init__(self):
        self.T, self.acc, self.start = build()
        self.n = len(self.T)
        self.ci = {c: i for i, c in enumerate(SIG)}
        self._bad = None

    def run(self, s, p=None):
        p = self.start if p is None else p
        for c in s: p = self.T[p][self.ci[c]]
        return p

    def fn(self, word):
        """The map state -> state for reading word."""
        return tuple(self.run(word, p) for p in range(self.n))

    def accepts(self, s): return self.acc[self.run(s)]

    def bad_pairs(self):
        """Pairs (a, b) where some suffix is accepted from a but not from b."""
        if self._bad is not None: return self._bad
        n, T = self.n, self.T
        pred = {}
        bad = set()
        q = deque()
        for a in range(n):
            for b in range(n):
                if self.acc[a] and not self.acc[b]: bad.add((a, b)); q.append((a, b))
        # predecessor lists per symbol
        P = [[[] for _ in range(n)] for _ in SIG]
        for p in range(n):
            for c in range(len(SIG)): P[c][T[p][c]].append(p)
        while q:
            a, b = q.popleft()
            for c in range(len(SIG)):
                for a0 in P[c][a]:
                    for b0 in P[c][b]:
                        if (a0, b0) not in bad: bad.add((a0, b0)); q.append((a0, b0))
        self._bad = bad
        return bad

    def shortest_to(self):
        """A shortest string reaching each state from the start."""
        best = {self.start: ""}; q = deque([self.start])
        while q:
            p = q.popleft()
            for c in SIG:
                t = self.T[p][self.ci[c]]
                if t not in best: best[t] = best[p] + c; q.append(t)
        return best

    def witness_suffix(self, a, b):
        """A shortest y accepted from a but not from b."""
        seen = {(a, b): ""}; q = deque([(a, b)])
        while q:
            x, z = q.popleft()
            if self.acc[x] and not self.acc[z]: return seen[(x, z)]
            for c in SIG:
                k = self.ci[c]; nx = (self.T[x][k], self.T[z][k])
                if nx not in seen: seen[nx] = seen[(x, z)] + c; q.append(nx)
        return None


# ---------------------------------------------------------------- theorems as string rules
def side_items(s, v):
    out = []
    parts = s.split(" | ")
    for part in parts:
        if part.strip() == "0^inf": out.append("BLANK"); continue
        out.extend(tokens(part, **v))
    return out


def to_segments(left, state, right, varmap, is_start):
    """Segments of the string form: ('lit', str) or ('rep', word, var, const)."""
    L = side_items(left, varmap); R = side_items(right, varmap)
    segs = []
    def lit(ch):
        if segs and segs[-1][0] == "lit": segs[-1] = ("lit", segs[-1][1] + ch)
        else: segs.append(("lit", ch))
    def item(t, where):
        if t == "BLANK":
            if where == "left":
                lit("<")
                if is_start: segs.append(("rep", "0", "nL", 0))
            else:
                if is_start: segs.append(("rep", "0", "nR", 0))
                lit(">")
        elif isinstance(t, Ctx):
            assert t.name in ("L", "R")
        elif isinstance(t, Rep):
            n = t.n; word = "".join(map(str, t.word))
            if n.is_const():
                lit(word * n.k)
            else:
                (var, a), = n.c.items(); assert a == 1
                segs.append(("rep", word, var, n.k))
        else:
            lit(str(t))
    for t in L: item(t, "left")
    R = list(R)
    if state == "E":
        assert R[0] == 0; R = R[1:]; lit("e")
    elif state == "A":
        assert R[0] == 1 and R[1] == 1; R = R[2:]; lit("A")
    else:
        raise ValueError(state)
    for t in R: item(t, "right")
    return segs


def rules():
    out = []
    for t in proofs.THEOREMS:
        if t["halt"]: continue
        s, e = t["start"], t["end"]
        varmap = {k: Lin(x) if not isinstance(x, Lin) else x for k, x in {**s[3], **e[3]}.items()}
        # start patterns use names like m2 = m + 2; give each name its own Lin from the theorem
        vs = {k: x for k, x in s[3].items()}; ve = {k: x for k, x in e[3].items()}
        u = to_segments(s[0], s[1], s[2], vs, True)
        v = to_segments(e[0], e[1], e[2], ve, False)
        out.append((t["name"], u, v))
    out.append(("CARRY", [("lit", "10A")], [("lit", "A10")]))
    return out


def seg_str(segs):
    return " ".join(x[1] if x[0] == "lit" else f"({x[1]})^{x[2]}{'+' + str(x[3]) if x[3] else ''}" for x in segs)


# ---------------------------------------------------------------- the closure check
def compose(f, g):            # first f, then g
    return tuple(g[x] for x in f)


def power_reps(D, words):
    """Representatives e = 0, 1, ... of the eventually periodic sequence of tuples (f_w^e for w in words).
    Every e >= 0 gives one of the returned tuples."""
    base = [D.fn(w) for w in words]
    ident = tuple(range(D.n))
    cur = tuple(ident for _ in words); seen = {}
    reps = []
    e = 0
    while cur not in seen:
        seen[cur] = e; reps.append((e, cur))
        cur = tuple(compose(c, b) for c, b in zip(cur, base)); e += 1
    return reps


def eval_side(D, segs, pw):
    """The state map for a side, given pw[var][word] = f_word^value."""
    f = tuple(range(D.n))
    for s in segs:
        if s[0] == "lit":
            f = compose(f, D.fn(s[1]))
        else:
            _, word, var, c = s
            f = compose(f, pw[var][word])
            for _ in range(c): f = compose(f, D.fn(word))
    return f


def closure(D, verbose=True, max_examples=3):
    bad = D.bad_pairs()
    reach = D.shortest_to()
    live = [p for p in reach]
    results = {}
    for name, u, v in rules():
        vars_ = {}
        for s in u + v:
            if s[0] == "rep": vars_.setdefault(s[2], set()).add(s[1])
        reps = {var: [(e, dict(zip(sorted(ws), tup))) for e, tup in power_reps(D, sorted(ws))] for var, ws in vars_.items()}
        names = sorted(reps)
        fails = []
        count = 0
        for combo in itertools.product(*[reps[n] for n in names]):
            pw = {n: c[1] for n, c in zip(names, combo)}
            vals = {n: c[0] for n, c in zip(names, combo)}
            fu = eval_side(D, u, pw); fv = eval_side(D, v, pw)
            for p in live:
                count += 1
                if (fu[p], fv[p]) in bad:
                    fails.append((p, vals, fu[p], fv[p]))
        results[name] = fails
        if verbose:
            print(f"{name:24s} {'closed' if not fails else str(len(fails)) + ' failures'}"
                  f"   (values per variable: {', '.join(f'{n}<{len(reps[n])}' for n in names) or '-'})", flush=True)
            for p, vals, a, b in fails[:max_examples]:
                x = reach[p]; y = D.witness_suffix(a, b)
                print("    x =", x, " vars", vals, " y =", y)
                print("      start", x, "|", inst(u, vals), "|", y)
                print("      end  ", x, "|", inst(v, vals), "|", y)
    return results


def inst(segs, vals):
    out = ""
    for s in segs:
        if s[0] == "lit": out += s[1]
        else: out += s[1] * (vals[s[2]] + s[3])
    return out


# ---------------------------------------------------------------- dispatch: every configuration in INV matches a rule
class NFA:
    def __init__(self):
        self.eps = {}; self.tr = {}; self.final = set(); self.n = 0
    def new(self):
        self.n += 1; return self.n - 1
    def add(self, a, c, b): self.tr.setdefault((a, c), set()).add(b)
    def addeps(self, a, b): self.eps.setdefault(a, set()).add(b)
    def closure(self, S):
        S = set(S); st = list(S)
        while st:
            a = st.pop()
            for b in self.eps.get(a, ()):
                if b not in S: S.add(b); st.append(b)
        return frozenset(S)
    def move(self, S, c):
        out = set()
        for a in S: out |= self.tr.get((a, c), set())
        return self.closure(out)


def pattern_nfa(patterns):
    N = NFA(); s0 = N.new()
    for c in SIG: N.add(s0, c, s0)
    for name, segs in patterns:
        cur = N.new(); N.addeps(s0, cur)
        for s in segs:
            if s[0] == "lit":
                for ch in s[1]:
                    nx = N.new(); N.add(cur, ch, nx); cur = nx
            else:
                _, word, var, c = s
                for _ in range(c):
                    for ch in word:
                        nx = N.new(); N.add(cur, ch, nx); cur = nx
                loop = cur
                for i, ch in enumerate(word):
                    nx = loop if i == len(word) - 1 else N.new()
                    N.add(cur, ch, nx); cur = nx
                cur = loop
        N.final.add(cur)
    return N, s0


def dispatch(D, pad=4):
    """Search for a string '<' 0^pad ... 0^pad '>' in INV containing no rule's start pattern."""
    N, s0 = pattern_nfa([(n, u) for n, u, v in rules()])
    # the padding: a small automaton counting the forced zeros at both ends
    # pad state: ('lead', k) after '<' and k zeros (k <= pad); 'mid'; ('trail', k) = last k symbols were zeros
    def padstep(ps, c):
        if ps == "start": return ("lead", 0) if c == "<" else None
        if ps[0] == "lead":
            if ps[1] < pad: return ("lead", ps[1] + 1) if c == "0" else None
            ps = ("trail", 0)
        if ps[0] == "trail":
            if c == ">": return "end" if ps[1] >= pad else None
            return ("trail", min(ps[1] + 1, pad)) if c == "0" else ("trail", 0)
        return None
    startS = N.closure({s0})
    init = (D.start, "start", startS, False)
    seen = {init: None}; q = deque([init])
    while q:
        node = q.popleft()
        p, ps, S, matched = node
        if D.acc[p] and ps == "end":
            if not matched:
                # rebuild the string
                out = []; k = node
                while seen[k] is not None: k, ch = seen[k]; out.append(ch)
                return "".join(reversed(out))
            continue
        for c in SIG:
            p2 = D.T[p][D.ci[c]]
            if not D.alive[p2]: continue
            ps2 = padstep(ps, c)
            if ps2 is None: continue
            if matched: S2, m2 = frozenset(), True
            else:
                S2 = N.move(S, c); m2 = bool(S2 & N.final)
                if m2: S2 = frozenset()
            nd = (p2, ps2, S2, m2)
            if nd not in seen: seen[nd] = (node, c); q.append(nd)
    return None


def add_alive(D):
    """States from which an accepting state can be reached."""
    alive = [False] * D.n
    for i in range(D.n): alive[i] = D.acc[i]
    changed = True
    while changed:
        changed = False
        for i in range(D.n):
            if not alive[i] and any(alive[t] for t in D.T[i]): alive[i] = True; changed = True
    D.alive = alive


# ---------------------------------------------------------------- configurations from the certified run
def config_string(cfg):
    """The string form of a symtm Config in state E (reading 0) or A (reading 1 1); Rep tokens kept as (word, n)."""
    seq = []
    def emit(t):
        if isinstance(t, Blank): return
        if isinstance(t, Rep): seq.append(("".join(map(str, t.word)), t.n.k)); return
        seq.append(str(t))
    left = list(cfg.left); right = list(cfg.right)
    for t in left: emit(t)
    from symtm import _unroll_front
    r = list(right)
    if cfg.state == "E":
        assert _unroll_front(r) == 0; r.pop(0); seq.append("e")
    elif cfg.state == "A":
        assert _unroll_front(r) == 1; r.pop(0); assert _unroll_front(r) == 1; r.pop(0); seq.append("A")
    for t in r: emit(t)
    return seq


def run_tokens(D, seq):
    """Run the automaton over '<' seq '>' where items are symbols or (word, count) repeats."""
    p = D.run("<0000")
    for t in seq:
        if isinstance(t, tuple):
            word, n = t
            # orbit of p under the word, with cycle detection
            orbit = {}; k = 0
            while k < n:
                if p in orbit:
                    cyc = k - orbit[p]; rem = (n - k) % cyc
                    for _ in range(rem): p = D.run(word, p)
                    break
                orbit[p] = k; p = D.run(word, p); k += 1
        else:
            p = D.run(t, p)
    p = D.run("0000>", p)
    return D.acc[p]


def check_run(D, rounds=60):
    """Every configuration the certified simulation passes through (first `rounds` rounds) must be in INV."""
    import casesim
    from symtm import Config, try_lemma, step
    cfg = Config([Blank()], "A", [Blank()])
    while not proofs.is_pass_position(cfg):
        if not try_lemma(cfg): step(cfg)
    first = config_string(cfg)
    ok = run_tokens(D, first)
    n_cfg = 1; bad = None
    phase = "gap"; r = 0
    while r < rounds:
        if phase == "gap":
            cfg = casesim.gap_phase(cfg)
            phase = "gap" if proofs.is_pass_position(cfg) else "packet"
        else:
            cfg, kind = casesim.packet_phase(cfg)
            if kind == "round": r += 1
            phase = "packet" if kind == "packet" else "gap"
        n_cfg += 1
        if not run_tokens(D, config_string(cfg)):
            bad = cfg; break
    return ok, first, n_cfg, bad


if __name__ == "__main__":
    D = DFA(); add_alive(D)
    print("automaton states:", D.n)
    ok, first, n_cfg, bad = check_run(D, int(sys.argv[1]) if len(sys.argv) > 1 else 40)
    print("start configuration in INV:", ok, " configurations of the run checked:", n_cfg, " first outside INV:", bad)
    closure(D)
    w = dispatch(D)
    print("dispatch:", "every configuration matches a theorem" if w is None else "UNMATCHED " + w)
