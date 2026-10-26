"""A learned regular invariant (closed tape language) for 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE,
with an exact check that it is closed under the proven theorems and that every configuration in it is covered.

String form of a configuration (alphabet  < > 0 1 e A):
  < and >  the blank tape on each side (0s next to them are blank tape too),
  e        the head in state E, reading a 0,
  A        the head in state A, reading a packet '1 1'; the packet's two cells are left out of the string.

The tape is read as a sequence of tokens: the two ends < >, the marks (runs of length >= 2: W wall 00, G gap 000,
M marker 11, B block 111), the head (G* = the head's gap, GW* = the head's gap touching a wall, MA = a marker the
packet sits inside, A = the packet between runs). Between two neighbouring tokens there are s single cells.
A token is labelled L or R by its side of the head.

INV = strings whose runs are all of length <= 3 (except GW*), with the head as described, and in which every window
of three neighbouring tokens (with the two separations, capped at CAP) belongs to a finite set P.
P is read off configurations of the certified run; the checks below decide, exactly, whether INV is closed under
the proven theorems and whether every configuration in INV is the start of some theorem.
"""
import itertools, sys, pickle, os
from collections import deque
from symtm import Lin, Rep, Ctx, Blank, Config, try_lemma, step, count_pairs, _unroll_front
import proofs
from inv import rules, inst, seg_str, NFA, pattern_nfa, config_string

SIG = ("<", ">", "0", "1", "e", "A")
CAP = 6
KWIN = 3

NAME = {(0, 2): "W", (0, 3): "G", (1, 2): "M", (1, 3): "B"}


class Scanner:
    """Deterministic scanner. With P = None it records windows (learning); otherwise it rejects unknown ones.
    A window is K neighbouring tokens with the K-1 separations between them."""

    def __init__(self, P=None, K=None):
        self.P = P
        self.K = K or KWIN
        self.seen = set()

    def start(self):
        # (stage, run_sym, run_len, run_flag, head, need1, hist, scur); hist = (t, s, t, s, ..., t) of <= K-1 tokens
        return ("S", None, 0, None, None, False, (), 0)

    def emit(self, s, tok):
        st, rs, rl, rf, head, need1, hist, sc = s
        w = (hist + (sc, tok)) if hist else (tok,)
        full = 2 * self.K - 1
        if len(w) == full or tok == ">":
            ww = (None,) * (full - len(w)) + w              # a short tape is one window, padded on the left
            if self.P is None: self.seen.add(ww)
            elif ww not in self.P: return None
        nh = w[-(full - 2):] if self.K > 1 else ()
        return (st, rs, rl, rf, head, need1, nh, 0)

    def single(self, s):
        n = s[7] + 1                      # separations: exact below CAP, then CAP..CAP+3 by residue mod 4
        if n >= CAP + 4: n -= 4
        return s[:7] + (n,)

    def side(self, head): return "R" if head else "L"

    def close1(self, s):
        st, rs, rl, rf, head, need1, hist, sc = s
        if rl == 1: return self.single(s)
        if rl == 3 and rf in ("L", "A"): return None            # J: no block left of the head
        name = NAME[(1, rl)]
        tok = name + "A" if rf == "A" else name + "." + rf
        return self.emit(s, tok)

    def close0(self, s):
        st, rs, rl, rf, head, need1, hist, sc = s
        if rf == "e":
            if rl == 3: return self.emit(s, "G*")
            if rl == 4: return self.emit(s, "GW*")
            return None
        if rl > 3: return None
        if rl == 3 and rf == "R": return None                    # K: no gap right of the head
        if rl == 1: return self.single(s)
        return self.emit(s, NAME[(0, rl)] + "." + rf)

    def delta(self, s, c):
        if s is None: return None
        st, rs, rl, rf, head, need1, hist, sc = s
        if st == "S":
            if c != "<": return None
            return self.emit(("L", None, 0, None, None, False, (), 0), "<")
        if st == "Z": return None
        if need1 and c != "1": return None
        if st == "L":
            if c == "0": return s
            if c == "1": return ("B", 1, 1, self.side(head), head, False, hist, sc)
            if c == "A" and not head:
                s = self.emit(s, "A")
                if s is None: return None
                return ("L", None, 0, None, "A", True) + s[6:]
            return None
        if c == "1":
            if rs == 1:
                if rl >= 3: return None
                return ("B", 1, rl + 1, rf, head, False, hist, sc)
            if rs == 0:
                s = self.close0(s)
                if s is None: return None
            return ("B", 1, 1, self.side(head), head, False) + s[6:]
        if c == "0":
            if rs == 0: return ("B", 0, min(rl + 1, 5), rf, head, False, hist, sc)
            s = self.close1(s)
            if s is None: return None
            return ("B", 0, 1, self.side(head), head, False) + s[6:]
        if c == "e":
            if head or rs != 0 or rl != 2: return None
            return ("B", 0, 3, "e", "e", False, hist, sc)
        if c == "A":
            if head: return None
            if rs == 1:
                return ("B", 1, rl, "A", "A", True, hist, sc)
            s = self.close0(s)
            if s is None: return None
            s = self.emit(s, "A")
            if s is None: return None
            return ("B", None, 0, None, "A", True) + s[6:]
        if c == ">":
            if not head or need1: return None
            if rs == 1:
                s = self.close1(s)
            elif rf == "e":
                s = self.emit(s, "G*")
            if s is None: return None
            s = (s[0], None, 0, None) + s[4:]
            s = self.emit(s, ">")
            if s is None: return None
            return ("Z", None, 0, None, None, False, (), 0)
        return None


# ---------------------------------------------------------------- automaton
class DFA:
    def __init__(self, scanner):
        sc = scanner
        start = sc.start()
        idx = {start: 0}; states = [start]; rows = {}
        q = deque([start])
        while q:
            s = q.popleft(); row = []
            for c in SIG:
                t = sc.delta(s, c)
                if t not in idx:
                    idx[t] = len(states); states.append(t); q.append(t)
                row.append(idx[t])
            rows[idx[s]] = row
        n = len(states)
        T = [rows.get(i) or [idx[None]] * len(SIG) for i in range(n)]
        acc = [s is not None and s[0] == "Z" for s in states]
        self.raw_states = n
        self.T, self.acc, self.start = minimize(T, acc, 0)
        self.n = len(self.T)
        self.ci = {c: i for i, c in enumerate(SIG)}
        self.alive = self._alive()
        self._bad = None

    def _alive(self):
        alive = list(self.acc); changed = True
        while changed:
            changed = False
            for i in range(self.n):
                if not alive[i] and any(alive[t] for t in self.T[i]): alive[i] = True; changed = True
        return alive

    def run(self, s, p=None):
        p = self.start if p is None else p
        for c in s: p = self.T[p][self.ci[c]]
        return p

    def fn(self, word): return tuple(self.run(word, p) for p in range(self.n))
    def accepts(self, s): return self.acc[self.run(s)]

    def bad_pairs(self):
        if self._bad is not None: return self._bad
        n, T = self.n, self.T
        P = [[[] for _ in range(n)] for _ in SIG]
        for p in range(n):
            for c in range(len(SIG)): P[c][T[p][c]].append(p)
        bad = set(); q = deque()
        for a in range(n):
            if self.acc[a]:
                for b in range(n):
                    if not self.acc[b]: bad.add((a, b)); q.append((a, b))
        while q:
            a, b = q.popleft()
            for c in range(len(SIG)):
                for a0 in P[c][a]:
                    for b0 in P[c][b]:
                        if (a0, b0) not in bad: bad.add((a0, b0)); q.append((a0, b0))
        self._bad = bad
        return bad

    def shortest_to(self):
        best = {self.start: ""}; q = deque([self.start])
        while q:
            p = q.popleft()
            for c in SIG:
                t = self.T[p][self.ci[c]]
                if t not in best: best[t] = best[p] + c; q.append(t)
        return best

    def witness_suffix(self, a, b):
        seen = {(a, b): ""}; q = deque([(a, b)])
        while q:
            x, z = q.popleft()
            if self.acc[x] and not self.acc[z]: return seen[(x, z)]
            for c in SIG:
                k = self.ci[c]; nx = (self.T[x][k], self.T[z][k])
                if nx not in seen: seen[nx] = seen[(x, z)] + c; q.append(nx)
        return None


def minimize(T, acc, start):
    n = len(T)
    part = [1 if a else 0 for a in acc]
    nparts = len(set(part))
    while True:
        sig = {}; new = []
        for i in range(n):
            key = (part[i],) + tuple(part[T[i][c]] for c in range(len(SIG)))
            new.append(sig.setdefault(key, len(sig)))
        if len(sig) == nparts: part = new; break
        part = new; nparts = len(sig)
    m = max(part) + 1
    T2 = [None] * m; acc2 = [False] * m
    for i in range(n):
        T2[part[i]] = [part[T[i][c]] for c in range(len(SIG))]; acc2[part[i]] = acc[i]
    return T2, acc2, part[start]


# ---------------------------------------------------------------- closure and dispatch
def compose(f, g): return tuple(g[x] for x in f)


def power_reps(D, words):
    base = [D.fn(w) for w in words]
    ident = tuple(range(D.n))
    cur = tuple(ident for _ in words); seen = {}; reps = []; e = 0
    while cur not in seen:
        seen[cur] = e; reps.append((e, cur))
        cur = tuple(compose(c, b) for c, b in zip(cur, base)); e += 1
    return reps


def eval_side(D, segs, pw):
    f = tuple(range(D.n))
    for s in segs:
        if s[0] == "lit": f = compose(f, D.fn(s[1]))
        else:
            _, word, var, c = s
            f = compose(f, pw[var][word])
            for _ in range(c): f = compose(f, D.fn(word))
    return f


def closure(D, verbose=True, max_examples=2):
    bad = D.bad_pairs(); reach = D.shortest_to()
    live = [p for p in reach if D.alive[p]]
    out = {}
    for name, u, v in rules():
        vars_ = {}
        for s in u + v:
            if s[0] == "rep": vars_.setdefault(s[2], set()).add(s[1])
        reps = {var: [(e, dict(zip(sorted(ws), tup))) for e, tup in power_reps(D, sorted(ws))] for var, ws in vars_.items()}
        names = sorted(reps); fails = []
        for combo in itertools.product(*[reps[n] for n in names]):
            pw = {n: c[1] for n, c in zip(names, combo)}; vals = {n: c[0] for n, c in zip(names, combo)}
            fu = eval_side(D, u, pw); fv = eval_side(D, v, pw)
            for p in live:
                if (fu[p], fv[p]) in bad: fails.append((p, vals, fu[p], fv[p]))
        out[name] = (fails, {n: len(reps[n]) for n in names})
        if verbose:
            print(f"  {name:24s} {'closed' if not fails else str(len(fails)) + ' failures'}"
                  f"   (all values covered by: {', '.join(f'{n} < {len(reps[n])}' for n in names) or '-'})", flush=True)
            for p, vals, a, b in fails[:max_examples]:
                x = reach[p]; y = D.witness_suffix(a, b)
                print("      start", x, "|", inst(u, vals), "|", y)
                print("      end  ", x, "|", inst(v, vals), "|", y)
    return out


def dispatch(D, pad=4):
    N, s0 = pattern_nfa([(n, u) for n, u, v in rules()])
    def padstep(ps, c):
        if ps == "start": return ("lead", 0) if c == "<" else None
        if ps[0] == "lead":
            if ps[1] < pad: return ("lead", ps[1] + 1) if c == "0" else None
            ps = ("trail", 0)
        if ps[0] == "trail":
            if c == ">": return "end" if ps[1] >= pad else None
            return ("trail", min(ps[1] + 1, pad)) if c == "0" else ("trail", 0)
        return None
    init = (D.start, "start", N.closure({s0}), False)
    seen = {init: None}; q = deque([init])
    while q:
        node = q.popleft(); p, ps, S, matched = node
        if D.acc[p] and ps == "end":
            if not matched:
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


# ---------------------------------------------------------------- learning P from the run
def expand(seq, cap=8):
    out = []
    for t in seq:
        if isinstance(t, tuple): out.append(t[0] * min(t[1], cap))
        else: out.append(t)
    return "".join(out)


def config_text(cfg):
    return "<" + expand(config_string(cfg)) + ">"


def fine_configs(rounds):
    """Configurations of the certified run, including sampled intermediate stages of the iterated bounces and of
    the carry (stage i of BOUNCE^k is itself a configuration the single-step rules pass through)."""
    import casesim
    orig_apply = casesim.apply
    out = []
    def apply(cfg, name, L, R, v):
        if name in ("BOUNCE^k", "WALLBOUNCE^k"):
            k = v["k"]; M = v["M"]
            for i in sorted(set(list(range(1, min(k, 5) + 1)) + list(range(max(1, k - 4), k + 1)))):
                vv = dict(v); vv["k"] = i; vv["m"] = M - (2 * i if name == "BOUNCE^k" else i)
                out.append(orig_apply(cfg, name, L, R, vv))
        new = orig_apply(cfg, name, L, R, v)
        return new
    casesim.apply = apply
    def carry_stages(cfg):
        r = list(cfg.right)
        try:
            a = _unroll_front(r); tail = r[1:]; b = _unroll_front(tail)
        except Exception:
            return
        if not (a == 1 and b == 1): return
        k, rest = count_pairs(cfg.left, (0, 1), from_back=True)
        k = k.k
        for i in sorted(set(list(range(1, min(k, 4) + 1)) + list(range(max(1, k - 3), k + 1)))):
            c = Config(rest + [Rep((1, 0), Lin(k - i))], "A", [1, 1, Rep((1, 0), Lin(i))] + tail[1:])
            out.append(c)
    cfg = Config([Blank()], "A", [Blank()])
    while not proofs.is_pass_position(cfg):
        if not try_lemma(cfg): step(cfg)
    out.append(cfg.copy())
    phase = "gap"; r = 0
    try:
        while r < rounds:
            if phase == "gap":
                cfg = casesim.gap_phase(cfg); phase = "gap" if proofs.is_pass_position(cfg) else "packet"
            else:
                carry_stages(cfg)
                cfg, kind = casesim.packet_phase(cfg)
                if kind == "round": r += 1
                phase = "packet" if kind == "packet" else "gap"
            out.append(cfg.copy())         # copy: packet_phase carries in place
    finally:
        casesim.apply = orig_apply
    return out


def learn(rounds, cache=None):
    if cache and os.path.exists(cache):
        return pickle.load(open(cache, "rb"))
    sc = Scanner(None); texts = []
    for cfg in fine_configs(rounds):
        t = config_text(cfg); texts.append(t)
        s = sc.start()
        for ch in t: s = sc.delta(s, ch)
        assert s is not None and s[0] == "Z", ("base conditions fail on a real configuration", t[:200])
    res = (sc.seen, len(texts))
    if cache: pickle.dump(res, open(cache, "wb"))
    return res


def show_window(w):
    return " ".join(f"[{x}]" if i % 2 else str(x) for i, x in enumerate(w))


if __name__ == "__main__":
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    P, ncfg = learn(rounds, cache=f"ctl_P_{rounds}.pkl")
    print(f"learned {len(P)} windows from {ncfg} configurations ({rounds} rounds)")
    D = DFA(Scanner(P))
    print("automaton:", D.raw_states, "scanner states,", D.n, "after minimizing")
    res = closure(D)
    w = dispatch(D)
    print("dispatch:", "every configuration in INV matches a theorem" if w is None else "UNMATCHED " + w)


# ---------------------------------------------------------------- saturation: grow P until INV is closed
def windows_of(text):
    """The windows of a string, or None if it breaks the base conditions."""
    sc = Scanner(None); s = sc.start()
    for ch in text: s = sc.delta(s, ch)
    if s is None or s[0] != "Z": return None
    return sc.seen


PROV = {}

def saturate(P, max_iter=200, per_rule=50, log=print):
    P = set(P); added_total = []
    for it in range(max_iter):
        D = DFA(Scanner(P))
        bad = D.bad_pairs(); reach = D.shortest_to()
        live = [p for p in reach if D.alive[p]]
        new = set(); broken = []
        nfail = 0
        for name, u, v in rules():
            vars_ = {}
            for s in u + v:
                if s[0] == "rep": vars_.setdefault(s[2], set()).add(s[1])
            reps = {var: [(e, dict(zip(sorted(ws), tup))) for e, tup in power_reps(D, sorted(ws))] for var, ws in vars_.items()}
            names = sorted(reps); k = 0
            for combo in itertools.product(*[reps[n] for n in names]):
                pw = {n: c[1] for n, c in zip(names, combo)}; vals = {n: c[0] for n, c in zip(names, combo)}
                fu = eval_side(D, u, pw); fv = eval_side(D, v, pw)
                for p in live:
                    if (fu[p], fv[p]) in bad:
                        nfail += 1
                        if k >= per_rule: continue
                        k += 1
                        y = D.witness_suffix(fu[p], fv[p])
                        end = reach[p] + inst(v, vals) + y
                        w = windows_of(end)
                        if w is None: broken.append((name, reach[p] + "|" + inst(u, vals) + "|" + y, end))
                        else:
                            for win in w - P:
                                if win not in new: PROV[win] = (it, name, reach[p] + "|" + inst(u, vals) + "|" + y, end)
                            new |= (w - P)
        log(f"iteration {it}: {D.n} states, {nfail} failures, {len(new)} new windows, {len(broken)} unfixable")
        if broken:
            return P, broken, added_total
        if not new:
            return P, [], added_total
        P |= new; added_total.append(new)
    return P, None, added_total


def failing_pairs(D, queries):
    """Of the pairs (a, b) in queries, those where some suffix is accepted from a but not from b.
    Explores only the pairs reachable from the queries."""
    T = D.T; ns = len(SIG)
    idx = {}; order = []; succ = []
    st = []
    for qp in queries:
        if qp not in idx:
            idx[qp] = len(order); order.append(qp); succ.append(None); st.append(qp)
    while st:
        a, b = st.pop()
        i = idx[(a, b)]; out = []
        if D.alive[a]:
            for c in range(ns):
                nx = (T[a][c], T[b][c])
                if not D.alive[nx[0]]: continue
                if nx not in idx:
                    idx[nx] = len(order); order.append(nx); succ.append(None); st.append(nx)
                out.append(idx[nx])
        succ[i] = out
    pred = [[] for _ in order]
    for i, out in enumerate(succ):
        for j in out: pred[j].append(i)
    bad = [False] * len(order); q = deque()
    for i, (a, b) in enumerate(order):
        if D.acc[a] and not D.acc[b]: bad[i] = True; q.append(i)
    while q:
        j = q.popleft()
        for i in pred[j]:
            if not bad[i]: bad[i] = True; q.append(i)
    return {qp for qp in queries if bad[idx[qp]]}


def closure_fast(D, collect=None, per_rule=50):
    """Closure check; returns {rule: [(p, vals, a, b), ...]} of failures (up to per_rule each)."""
    reach = D.shortest_to(); live = [p for p in reach if D.alive[p]]
    work = []; queries = set()
    for name, u, v in rules():
        vars_ = {}
        for s in u + v:
            if s[0] == "rep": vars_.setdefault(s[2], set()).add(s[1])
        reps = {var: [(e, dict(zip(sorted(ws), tup))) for e, tup in power_reps(D, sorted(ws))] for var, ws in vars_.items()}
        names = sorted(reps)
        for combo in itertools.product(*[reps[n] for n in names]):
            pw = {n: c[1] for n, c in zip(names, combo)}; vals = {n: c[0] for n, c in zip(names, combo)}
            fu = eval_side(D, u, pw); fv = eval_side(D, v, pw)
            for p in live:
                if D.alive[fu[p]] and fu[p] != fv[p]:
                    work.append((name, u, v, p, vals, fu[p], fv[p])); queries.add((fu[p], fv[p]))
    badq = failing_pairs(D, queries)
    fails = {}
    for name, u, v, p, vals, a, b in work:
        if (a, b) in badq:
            fails.setdefault(name, []).append((p, vals, a, b, u, v))
    return fails, reach


def saturate2(P, max_iter=300, per_rule=40, log=print):
    P = set(P)
    for it in range(max_iter):
        D = DFA(Scanner(P))
        fails, reach = closure_fast(D)
        new = set(); broken = []; nfail = sum(len(x) for x in fails.values())
        for name, lst in fails.items():
            for p, vals, a, b, u, v in lst[:per_rule]:
                y = D.witness_suffix(a, b)
                start = reach[p] + "|" + inst(u, vals) + "|" + y
                end = reach[p] + inst(v, vals) + y
                w = windows_of(end)
                if w is None: broken.append((name, start, end))
                else:
                    for win in w - P:
                        if win not in new: PROV[win] = (it, name, start, end)
                    new |= (w - P)
        log(f"iteration {it}: {D.n} states, {nfail} failures, {len(new)} new windows, {len(broken)} unfixable")
        if broken or not new:
            return P, broken
        P |= new
    return P, None
