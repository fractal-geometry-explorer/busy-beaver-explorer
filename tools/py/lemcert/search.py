"""Search for a closed set of abstract configurations (nodes) that contains a configuration of the run from blank
tape and from which no halt is reachable.

usage: python3 search.py MACHINE [options]
"""
import sys
import time
from engine import (canon_near, Engine, Halt, K, V, ladd, isconst, lvars, norm_side, canon, cfg_str, compress_side, push,
                    subst_cfg, cvars)

sys.setrecursionlimit(100000)


# ------------------------------------------------------------------ subsumption
def side_cells_ok(items):
    return True


def match_side(N, C):
    """Is every tape of the side C (for every value of its variables) a tape of the node side N?
    N's counts are constants (exact) or ('ge', c) lower bounds with an independent fresh variable."""
    Ni, Nt = N
    Ci, Ct = C
    return _match(tuple(Ni), Nt, tuple(Ci), Ct, {})


def _pop_c(Ci, Ct):
    """First cell of C: list of (cell, rest) or None if it depends on a variable."""
    if not Ci:
        if Ct == 'B':
            return [(0, (Ci, Ct))]
        return None
    w, e = Ci[0]
    if isconst(e):
        if e[0] == 0:
            return _pop_c(Ci[1:], Ct)
        rest = Ci[1:]
        if e[0] > 1:
            rest = ((w, (e[0] - 1, ())),) + rest
        if len(w) > 1:
            rest = ((w[1:], K(1)),) + rest
        return [(w[0], (rest, Ct))]
    if e[0] >= 1:
        rest = ((w, (e[0] - 1, e[1])),) + Ci[1:]
        if len(w) > 1:
            rest = ((w[1:], K(1)),) + rest
        return [(w[0], (rest, Ct))]
    return None


def _all_blank(Ci, Ct):
    if Ct != 'B':
        return False
    return all(all(b == 0 for b in w) for w, e in Ci)


def _match(Ni, Nt, Ci, Ct, memo):
    key = (Ni, Nt, Ci, Ct)
    if key in memo:
        return memo[key]
    memo[key] = False
    r = _match1(Ni, Nt, Ci, Ct, memo)
    memo[key] = r
    return r


def _strip_zero(Ci):
    while Ci and Ci[0][1] == K(0):
        Ci = Ci[1:]
    return Ci


def _match1(Ni, Nt, Ci, Ct, memo):
    Ci = _strip_zero(Ci)
    if not Ni:
        if Nt == 'A':
            return True
        return _all_blank(Ci, Ct)
    w, e = Ni[0]
    if isinstance(e, tuple) and len(e) == 2 and e[0] == 'ge':
        c = e[1]
        # consume at least c copies of w from C
        return _consume(w, c, Ni[1:], Nt, Ci, Ct, memo, 0)
    # exact count: expand into cells
    n = e[0]
    cells = w * n
    return _cells(cells, Ni[1:], Nt, Ci, Ct, memo)


def _cells(cells, Nrest, Nt, Ci, Ct, memo):
    for b in cells:
        Ci = _strip_zero(Ci)
        p = _pop_c(Ci, Ct)
        if p is None or len(p) != 1:
            return False
        b2, (Ci, Ct) = p[0]
        if b2 != b:
            return False
    return _match(Nrest, Nt, Ci, Ct, memo)


def _consume(w, c, Nrest, Nt, Ci, Ct, memo, got):
    """got = number of copies (lower bound, constant) consumed so far."""
    Ci = _strip_zero(Ci)
    # option 1: stop here
    if got >= c and _match(Nrest, Nt, Ci, Ct, memo):
        return True
    if not Ci:
        if Ct == 'B' and all(b == 0 for b in w):
            # blank supplies any number of zero words; then rest must match blank
            return _match(Nrest, Nt, Ci, Ct, memo)
        return False
    cw, ce = Ci[0]
    # option 2: a whole block of C made of copies of w
    if len(cw) % len(w) == 0 and cw == w * (len(cw) // len(w)) and not isconst(ce):
        k = len(cw) // len(w)
        return _consume(w, c, Nrest, Nt, Ci[1:], Ct, memo, got + k * ce[0])
    if len(cw) % len(w) == 0 and cw == w * (len(cw) // len(w)) and isconst(ce) and ce[0] > 0:
        k = len(cw) // len(w)
        if _consume(w, c, Nrest, Nt, Ci[1:], Ct, memo, got + k * ce[0]):
            return True
    # option 3: one copy of w from literal cells
    C2, T2 = Ci, Ct
    for b in w:
        C2 = _strip_zero(C2)
        p = _pop_c(C2, T2)
        if p is None or len(p) != 1:
            return False
        b2, (C2, T2) = p[0]
        if b2 != b:
            return False
    if (C2, T2) == (Ci, Ct):
        return False
    return _consume(w, c, Nrest, Nt, C2, T2, memo, got + 1)


def subsumed(N, C):
    if N[0] != C[0] or N[1] != C[1]:
        return False
    return match_side(N[2], C[2]) and match_side(N[3], C[3])


# ------------------------------------------------------------------ generalisation
NBIG = [99]


TAIL = ['R']
TS = [8]


LEVELS = []
MOD = [1]
RUNMODE = [False]
SPLITRUN = [0]


def mkge(e, T):
    """Abstract a big count e (a Lin): ('ge', c) or, with MOD p > 1 and a known residue, ('ge', c, p) = c + p*v."""
    c = lbval(e[0], T)
    p = MOD[0]
    if p > 1 and all(b % p == 0 for v, b in e[1]):
        c2 = c + ((e[0] - c) % p)
        return ('ge', c2, p)
    return ('ge', c)


def ge_fresh(e, v):
    return (e[1], ((v, e[2] if len(e) == 3 else 1),))


def lbval(c, T):
    """The lower bound kept for a count with constant part c: T if c >= T, else TS (or c if c < TS)."""
    if c >= T:
        return T
    if c >= TS[0]:
        best = TS[0]
        for v in LEVELS:
            if best < v <= c and v < T:
                best = v
        return best
    return c


def gen_side(side, T, keep, nbig=None, which=None):
    """Counts: constants >= T and counts with variables become lower bounds ('ge', c).  Items are kept up to the
    nbig-th big item; after it, items worth at most `keep` cells, then any tape."""
    if nbig is None:
        nbig = NBIG[0]
    items, term = side
    bigs = [j for j, (w, e) in enumerate(items) if not isconst(e) or e[0] >= TS[0]][:nbig]
    last = bigs[-1] if bigs else -1
    out = []
    for w, e in items[:last + 1]:
        if not isconst(e) or e[0] >= TS[0]:
            out.append((w, mkge(e, T)))
        else:
            out.append((w, e))
    i = last + 1
    nb = len(bigs)
    if which is not None and which != TAIL[0] and term == 'B':
        tail = tuple((w, mkge(e, T)) if (not isconst(e) or e[0] >= TS[0]) else (w, e) for w, e in items[i:])
        return (tuple(out) + tail, term)
    # cut after `keep` cells
    if nb == 0 or RUNMODE[0]:
        out = []
        i = 0
    rest = items[i:]
    kept = []
    n = 0
    full = True
    for w, e in rest:
        if RUNMODE[0] and (not isconst(e) or e[0] >= 2):
            if n + 1 > keep:
                full = False
                break
            if SPLITRUN[0] and (not isconst(e) or e[0] > SPLITRUN[0]):
                kk = min(SPLITRUN[0], e[0])
                if kk > 0:
                    kept.append((w, K(kk)))
                full = False
                break
            kept.append((w, mkge(e, T) if (not isconst(e) or e[0] >= TS[0]) else e))
            n += 1
            continue
        if not isconst(e) or e[0] >= T:
            full = False
            break
        sz = len(w) * e[0]
        if n + sz > keep:
            full = False
            # partial: literal cells up to keep
            cells = (w * e[0])[:keep - n]
            if cells:
                kept.append((cells, K(1)))
            break
        kept.append((w, e))
        n += sz
    if full and term != 'A':
        return (tuple(out) + tuple(kept), term)
    return (tuple(out) + tuple(kept), 'A')


def is_ge_(e):
    return isinstance(e, tuple) and e[0] == 'ge'


def _rkey(c):
    names = {}

    def rl(e):
        return (e[0], tuple((names.setdefault(v, len(names)), a) for v, a in e[1]))

    def rs(s):
        return (tuple((w, rl(e)) for w, e in s[0]), s[1])
    return (c[0], c[1], rs(c[2]), rs(c[3]))


def gen_cfg(c, T, keepL, keepR):
    q, f, L, R = c
    return (q, f, gen_side(L, T, keepL), gen_side(R, T, keepR))


def node_to_cfg(N, eng):
    """A symbolic configuration standing for the node: fresh variables for lower bounds."""
    q, f, L, R = N

    def side(s):
        items, term = s
        out = []
        for w, e in items:
            if isinstance(e, tuple) and e[0] == 'ge':
                out.append((w, ge_fresh(e, eng.fresh())))
            else:
                out.append((w, e))
        return (tuple(out), term)
    return (q, f, side(L), side(R))


def nstr(N):
    def ee(e):
        if isinstance(e, tuple) and len(e) == 2 and e[0] == 'ge':
            return ('ge', e[1])
        return e
    q, f, L, R = N
    fake = (q, f, (tuple((w, (e[1], (('+', e[2] if len(e) == 3 else 1),)) if e[0] == 'ge' else e) for w, e in L[0]), L[1]),
            (tuple((w, (e[1], (('+', e[2] if len(e) == 3 else 1),)) if e[0] == 'ge' else e) for w, e in R[0]), R[1]))
    return cfg_str(fake)


# ------------------------------------------------------------------ macro moves
def subst_lin_seq(e, subs):
    from engine import lsubst
    for v, y in subs:
        e = lsubst(e, v, y)
    return e


def subst_cfg_seq(c, subs):
    for v, y in subs:
        c = subst_cfg(c, v, y)
    return c


class Rule:
    """G(z + m) reaches G(z + m + d) in at least one step, for all z >= 0 (one variable per item)."""

    def __init__(self, shape, words, m, d, moves):
        self.shape, self.words, self.m, self.d, self.moves = shape, words, m, d, moves


class Prover:
    def __init__(self, machine, T=8, keep=4, maxdepth=4000, maxnodes=20000, verbose=False, loops=True):
        self.eng = Engine(machine)
        self.T = T
        self.keep = {}
        self.keep0 = keep
        self.maxdepth = maxdepth
        self.maxnodes = maxnodes
        self.verbose = verbose
        self.loops = loops
        self.rules = {}        # shape -> Rule or None
        self.stats = {'rules': 0, 'ruleapps': 0, 'infloops': 0}

    def advance(self, c):
        """One macro move: list of (successor, subs), successors canonical."""
        e = self.eng
        q, f, L, R = c
        side = R if f == 'R' else L
        if side[0]:
            w, ex = side[0][0]
            if not isconst(ex) or ex[0] >= 3:
                r = e.cross(c)
                if r is not None:
                    return [(canon_near(x), ()) for x in r]
                for k in (2, 3, 4, 6):
                    if len(w) * k > 24:
                        break
                    if e.window(q, f, w * k, ()) is not None:
                        outs = []
                        for x, sb in e.regroup(c, k):
                            r = e.cross(x)
                            if r is not None:
                                outs.extend((y, sb) for y in r)
                            else:
                                outs.extend((y, sb + sb2) for y, sb2 in e.step(x))
                        return [(canon_near(x), sb) for x, sb in outs]
        return [(canon_near(x), sb) for x, sb in e.step(c)]

    def is_checkpoint(self, c):
        q, f, L, R = c
        side = R if f == 'R' else L
        return not side[0]

    def shape(self, c):
        q, f, L, R = c
        return (q, f, tuple(w for w, e in L[0]), L[1], tuple(w for w, e in R[0]), R[1])

    def lshape(self, c):
        """Shape for loops: words and which counts are literal 1."""
        q, f, L, R = c
        return (q, f, tuple((w, e == K(1)) for w, e in L[0]), L[1], tuple((w, e == K(1)) for w, e in R[0]), R[1])

    def generalize(self, c):
        k = self.keep.get(self.shape(c), self.keep0)
        return gen_cfg(c, self.T, k, k), self.shape(c)

    def find(self, c):
        for i, N in enumerate(self.nodes):
            if subsumed(N, c):
                return i
        return None

    # -------------------------------------------------------------- loops (induction rules)
    @staticmethod
    def counts(c):
        return [e for w, e in c[2][0]] + [e for w, e in c[3][0]]

    @staticmethod
    def with_counts(c, es):
        q, f, L, R = c
        nl = len(L[0])
        Li = tuple((w, es[i]) for i, (w, _) in enumerate(L[0]))
        Ri = tuple((w, es[nl + i]) for i, (w, _) in enumerate(R[0]))
        return (q, f, (Li, L[1]), (Ri, R[1]))

    def prove_rule(self, P, d):
        """P: a configuration, d: the constant changes of its counts after one loop.  Returns a Rule or None.
        The rule is proved from the smallest minimum counts that the symbolic run needs."""
        from engine import Stuck
        es = self.counts(P)
        m = []
        for e, dd in zip(es, d):
            if e == K(1) and dd == 0:
                m.append(None)          # literal
            else:
                m.append(max(-dd, 0))
        for attempt in range(60):
            zs = [None if mm is None else self.eng.fresh() for mm in m]
            G = self.with_counts(P, [K(1) if mm is None else (mm, ((z, 1),)) for mm, z in zip(m, zs)])
            target = [K(1) if mm is None else (mm + dd, ((z, 1),)) for mm, z, dd in zip(m, zs, d)]
            sh = self.lshape(G)
            self.eng.nosplit = True
            try:
                c = G
                for n in range(1, 3000):
                    nxt = self.advance(c)
                    if len(nxt) != 1:
                        return None
                    c = nxt[0][0]
                    if self.lshape(c) == sh:
                        if self.counts(c) == target:
                            return Rule(sh, None, m, d, n)
                        return None
                return None
            except Stuck as s:
                v = s.args[0]
                if v is None or v not in zs:
                    return None
                m[zs.index(v)] += 1
            except Halt:
                return None
            except Exception as ex:
                if type(ex).__name__ == 'ExitS':
                    return None
                raise
            finally:
                self.eng.nosplit = False
        return None

    def try_loop(self, c, hist):
        """hist: linked list (cfg, subs_after, parent).  Look back for the same loop shape."""
        sh = self.lshape(c)
        subs = []
        h = hist
        n = 0
        while h is not None and n < 400:
            pc, psubs, parent, psh = h
            subs = list(psubs) + subs
            if psh == sh:
                P = subst_cfg_seq(pc, subs)
                d = []
                ok = True
                for a, b in zip(self.counts(P), self.counts(c)):
                    x = ldiff_(b, a)
                    if x is None:
                        ok = False
                        break
                    d.append(x)
                if ok and any(d):
                    r = self.apply_loop(c, P, tuple(d))
                    if r is not None or not getattr(self, 'tailloops', False) or any(x < 0 for x in d):
                        return r
                    gk = getattr(self, 'gen_keys', None)
                    if gk is None:
                        gk = self.gen_keys = set()
                    if _rkey(P) in gk:
                        self.stats['tailclose'] = self.stats.get('tailclose', 0) + 1
                        return []
                    j = self.eng.fresh()
                    es = self.counts(P)
                    Pg = canon(self.with_counts(P, [ladd(e, (0, ((j, x),))) if x > 0 else e for e, x in zip(es, d)]))
                    gk.add(_rkey(Pg))
                    self.stats['tailgen'] = self.stats.get('tailgen', 0) + 1
                    return [(Pg, ())]
                if ok and not any(d) and P == c:
                    self.stats['infloops'] += 1
                    return []          # exact repeat: runs for ever
                return None
            h = parent
            n += 1
        return None

    def apply_loop(self, c, P, d):
        key = (self.lshape(P), d)
        if key not in self.rules:
            r = self.prove_rule(P, d)
            self.rules[key] = r
            if r is not None:
                self.stats['rules'] += 1
        r = self.rules[key]
        if r is None:
            return None
        es = self.counts(c)
        dec = [i for i, x in enumerate(d) if x < 0]
        for i, (e, mm) in enumerate(zip(es, r.m)):
            if mm is not None and e[0] < mm:
                return None
        if not dec:
            self.stats['infloops'] += 1
            return []
        if len(dec) > 1:
            return None
        i = dec[0]
        dd = -d[i]
        # e_i - m_i = dd * n' + r; then n = n' + 1 loops
        outs = []
        cs = [(c, ())]
        e = es[i]
        for v, a in e[1]:
            if a % dd:
                nc = []
                for x, sb in cs:
                    for rr in range(dd):
                        y = (rr, ((self.eng.fresh(), dd),))
                        nc.append((subst_cfg(x, v, y), sb + ((v, y),)))
                cs = nc
        for x, sb in cs:
            es2 = self.counts(x)
            ei = es2[i]
            base = ei[0] - r.m[i]
            rr = base % dd
            nprime = ((base - rr) // dd, tuple((v, a // dd) for v, a in ei[1]))
            n = ladd(nprime, K(1))
            new = []
            for j, (ej, dj) in enumerate(zip(es2, d)):
                if dj == 0:
                    new.append(ej)
                elif dj > 0:
                    new.append(ladd(ej, lmul_(n, dj)))
                else:
                    # ei - n*dd = m_i + rr - dd
                    new.append(K(r.m[i] + rr - dd))
            self.stats['ruleapps'] += 1
            outs.append((canon(self.with_counts(x, new)), sb))
        return outs

    # -------------------------------------------------------------- search
    def run(self, start):
        """start: a concrete canonical configuration reached from blank tape."""
        while True:
            res = self.attempt(start)
            if res[0] == 'ok':
                return res
            if res[0] == 'halt':
                if self.verbose:
                    print("HALT", res[1], f"nodes {len(self.nodes)}")
                    for x in res[3][:6]:
                        print("   <-", x)
                done = True
                for shp in res[2]:
                    k = self.keep.get(shp, self.keep0)
                    if k < 64:
                        self.keep[shp] = k * 2
                        done = False
                if done:
                    return ('fail', 'keep limit', res)
                continue
            return res

    def attempt(self, start):
        self.nodes = []
        self.origin = []
        g, shp = self.generalize(start)
        self.nodes.append(g)
        self.origin.append(shp)
        self.parent = [None]
        i = 0
        while i < len(self.nodes):
            if len(self.nodes) > self.maxnodes:
                return ('fail', 'too many nodes', len(self.nodes))
            N = self.nodes[i]
            try:
                self.explore(i)
            except Halt as h:
                chain = []
                j = i
                while j is not None:
                    chain.append(j)
                    j = self.parent[j]
                return ('halt', str(h), [self.origin[j] for j in chain], [nstr(self.nodes[j]) for j in chain])
            i += 1
        return ('ok', self.nodes)

    def explore(self, i):
        N = self.nodes[i]
        c0 = node_to_cfg(N, self.eng)
        stack = [(x, 1, (c0, sb, None, self.lshape(c0))) for x, sb in self.advance_first(c0)]
        while stack:
            c, d, hist = stack.pop()
            j = self.find(c)
            if j is not None:
                continue
            if self.is_checkpoint(c) or d > self.maxdepth:
                g, shp = self.generalize(c)
                if self.find(node_to_cfg(g, self.eng)) is None:
                    self.nodes.append(g)
                    self.origin.append(shp)
                    self.parent.append(i)
                    if self.verbose and len(self.nodes) % 50 == 0:
                        print(len(self.nodes), nstr(g), flush=True)
                continue
            if self.loops:
                lo = self.try_loop(c, hist)
                if lo is not None:
                    for x, sb in lo:
                        stack.append((x, d + 1, (c, sb, hist, self.lshape(c))))
                    continue
            for x, sb in self.advance(c):
                stack.append((x, d + 1, (c, sb, hist, self.lshape(c))))

    def advance_first(self, c):
        return [(canon(x), sb) for x, sb in self.eng.step(c)]


def ldiff_(b, a):
    from engine import ldiff
    return ldiff(b, a)


def lmul_(x, k):
    from engine import lmul
    return lmul(x, k)


def blank_cfg():
    return (0, 'R', ((), 'B'), ((), 'B'))


def run_concrete(machine, n):
    """Plain simulation for n steps; returns the canonical configuration."""
    from engine import parse
    T = parse(machine)
    tape = {}
    pos, q = 0, 0
    for _ in range(n):
        b = tape.get(pos, 0)
        t = T[(q, b)]
        if t is None:
            raise Halt("concrete halt")
        wr, d, q = t
        tape[pos] = wr
        pos += 1 if d == 'R' else -1
    lo = min(list(tape) + [pos]) 
    hi = max(list(tape) + [pos])
    R = tuple(((tape.get(x, 0),), K(1)) for x in range(pos, hi + 1))
    L = tuple(((tape.get(x, 0),), K(1)) for x in range(pos - 1, lo - 1, -1))
    return canon((q, 'R', (L, 'B'), (R, 'B')))


if __name__ == "__main__":
    m = sys.argv[1]
    n0 = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    T = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    P = Prover(m, T=T, verbose=True)
    c = run_concrete(m, n0)
    print("start", cfg_str(c))
    t = time.time()
    r = P.run(c)
    print(r[0], r[1:] if r[0] != 'ok' else len(r[1]), f"{time.time() - t:.1f}s", P.stats)
    if r[0] == 'ok':
        for N in r[1]:
            print("  ", nstr(N))
