"""Summary certificates: nodes with a caller's stack, exits, and fixpoint search.

A node is an abstract configuration (q, f, L, R) whose sides end in 'B' (blank), 'A' (any stream) or 'S' (the
caller's part of the tape, which the node never reads: reading it is an *exit*).  Counts are exact constants or lower
bounds ('ge', c).  A node's claim: from every configuration it stands for, with any tape in place of S, the machine
either runs for ever or reaches one of the node's exits: the head facing S in state q', the other side matching X.

Exploring a node runs macro moves from it.  A branch ends
* at an exit (head reads S): the exit is recorded;
* when a node M covers it: if M has an S side, M covers a prefix of the branch's side and the rest of that side
  becomes M's S; the branch continues from each exit of M (with that rest behind the head);
  otherwise the branch is closed (M never halts and never exits);
* at a checkpoint (head at the edge of what the side holds, facing 'A' or 'B'): a new node is made.  If the side
  behind the head holds more than CALLK literal cells before its first big item, the new node keeps only CALLK of
  them and an S behind them (a call); otherwise the whole configuration is generalised.
A halt on any branch fails the attempt; the generalisation that let it in is refined and the search restarts.
"""
import sys
import time
from engine import (Engine, Halt, ExitS, Stuck, K, V, ladd, isconst, norm_side, canon, cfg_str, subst_cfg)
from search import Prover as FlatProver, gen_side, nstr, run_concrete, TS, lbval, mkge, ge_fresh


def is_ge(e):
    return isinstance(e, tuple) and e[0] == 'ge'


# ------------------------------------------------------------------ prefix matching
def _pop1(Ci, Ct):
    """First cell of the concrete-ish side C: (cell, rest) or None if unknown."""
    while Ci and Ci[0][1] == K(0):
        Ci = Ci[1:]
    if not Ci:
        if Ct == 'B':
            return 0, (Ci, Ct)
        return None
    w, e = Ci[0]
    if e[0] >= 1:
        rest = Ci[1:]
        e1 = (e[0] - 1, e[1])
        if e1 != K(0):
            rest = ((w, e1),) + rest
        if len(w) > 1:
            rest = ((w[1:], K(1)),) + rest
        return w[0], (rest, Ct)
    return None


def _strip(Ci):
    while Ci and Ci[0][1] == K(0):
        Ci = Ci[1:]
    return Ci


def gen_match(Ni, Ci, Ct):
    """Yield the rests (Ci', Ct) of C after the node items Ni have consumed a prefix of it, for all values."""
    Ci = _strip(Ci)
    if not Ni:
        yield (Ci, Ct)
        return
    w, e = Ni[0]
    if is_ge(e):
        yield from _consume(w, e[1], Ni[1:], Ci, Ct, 0, 0, e[2] if len(e) == 3 else 1, True)
    else:
        cells = w * e[0]
        C2 = (Ci, Ct)
        for b in cells:
            p = _pop1(*C2)
            if p is None or p[0] != b:
                return
            C2 = p[1]
        yield from gen_match(Ni[1:], *C2)


def _consume(w, c, Nrest, Ci, Ct, got, depth, p=1, okm=True):
    """Consume copies of w for a node count c + p*v; okm: the symbolic part consumed so far is a multiple of p."""
    if depth > 200:
        return
    Ci = _strip(Ci)
    # take more first (greedy), then stop
    if Ci:
        cw, ce = Ci[0]
        if len(cw) % len(w) == 0 and cw == w * (len(cw) // len(w)) and (not isconst(ce) or ce[0] > 1):
            k = len(cw) // len(w)
            ok2 = okm and all((k * b) % p == 0 for v, b in ce[1])
            yield from _consume(w, c, Nrest, Ci[1:], Ct, got + k * ce[0], depth + 1, p, ok2)
        else:
            C2 = (Ci, Ct)
            ok = True
            for b in w:
                q = _pop1(*C2)
                if q is None or q[0] != b:
                    ok = False
                    break
                C2 = q[1]
            if ok and C2 != (Ci, Ct):
                yield from _consume(w, c, Nrest, C2[0], C2[1], got + 1, depth + 1, p, okm)
    elif Ct == 'B' and all(b == 0 for b in w) and got < c:
        yield from gen_match(Nrest, Ci, Ct)
        return
    if got >= c and okm and (got - c) % p == 0:
        yield from gen_match(Nrest, Ci, Ct)


def trim_hist(h, n=120):
    items = []
    while h is not None and len(items) < n:
        items.append(h)
        h = h[2]
    out = None
    for (c, sb, _, sh) in reversed(items):
        out = (c, sb, out, sh)
    return out


def blank_rest(Ci, Ct):
    return Ct == 'B' and all(all(b == 0 for b in w) for w, e in Ci)


BIGT = [8]
WHY = {}


def has_big(items):
    return any(not isconst(e) or e[0] >= TS[0] for w, e in items)


def side_cover(N, C):
    """None if the node side N does not cover C; 'full' if it covers it all; ('rest', side) if N ends in S and covers a
    prefix of C, the rest being side."""
    Ni, Nt = N
    Ci, Ct = C
    for rest in gen_match(Ni, Ci, Ct):
        Ri, Rt = rest
        if Nt == 'A':
            return 'full'
        if Nt == 'B':
            if blank_rest(Ri, Rt):
                return 'full'
            continue
        if Nt == 'S':
            return ('rest', rest)
    return None


def cover(N, c):
    """How node N covers configuration c: None, 'full', or ('rest', side, which) for an S side."""
    if N[0] != c[0] or N[1] != c[1]:
        return None
    a = side_cover(N[2], c[2])
    if a is None:
        return None
    b = side_cover(N[3], c[3])
    if b is None:
        return None
    if a == 'full' and b == 'full':
        return 'full'
    return ('rest', (None if a == 'full' else a[1], None if b == 'full' else b[1]), None)


def rename_key(c):
    names = {}

    def rl(e):
        return (e[0], tuple((names.setdefault(v, len(names)), a) for v, a in e[1]))

    def rs(s):
        return (tuple((w, rl(e)) for w, e in s[0]), s[1])
    return (c[0], c[1], rs(c[2]), rs(c[3]))


# ------------------------------------------------------------------ the prover
CALLK = 3


class Prover(FlatProver):
    def __init__(self, machine, callk=CALLK, **kw):
        super().__init__(machine, **kw)
        self.callk = callk
        self.cpmax = 6
        self.callsides = 'LR'
        self.lookahead = True
        self.frame = False
        self.slimit = 0
        self.Tcall = 0
        self.runcall = False
        self.keepexact = False
        self.splitrun = 0
        self.fullexits = False
        self.bfs = False
        self.la_fail = set()
        self.jmax = 12
        BIGT[0] = self.T

    def fresh_side(self, s):
        items, term = s
        out = []
        for w, e in items:
            if is_ge(e):
                out.append((w, ge_fresh(e, self.eng.fresh())))
            else:
                out.append((w, e))
        return (tuple(out), term)

    def node_cfg(self, N):
        q, f, L, R = N
        return (q, f, self.fresh_side(L), self.fresh_side(R))

    def is_checkpoint(self, c):
        q, f, L, R = c
        side = R if f == 'R' else L
        return not side[0] and side[1] in 'AB'

    def junk(self, c):
        q, f, L, R = c
        behind = L if f == 'R' else R
        front = R if f == 'R' else L
        if front[1] == 'S':
            return 0
        n = 0
        for w, e in behind[0]:
            if not isconst(e):
                break
            n += len(w) * e[0]
            if n > 64:
                break
        return n

    def make_node(self, c):
        """The node for checkpoint c: a call (keep CALLK literal cells behind the head, then S) or the whole
        configuration generalised."""
        q, f, L, R = c
        front, behind = (R, L) if f == 'R' else (L, R)
        k = self.keep0
        fw = f
        bw = 'L' if f == 'R' else 'R'
        Tc = self.Tcall or self.T
        if front[1] == 'S':
            gfront = self.gen_keep_s(front, self.slimit, Tc)
            gbehind = self.fr(gen_side(behind, Tc, k, which=bw))
            if f == 'R':
                return (q, f, gbehind, gfront), self.shape(c)
            return (q, f, gfront, gbehind), self.shape(c)
        gfront = gen_side(front, self.T, k, which=fw)
        items, term = behind
        cells = ()
        callable_ = True
        for w, e in items:
            if len(cells) > self.callk:
                break
            if not isconst(e):
                break
            cells += w * e[0]
        if self.runcall:
            import search as _s
            _s.SPLITRUN[0] = self.splitrun
            try:
                gcall = gen_side(behind, Tc, self.callk, which=None)
            finally:
                _s.SPLITRUN[0] = 0
        else:
            gcall = None
        if self.runcall and bw in self.callsides and term != 'S' and gcall[1] == 'A' and term != 'A' and gcall[0]:
            gbehind = (gcall[0], 'S')
            gfront = self.fr(gen_side(front, Tc, k, which=fw))
        elif len(cells) > self.callk and bw in self.callsides:
            gbehind = (((cells[:self.callk], K(1)),), 'S')
            gfront = gen_side(front, Tc, k, which=fw)
            if self.frame and gfront[1] == "A" and gfront[0]:
                gfront = (gfront[0], 'S')
        elif term == 'S':
            gbehind = self.gen_keep_s(behind, self.slimit, Tc)
            gfront = self.fr(gen_side(front, Tc, k, which=fw))
        else:
            gbehind = self.fr(gen_side(behind, self.T, k, which=bw))
        if self.frame and self.slimit and front[1] != 'S' and len(gfront[0]) > self.slimit:
            Tf = self.T if (gbehind[1] != 'S') else Tc
            gfront = (self.gen_keep_s((front[0], 'S'), self.slimit, Tf)[0], 'S')
        if f == 'R':
            return (q, f, gbehind, gfront), self.shape(c)
        return (q, f, gfront, gbehind), self.shape(c)

    def cuts_counter(self, G):
        for side in (G[2], G[3]):
            for w, e in side[0]:
                if is_ge(e) and e[1] >= TS[0]:
                    return True
        return False

    def fr(self, g):
        if self.frame and g[1] == 'A' and g[0]:
            return (g[0], 'S')
        return g

    def gen_keep_s(self, side, limit=0, T=None):
        """Generalise counts on a side that ends in S, keeping every item."""
        items, term = side
        out = []
        for w, e in items:
            if limit and len(out) >= limit:
                break
            if not isconst(e) or e[0] >= TS[0]:
                out.append((w, mkge(e, T or self.T)))
            else:
                out.append((w, e))
        return (tuple(out), term)

    def find_cover(self, c):
        for j, nd in enumerate(self.nodes):
            if nd['hasS']:
                continue
            r = cover(nd['N'], c)
            if r is not None:
                return j, r
        return None, None

    def continuations(self, j, rest, which, start=0):
        """Configurations after the exits of node j, with `rest` in place of S on side `which`."""
        out = []
        for (q2, f2, X) in self.nodes[j]['exits'][start:]:
            Xs = self.fresh_side(X)
            fi = 0 if f2 == 'L' else 1
            rf = rest[fi]
            ro = rest[1 - fi]
            if rf is None:
                raise RuntimeError("exit on a side without S")
            if Xs[1] == 'S':
                if ro is None:
                    raise RuntimeError("exit side ends in S but the node side does not")
                Xs = (Xs[0] + ro[0], ro[1])
            if f2 == 'L':
                out.append(canon((q2, f2, rf, Xs)))
            else:
                out.append(canon((q2, f2, Xs, rf)))
        return out

    def add_node(self, N, shp, parent):
        nd = {'N': N, 'exits': [], 'deps': set(), 'origin': shp, 'parent': parent,
              'hasS': N[2][1] == 'S' or N[3][1] == 'S'}
        self.nodes.append(nd)
        self.index[N] = len(self.nodes) - 1
        self.work.append(len(self.nodes) - 1)
        return len(self.nodes) - 1

    def attempt(self, start):
        self.nodes = []
        self.work = []
        self.index = {}
        N, shp = self.make_node_top(start)
        self.add_node(N, shp, None)
        n_expl = 0
        while self.work:
            if len(self.nodes) > self.maxnodes:
                return ('fail', 'too many nodes', len(self.nodes))
            i = self.work.pop()
            n_expl += 1
            try:
                new = self.explore(i)
            except Halt as h:
                if self.verbose is True and getattr(h, 'path', None):
                    print("PATH in node", nstr(self.nodes[i]['N']))
                    for p in h.path[-40:]:
                        print("     ", p)
                chain = []
                j = i
                while j is not None:
                    chain.append(j)
                    j = self.nodes[j]['parent']
                if self.verbose is True:
                    for j in chain[:3]:
                        print("NODE", nstr(self.nodes[j]['N']), "made by path:")
                        hc = self.nodes[j].get('hist')
                        if hc:
                            path = [cfg_str(hc[0])]
                            hh = hc[1]
                            while hh is not None and len(path) < 3000:
                                path.append(cfg_str(hh[0]))
                                hh = hh[2]
                            for p in path[::-1]:
                                print("        ", WHY.get(p, ''), p)
                return ('halt', str(h), [self.nodes[j]['origin'] for j in chain],
                        [nstr(self.nodes[j]['N']) for j in chain])
            if new:
                for d in self.nodes[i]['deps']:
                    if d not in self.work:
                        self.work.append(d)
            if self.verbose and n_expl % 200 == 0:
                print(f"  explored {n_expl}, nodes {len(self.nodes)}, queue {len(self.work)}", flush=True)
        return ('ok', self.nodes)

    def make_node_top(self, c):
        q, f, L, R = c
        k = self.keep0
        import search as _s
        old = _s.MOD[0]
        _s.MOD[0] = 1
        try:
            return (q, f, gen_side(L, self.T, k, which='L'), gen_side(R, self.T, k, which='R')), self.shape(c)
        finally:
            _s.MOD[0] = old

    def add_exit(self, i, q, f, X):
        nd = self.nodes[i]
        Xg = self.gen_exit(X, 'L' if f == 'R' else 'R')
        for (q2, f2, Y) in nd['exits']:
            if q2 == q and f2 == f and side_cover(Y, self.fresh_side(Xg)) == 'full':
                return False
        nd['exits'].append((q, f, Xg))
        return True

    def gen_exit(self, X, which):
        k = self.keep0
        if self.fullexits and X[1] == 'A':
            return self.gen_keep_s(X, 0, self.Tcall or self.T)
        return gen_side(X, self.T, k, which=which) if X[1] != 'S' else self.gen_keep_s(X)

    def lookahead_loop(self, c, hist, nmax=150):
        """Follow the single-branch run from c for up to nmax macro moves; if a loop rule applies on the way,
        return its results (the path is deterministic and introduces no substitutions)."""
        key = rename_key(c)
        if key in self.la_fail:
            return None
        x = c
        h = hist
        for t in range(nmax):
            try:
                nxt = self.advance(x)
            except Exception:
                break
            if len(nxt) != 1 or nxt[0][1]:
                break
            y = nxt[0][0]
            q, f, L, R = y
            side = R if f == 'R' else L
            if not side[0] and side[1] == 'S':
                break
            h = (x, (), h, self.lshape(x))
            lo = self.try_loop(y, h)
            if lo is not None:
                self.stats['lookahead'] = self.stats.get('lookahead', 0) + 1
                return lo
            x = y
        self.la_fail.add(key)
        return None

    def loose(self, c):
        q, f, L, R = c
        front, behind = (R, L) if f == 'R' else (L, R)
        fs = (tuple((w, e == K(1)) for w, e in front[0]), front[1])
        b0 = behind[0][0][0] if behind[0] else behind[1]
        return (q, f, fs, b0)

    def seen_once(self, c, hist):
        sh = self.loose(c)
        h = hist
        n = 0
        cnt = 0
        while h is not None and n < 400:
            if self.loose(h[0]) == sh:
                cnt += 1
            h = h[2]
            n += 1
        return cnt == 1

    def explore(self, i):
        nd = self.nodes[i]
        N = nd['N']
        c0 = self.node_cfg(N)
        new = False
        if 'seen' not in nd:
            nd['seen'] = set()
            nd['sites'] = []
            stack = [(x, 1, (c0, sb, None, self.lshape(c0)), 0) for x, sb in self.advance_first(c0)]
        else:
            stack = []
            for site in nd['sites']:
                j, rest, which, sc, shist, sd, scp, used = site
                ex = self.nodes[j]['exits']
                if len(ex) > used:
                    for x in self.continuations(j, rest, which, used):
                        stack.append((x, sd + 1, (sc, (), shist, self.lshape(sc)), scp))
                        if self.verbose is True: WHY[cfg_str(x)] = 'resume'
                    site[7] = len(ex)
        steps = 0
        seen = nd['seen']
        while stack:
            c, d, hist, cp = stack.pop(0) if self.bfs else stack.pop()
            key = hash(rename_key(c))
            if key in seen:
                continue
            seen.add(key)
            steps += 1
            q, f, L, R = c
            side = R if f == 'R' else L
            if not side[0] and side[1] == 'S':
                other = L if f == 'R' else R
                if self.add_exit(i, q, f, other):
                    new = True
                    if self.verbose is True:
                        nd.setdefault('exit_hist', []).append((c, hist))
                continue
            j, how = self.find_cover(c)
            if j is not None and how == 'full':
                continue
            if self.loops:
                lo = self.try_loop(c, hist)
                if lo is not None:
                    for x, sb in lo:
                        stack.append((x, d + 1, (c, sb, hist, self.lshape(c)), cp))
                        if self.verbose is True: WHY[cfg_str(x)] = 'loop'
                    continue
            if j is not None:
                _, rest, which = how
                self.nodes[j]['deps'].add(i)
                nd['sites'].append([j, rest, which, c, trim_hist(hist), d, cp, len(self.nodes[j]['exits'])])
                for x in self.continuations(j, rest, which):
                    stack.append((x, d + 1, (c, (), hist, self.lshape(c)), cp))
                    if self.verbose is True: WHY[cfg_str(x)] = 'cover'
                continue
            if steps == 20000 and self.verbose:
                print("  long exploration of", nstr(N)[:150], flush=True)
            if self.verbose and 20000 <= steps < 20003:
                print("     ", d, cp, cfg_str(c)[:200], flush=True)
            if self.is_checkpoint(c) or d > self.maxdepth or self.junk(c) > self.jmax or steps > 20000:
                if self.loops and self.lookahead and d <= self.maxdepth and steps <= 20000:
                    lo = self.lookahead_loop(c, hist)
                    if lo is not None:
                        for x, sb in lo:
                            stack.append((x, d + 1, (c, sb, hist, self.lshape(c)), cp))
                            if self.verbose is True: WHY[cfg_str(x)] = 'lookahead'
                        continue
                G, shp = self.make_node(c)
                isS = G[2][1] == 'S' or G[3][1] == 'S'
                if not isS and cp < self.cpmax and d <= self.maxdepth and steps <= 20000 and c[2][1] != 'S' and c[3][1] != 'S':
                    for x, sb in self.advance(c):
                        stack.append((x, d + 1, (c, sb, hist, self.lshape(c)), cp + 1))
                        if self.verbose is True: WHY[cfg_str(x)] = 'cp'
                    continue
                if isS and self.keepexact and cp < self.cpmax and d <= self.maxdepth and steps <= 20000 \
                        and c[2][1] != 'S' and c[3][1] != 'S' and self.cuts_counter(G):
                    for x, sb in self.advance(c):
                        stack.append((x, d + 1, (c, sb, hist, self.lshape(c)), cp + 1))
                        if self.verbose is True: WHY[cfg_str(x)] = 'cpX'
                    continue
                if isS and cp < self.cpmax and d <= self.maxdepth and steps <= 20000 and self.seen_once(c, hist):
                    for x, sb in self.advance(c):
                        stack.append((x, d + 1, (c, sb, hist, self.lshape(c)), cp + 1))
                        if self.verbose is True: WHY[cfg_str(x)] = 'cpS'
                    continue
                if not isS and G not in self.index:
                    why = 'cp' if cp >= self.cpmax else ('depth' if d > self.maxdepth else ('steps' if steps > 20000 else 'S-in-c'))
                    self.stats['top_' + why] = self.stats.get('top_' + why, 0) + 1
                    if self.verbose and self.stats['top_' + why] <= 3:
                        print("TOPNODE", why, cp, d, steps, cfg_str(c)[:200], self.stats, flush=True)
                if G in self.index:
                    j = self.index[G]
                else:
                    j = self.add_node(G, shp, i)
                if self.verbose is True:
                    self.nodes[j]['hist'] = (c, hist)
                how = cover(G, c)
                if how is None:
                    raise RuntimeError("new node does not cover its configuration: " + cfg_str(c) + " / " + nstr(G))
                if how != 'full':
                    _, rest, which = how
                    self.nodes[j]['deps'].add(i)
                    nd['sites'].append([j, rest, which, c, trim_hist(hist), d, cp, len(self.nodes[j]['exits'])])
                    for x in self.continuations(j, rest, which):
                        stack.append((x, d + 1, (c, (), hist, self.lshape(c)), cp))
                        if self.verbose is True: WHY[cfg_str(x)] = 'nodecont'
                if self.verbose and len(self.nodes) % 100 == 0:
                    print(len(self.nodes), nstr(G), flush=True)
                continue
            try:
                nxt = self.advance(c)
            except ExitS:
                raise RuntimeError("exit inside a move: " + cfg_str(c))
            except Halt as h:
                path = [cfg_str(c)]
                hh = hist
                while hh is not None:
                    path.append(cfg_str(hh[0]))
                    hh = hh[2]
                h.path = path[::-1]
                raise
            for x, sb in nxt:
                stack.append((x, d + 1, (c, sb, hist, self.lshape(c)), cp))
                if self.verbose is True: WHY[cfg_str(x)] = 'step'
        return new


def run_global(P, start, kmax=64):
    while True:
        r = P.attempt(start)
        print(f"keep {P.keep0}: {r[0]} {r[1] if r[0] != 'ok' else ''} nodes {len(P.nodes)}", flush=True)
        if r[0] != 'halt' or P.keep0 >= kmax:
            return r
        P.keep0 *= 2


if __name__ == "__main__":
    m = sys.argv[1]
    n0 = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    T = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    P = Prover(m, T=T, verbose=True)
    c = run_concrete(m, n0)
    print("start", cfg_str(c))
    t = time.time()
    P.verbose = 'progress'
    r = run_global(P, c)
    print(r[0], r[1:] if r[0] != 'ok' else len(r[1]), f"{time.time() - t:.1f}s", P.stats)
    if r[0] == 'ok':
        for nd in r[1]:
            print("  ", nstr(nd['N']), "  exits:", [(q, f, nstr((0, 'R', ((), 'B'), X))) for q, f, X in nd['exits']])
