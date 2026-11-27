#!/usr/bin/env python3
"""Return-shape analysis (set-based analysis of the machine's sweeps).
The tape right of a cut is a token list (token d = 1^d 0) described by explicit cells followed by a nonterminal.
A call = the head entering a tail V in state S with left context ctx (the cells back to the J-th zero);
it returns when the head leaves to the left of ctx.  Contract C(S,ctx,V) = set of (S', head cells, V').
Nonterminals are not given: a return whose tail has more than L tokens is cut after L tokens and the rest is
named by the call (state, ctx, the caller's nonterminal truncated to depth j), the exit state and the L head tokens.
The grammar is the least fixpoint from a seed tape.  Everything is finite; a reachable halting transition = failure."""
import sys, collections, argparse, time

class Fail(Exception): pass

def parse_tm(s, mirror=False):
    T = {}
    for i, row in enumerate(s.split('_')):
        for b in range(2):
            t = row[3*b:3*b+3]
            if t[0] == '-': T[(i, b)] = None
            else:
                d = 1 if t[1] == 'R' else -1
                T[(i, b)] = (int(t[0]), -d if mirror else d, ord(t[2]) - 65)
    return T

def fmt_cells(cs):
    out = []; d = 0
    for c in cs:
        if c: d += 1
        else: out.append(str(d)); d = 0
    s = ' '.join(out)
    if d: s += ' 1^%d|' % d
    return s

def load(fn, skip=0, maxn=None):
    """sampler output -> {(state, gap, first token): [token lists]}"""
    out = collections.defaultdict(list)
    n = 0
    for ln in open(fn):
        if ln.startswith('HALT'): raise SystemExit('halted')
        n += 1
        if n <= skip: continue
        if maxn and n > skip + maxn: break
        a, b = ln.split(':'); _, st, gap = a.split(); toks = tuple(int(x) for x in b.split())
        out[(ord(st) - 65, int(gap), toks[0])].append(toks)
    return out

def trunc(V, j):
    if not isinstance(V, tuple): return V
    if V[0] == 'O':
        if j == 0: return '*'
        return ('O', V[1], V[2], trunc(V[3], j - 1), V[4], V[5])
    if V[0] == 'T': return ('T', trunc(V[1], j), V[2])
    return V

class SBA:
    def __init__(self, T, L=1, J=2, j=1, fuel=200000, maxword=2000, maxshapes=5000, maxnt=200000):
        self.T, self.L, self.J, self.j = T, L, J, j
        self.fuel, self.maxword, self.maxshapes, self.maxnt = fuel, maxword, maxshapes, maxnt
        self.prods = collections.defaultdict(set); self.prods['END'].add((0, 'END'))
        self.C = {}; self.cdeps = collections.defaultdict(set); self.udeps = collections.defaultdict(set)
        self.work = collections.deque(); self.inwork = set(); self.nsteps = 0; self.nevals = 0
        self.tops = []

    def push(self, key):
        if key not in self.inwork: self.inwork.add(key); self.work.append(key)
    def add_prod(self, N, t, N2):
        s = self.prods[N]
        if (t, N2) not in s:
            s.add((t, N2))
            if len(self.prods) > self.maxnt: raise Fail(('nonterminals',))
            for u in self.udeps[N]: self.push(u)
    def unfold(self, V, user):
        self.udeps[V].add(user); return list(self.prods[V])
    def chain(self, N, toks, V2):
        cur = N
        for i, t in enumerate(toks):
            nx = V2 if i == len(toks) - 1 else ('T', N, tuple(toks[:i + 1]))
            self.add_prod(cur, t, nx); cur = nx
    def get(self, key, user):
        self.cdeps[key].add(user)
        if key not in self.C: self.C[key] = set(); self.push(key)
        return self.C[key]

    def run(self, S, cells, h, V, user, left_blank=False, is_target=None):
        T = self.T
        stack = [(S, list(cells), h, V, 0, False, False)]
        seen = set()
        while stack:
            S, cells, h, V, n, inside, ret = stack.pop()
            sk = (S, tuple(cells), h, V, inside)
            if sk in seen: continue
            seen.add(sk)
            if ret and left_blank and inside:
                lo = next((i for i, x in enumerate(cells) if x), len(cells))
                if h < lo and lo < len(cells):
                    yield (S, lo - h - 1, cells[lo:], V); continue
            while True:
                if h < 0:
                    if not left_blank:
                        yield (S, cells, V); break
                    cells.insert(0, 0); h = 0
                if h == len(cells):
                    if left_blank: inside = True
                    i0 = len(cells); z = 0
                    while z < self.J:
                        if i0 == 0:
                            if left_blank: cells.insert(0, 0); h += 1; i0 = 1
                            else: break
                        i0 -= 1
                        if cells[i0] == 0: z += 1
                    shapes = self.get((S, tuple(cells[i0:]), V), user)
                    if i0 == 0 and not left_blank and self.J:
                        for (S2, w, V2) in shapes: yield (S2, list(w), V2)
                        break
                    for (S2, w, V2) in shapes:
                        stack.append((S2, cells[:i0] + list(w), i0 - 1, V2, n + 1, inside, True))
                    break
                tr = T[(S, cells[h])]
                if tr is None: raise Fail(('halt', user, S, fmt_cells(cells), h, V))
                w, d, S2 = tr
                cells[h] = w; h += d; S = S2; n += 1; self.nsteps += 1
                if n > self.fuel: raise Fail(('fuel', user, S, fmt_cells(cells[:200]), h, V))
                if len(cells) > self.maxword: raise Fail(('long', user, S, fmt_cells(cells[:200]), h, V))
                if left_blank:
                    lo = next((i for i, x in enumerate(cells) if x), len(cells))
                    if h >= lo: inside = True
                    elif inside and d < 0:
                        if lo == len(cells): continue
                        ev = (S, lo - h - 1, cells[lo:], V)
                        if is_target is None or is_target(ev):
                            yield ev; break
                        inside = False

    def complete(self, cells, V, user):
        """make cells end at a token boundary by unfolding V if needed; strip blank"""
        if cells and cells[-1] == 1:
            out = []
            for (t, V3) in self.unfold(V, user): out += self.complete(cells + [1] * t + [0], V3, user)
            return out
        if V == 'END':
            n = len(cells)
            while n and cells[n - 1] == 0: n -= 1
            if n < len(cells): cells = cells[:n] + ([0] if n else [])
            if n == 0: cells = []
        return [(cells, V)]

    def norm(self, base, S2, cells, V2, user, L):
        res = []
        for (cs, V) in self.complete(list(cells), V2, user):
            starts = [0] + [i + 1 for i, x in enumerate(cs) if x == 0]
            ntok = len(starts) - 1
            if ntok <= L:
                res.append((S2, tuple(cs), V)); continue
            head = tuple(cs[:starts[L]])
            toks = [starts[i + 1] - starts[i] - 1 for i in range(L, ntok)]
            N = ('O',) + base + (S2, head)
            self.chain(N, toks, V)
            res.append((S2, head, N))
        return res

    def eval_contract(self, key):
        S, ctx, V = key
        res = set(self.C[key])
        base = (S, ctx, trunc(V, self.j))
        for (t, V1) in self.unfold(V, key):
            for (S2, cs, V2) in self.run(S, list(ctx) + [1] * t + [0], len(ctx), V1, key):
                for sh in self.norm(base, S2, cs, V2, key, self.L): res.add(sh)
                if len(res) > self.maxshapes: raise Fail(('shapes', key))
        return res

    def eval_top(self, key):
        _, st, gap = key
        top = ('TOP', st, gap)
        for (S2, gap2, cs, V2) in self.run(st, [0] * (gap + 1), 0, top, key, left_blank=True):
            top2 = ('TOP', S2, gap2)
            if top2 not in self.prods: self.push(('top', S2, gap2))
            for (cs2, V) in self.complete(list(cs), V2, key):
                starts = [0] + [i + 1 for i, x in enumerate(cs2) if x == 0]
                toks = [starts[i + 1] - starts[i] - 1 for i in range(len(starts) - 1)]
                self.chain(top2, toks, V)

    def solve(self, typ, seed):
        self.top0 = ('TOP', typ[0], typ[1])
        self.chain(self.top0, list(seed), 'END')
        self.push(('top', typ[0], typ[1]))
        while self.work:
            key = self.work.popleft(); self.inwork.discard(key); self.nevals += 1
            if key[0] == 'top': self.eval_top(key); continue
            res = self.eval_contract(key)
            if res != self.C[key]:
                self.C[key] = res
                for u in self.cdeps[key]: self.push(u)

    def accepts(self, toks):
        cur = {self.top0}
        for t in list(toks) + [0, 0]:
            cur = {N2 for N in cur for (t2, N2) in self.prods[N] if t2 == t}
            if not cur: return False
        return 'END' in cur

def attempt(T, typ, seed, L, J, j, **kw):
    A = SBA(T, L=L, J=J, j=j, **kw)
    t0 = time.time()
    try:
        A.solve(typ, seed); status = 'CLOSED'
    except Fail as e:
        status = 'FAIL ' + e.args[0][0]; A.fail = e.args[0]
    except RecursionError:
        status = 'FAIL recursion'
    A.time = time.time() - t0
    return A, status

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('tm'); ap.add_argument('samples'); ap.add_argument('--mirror', action='store_true')
    ap.add_argument('-L', type=int, nargs='+', default=[1]); ap.add_argument('-J', type=int, nargs='+', default=[2])
    ap.add_argument('-j', type=int, nargs='+', default=[0, 1]); ap.add_argument('--seed', type=int, default=20)
    ap.add_argument('--only', default=None); ap.add_argument('-v', action='store_true')
    a = ap.parse_args()
    T = parse_tm(a.tm, a.mirror)
    sm = load(a.samples, 0)
    types = [a.only] if a.only else None
    for typ, lists in sorted(sm.items(), key=lambda kv: -len(kv[1])):
        name = '%s,%d,%d' % (chr(65 + typ[0]), typ[1], typ[2])
        if types and name not in types: continue
        if len(lists) <= a.seed: continue
        seed = lists[a.seed]
        for J in a.J:
            for L in a.L:
                for j in a.j:
                    A, status = attempt(T, typ, seed, L, J, j)
                    print('type', name, 'seed len', len(seed), 'J', J, 'L', L, 'j', j, status, '%.1fs' % A.time, 'nonterminals', len(A.prods),
                          'contracts', len(A.C), 'shapes', sum(len(x) for x in A.C.values()), 'evals', A.nevals,
                          '' if status == 'CLOSED' else str(getattr(A, 'fail', ''))[:150])
                    sys.stdout.flush()
