#!/usr/bin/env python3
"""contractsat: ask a SAT solver for a contract table that proves a machine never halts.

The proof object (see ../../followup/write-only-test.md, last sections):

  * n classes of half tapes (the tape right of a boundary), class 0 = blank;
  * phi(cell, class) -> class, with phi(0, 0) = 0, so the classes are the states of an automaton that reads a
    half tape from its far end;
  * R[q][s] = set of (s', q'): if the head enters a half tape of class q in state s (on its first cell), it can
    only come back out in a state s' leaving a half tape of class q';
  * a window of W exact cells at the left frontier of the tape (blank to its left), followed by a half tape that
    is known only by its class.  The window slides left with the frontier; the cell that drops out on its right
    is absorbed into the class by phi.  A step out of the right end of the window is a call answered by R.

Constraints: R is closed under "one cell in front" (a call on c.t is the cell c making calls on t), no halting
transition is reachable inside a reachable call, and no halting transition is reachable in the window graph
from the blank tape.  The table need not be least: the solver may merge tapes that behave differently.

The window graph is encoded lazily: a window configuration gets a variable and its clauses only once some model
reaches it, so an UNSAT answer is still exact for the given (n, W).

With mirror = R the tape is mirrored first (window at the right end, classes for the half tape on the left).

usage: contractsat.py MACHINE L|R n W [--out cert.json] [--solver cadical153] [--sym] [--seed k]
"""
import sys, json, time, argparse
from pysat.solvers import Solver


def parse(m, mirror=False):
    t = {}
    for i, p in enumerate(m.split('_')):
        for b in (0, 1):
            x = p[3 * b:3 * b + 3]
            if x[0] == '-':
                t[(i, b)] = None
            else:
                d = 1 if x[1] == 'R' else -1
                if mirror:
                    d = -d
                t[(i, b)] = (int(x[0]), d, ord(x[2]) - 65)
    return t


class Enc:
    def __init__(self, machine, mirror, n, W, solver='cadical153', sym=False, verbose=True, runs=None, keys=None):
        self.machine, self.mirror, self.n, self.W = machine, mirror, n, W
        self.t = parse(machine, mirror)
        self.S = len(machine.split('_'))
        self.nv = 0
        self.sol = Solver(name=solver)
        self.ncl = 0
        self.verbose = verbose
        self.X = {}          # window config -> var
        self.expanded = set()
        self.cap = 200000
        self.big = 0
        self.wcache = {}
        self.stepcap = 20000
        self.capped = 0
        self.runs = runs
        self.keys = keys     # allowed window situations (word, pos, state), or None for no restriction
        if runs:
            b, Z, D = runs
            self.n = n = D * (Z + 1) + 1 + (1 if b == 0 else 0)
        self.build(sym)

    def new(self):
        self.nv += 1
        return self.nv

    def add(self, cl):
        self.sol.add_clause(cl)
        self.ncl += 1

    def build(self, sym):
        n, S, t = self.n, self.S, self.t
        rg = range(n)
        ret = sorted({v[2] for v in t.values() if v and v[1] < 0})   # states in which the head can step left
        self.ret = ret
        self.F = F = [[[self.new() for p in rg] for q in rg] for c in (0, 1)]
        self.R = R = [[[[self.new() for q2 in rg] for s2 in range(S)] for s in range(S)] for q in rg]
        self.T = T = [[[[[self.new() for p in rg] for s2 in range(S)] for s in range(S)] for q in rg] for c in (0, 1)]
        self.C = C = [[[self.new() for s in range(S)] for q in rg] for c in (0, 1)]
        self.CC = CC = [[self.new() for s in range(S)] for q in rg]
        # phi is a function
        for c in (0, 1):
            for q in rg:
                self.add(F[c][q][:])
                for p in rg:
                    for p2 in range(p + 1, n):
                        self.add([-F[c][q][p], -F[c][q][p2]])
        self.add([F[0][0][0]])
        for c in (0, 1):
            for q in rg:
                for s in range(S):
                    # 1. a call on class p = phi(c,q) is the cell c in front of q
                    for p in rg:
                        f = F[c][q][p]
                        self.add([-CC[p][s], -f, C[c][q][s]])
                        for s2 in ret:
                            for p2 in rg:
                                self.add([-T[c][q][s][s2][p2], -f, R[p][s][s2][p2]])
                    tr = t[(s, c)]
                    if tr is None:
                        self.add([-C[c][q][s]])
                        continue
                    w, d, s3 = tr
                    if d < 0:
                        for p2 in rg:
                            self.add([-F[w][q][p2], T[c][q][s][s3][p2]])
                    else:
                        self.add([-C[c][q][s], CC[q][s3]])
                        for s4 in ret:
                            for q2 in rg:
                                r = R[q][s3][s4][q2]
                                self.add([-C[c][q][s], -r, C[w][q2][s4]])
                                for s2 in ret:
                                    for p2 in rg:
                                        self.add([-r, -T[w][q2][s4][s2][p2], T[c][q][s][s2][p2]])
        if sym and not self.runs:
            self.symbreak()
        if self.runs:
            self.structure()
        try:
            self.sol.set_phases([-v for v in range(1, self.nv + 1)])
        except Exception:
            pass
        # start: blank window, head at its left end... the head starts at window position 0
        x0 = self.xvar(((0,) * self.W, 0, 0, 0))
        self.add([x0])
        if self.keys is not None:      # the whole window graph at once
            for k in sorted(self.keys):
                for q in range(self.n):
                    self.expand(k + (q,))

    def structure(self):
        """Run-length structure: a class is (d, z) = (automaton state d, z leading cells equal to b), z <= Z.
        phi(b, (d,z)) = (d, z+1), phi(b, (d,Z)) = sink, phi(1-b, x) is some (d', 0) or the sink; sink is closed.
        For b = 0 the blank half tape is an extra class 0; for b = 1 it is (0, 0) with phi(0, (0,0)) = (0,0)."""
        b, Z, D = self.runs
        n, F = self.n, self.F
        off = 1 if b == 0 else 0
        cls = lambda d, z: off + d * (Z + 1) + z
        sink = n - 1
        for c in (0, 1):
            self.add([F[c][sink][sink]])
        for d in range(D):
            for z in range(Z + 1):
                self.add([F[b][cls(d, z)][cls(d, z + 1) if z < Z else sink]])
        heads = [cls(d, 0) for d in range(D)] + [sink]
        srcs = [cls(d, z) for d in range(D) for z in range(Z + 1)] + ([0] if b == 0 else [])
        for q in srcs:
            for p in range(n):
                if p not in heads:
                    self.add([-F[1 - b][q][p]])
        # symmetry: automaton states d are numbered in order of first use by the sources in order
        # (weak form: phi(1-b, blank) is state 0 or 1)
        first = 0 if b == 0 else cls(0, 0)
        for d in range(2 if b == 0 else 2, D):
            self.add([-F[1 - b][first][cls(d, 0)]])

    def symbreak(self):
        # classes other than 0 are numbered in the order a breadth-first search over phi finds them
        # (order of the pairs (q, c): (0,1), (1,0), (1,1), (2,0), ...).  Unreachable classes come last.
        n, F = self.n, self.F
        pairs = [(0, 1)] + [(q, c) for q in range(1, n) for c in (0, 1)]
        # m[i][k] : max class among targets of pairs[0..i] is >= k
        prev = None
        for i, (q, c) in enumerate(pairs):
            cur = [None] * n
            for k in range(1, n):
                v = self.new()
                cur[k] = v
                # v <-> prev[k] or F[c][q][>=k]
                ge = [F[c][q][p] for p in range(k, n)]
                self.add([-v] + ge + ([prev[k]] if prev else []))
                for g in ge:
                    self.add([-g, v])
                if prev:
                    self.add([-prev[k], v])
            # target of this pair may be at most (max so far) + 1
            for k in range(2, n):
                if prev:
                    self.add([-F[c][q][k], prev[k - 1]])
                else:
                    self.add([-F[c][q][k]])
            # a class q is only expanded if it has been reached: pair (q, c) with q >= 1 needs max so far >= q
            prev = cur

    def xvar(self, cfg):
        v = self.X.get(cfg)
        if v is None:
            v = self.X[cfg] = self.new()
        return v

    def run_window(self, cfg):
        """Run exactly inside the window. Returns ('halt',) | ('loop',) | ('right', word, s3) | ('left', word, s3)."""
        word, pos, s, q = cfg
        if self.keys is not None and (word, pos, s) not in self.keys:
            return ('halt',)       # outside the allowed situations: treated like a halt (sound, only stricter)
        word = list(word)
        W, t = self.W, self.t
        seen = set()
        steps = 0
        while True:
            key = (tuple(word), pos, s)
            if key in seen:
                return ('loop',)
            seen.add(key)
            steps += 1
            if steps > self.stepcap:      # too long to follow: treated like a halt (sound, only stricter)
                self.capped += 1
                return ('halt',)
            tr = t[(s, word[pos])]
            if tr is None:
                return ('halt',)
            w, d, s3 = tr
            word[pos] = w
            pos += d
            s = s3
            if pos < 0:
                return ('left', tuple(word), s)
            if pos >= W:
                return ('right', tuple(word), s)

    def expand(self, cfg):
        """Add the clauses of one window configuration."""
        self.expanded.add(cfg)
        x = self.xvar(cfg)
        q = cfg[3]
        n, S, W = self.n, self.S, self.W
        res = self.run_window(cfg)
        if res[0] == 'halt':
            self.add([-x])
        elif res[0] == 'right':
            _, word, s3 = res
            self.add([-x, self.CC[q][s3]])
            for s4 in self.ret:
                for q2 in range(n):
                    self.add([-x, -self.R[q][s3][s4][q2], self.xvar((word, W - 1, s4, q2))])
        elif res[0] == 'left':
            _, word, s3 = res
            c = word[-1]
            nw = (0,) + word[:-1]
            for p in range(n):
                self.add([-x, -self.F[c][q][p], self.xvar((nw, 0, s3, p))])

    def model_tables(self, model):
        val = lambda v: model[v - 1] > 0
        n, S = self.n, self.S
        phi = [[next(p for p in range(n) if val(self.F[c][q][p])) for q in range(n)] for c in (0, 1)]
        R = {}
        for q in range(n):
            for s in range(S):
                R[(q, s)] = [(s2, q2) for s2 in range(S) for q2 in range(n) if val(self.R[q][s][s2][q2])]
        return phi, R

    def lfp(self, phi):
        """Least R closed under the cell rules, for a given phi."""
        n, S, t = self.n, self.S, self.t
        T = {(c, q, s): set() for c in (0, 1) for q in range(n) for s in range(S)}
        R = {(q, s): set() for q in range(n) for s in range(S)}
        ch = True
        while ch:
            ch = False
            for (c, q, s), cur in T.items():
                tr = t[(s, c)]
                if tr is None:
                    continue
                w, d, s3 = tr
                if d < 0:
                    new = {(s3, phi[w][q])}
                else:
                    new = set()
                    for (s4, q2) in R[(q, s3)]:
                        new |= T[(w, q2, s4)]
                if not new <= cur:
                    cur |= new
                    ch = True
                r = R[(phi[c][q], s)]
                if not cur <= r:
                    r |= cur
                    ch = True
        return R

    def reach(self, phi, R, cap=None, cc=None):
        """Breadth-first search of the window graph under a model.
        Returns (seen, path, complete): `path` is a shortest path from the start to a configuration that halts
        in the window (None if there is none among the first `cap` configurations); `complete` says that the
        whole reachable set was visited."""
        from collections import deque
        W = self.W
        start = ((0,) * W, 0, 0, 0)
        par = {start: None}
        st = deque([start])
        while st:
            cfg = st.popleft()
            res = self.wcache.get(cfg[:3])
            if res is None:
                res = self.wcache[cfg[:3]] = self.run_window(cfg)
            q = cfg[3]
            nxt = ()
            if res[0] == 'halt' or (res[0] == 'right' and cc is not None and (q, res[2]) not in cc):
                # a halt in the window, or a call that the model has not marked as reachable
                path = []
                while cfg is not None:
                    path.append(cfg)
                    cfg = par[cfg]
                return par, path[::-1], False
            if res[0] == 'right':
                _, word, s3 = res
                nxt = [(word, W - 1, s4, q2) for (s4, q2) in R[(q, s3)]]
            elif res[0] == 'left':
                _, word, s3 = res
                nxt = [((0,) + word[:-1], 0, s3, phi[word[-1]][q])]
            for c in nxt:
                if c not in par:
                    par[c] = cfg
                    st.append(c)
            if cap and len(par) > cap:
                return par, None, False
        return par, None, True

    def solve(self, max_rounds=10 ** 9, tlimit=None):
        t0 = time.time()
        rnd = 0
        while rnd < max_rounds:
            rnd += 1
            ok = self.sol.solve()
            if not ok:
                if self.verbose:
                    print(f'# n={self.n} W={self.W}: UNSAT after {rnd} rounds, {len(self.expanded)} window configs, '
                          f'{self.ncl} clauses, {time.time() - t0:.1f}s', flush=True)
                return None
            model = self.sol.get_model()
            phi, R = self.model_tables(model)
            cc = {(q, s) for q in range(self.n) for s in range(self.S) if model[self.CC[q][s] - 1] > 0}
            Rl = self.lfp(phi)
            seen, path, complete = self.reach(phi, Rl, cap=self.cap, cc=cc)
            if path is not None:
                new = [c for c in path if c not in self.expanded]
                assert new, path
            elif complete:
                new = []
            else:      # graph too large to finish: add clauses for the first unexpanded configurations found
                new = [c for c in seen if c not in self.expanded][:2000]
                self.big += 1
                if not new:
                    self.cap *= 2
                    continue
            if not new:
                if self.verbose:
                    print(f'# n={self.n} W={self.W}: SAT after {rnd} rounds, {len(seen)} reachable window configs '
                          f'({len(self.expanded)} expanded), {self.ncl} clauses, {time.time() - t0:.1f}s', flush=True)
                return self.certificate(model, phi, seen)
            for c in new:
                self.expand(c)
            if self.verbose and (rnd % 25 == 0):
                print(f'#   round {rnd}: {len(self.expanded)} window configs, {self.big} big, {self.ncl} clauses, '
                      f'{time.time() - t0:.1f}s', flush=True)
            if tlimit and time.time() - t0 > tlimit:
                print(f'# n={self.n} W={self.W}: TIMEOUT after {rnd} rounds, {len(self.expanded)} window configs',
                      flush=True)
                return 'timeout'
        return 'timeout'

    def certificate(self, model, phi, seen):
        """Certificate with the least tables for phi (not the solver's, which may hold more)."""
        n, S, t, W = self.n, self.S, self.t, self.W
        R = self.lfp(phi)
        T = {}
        for c in (0, 1):
            for q in range(n):
                for s in range(S):
                    tr = t[(s, c)]
                    if tr is None:
                        continue
                    w, d, s3 = tr
                    pass
        T = {(c, q, s): set() for c in (0, 1) for q in range(n) for s in range(S)}
        ch = True
        while ch:
            ch = False
            for (c, q, s), cur in T.items():
                tr = t[(s, c)]
                if tr is None:
                    continue
                w, d, s3 = tr
                new = {(s3, phi[w][q])} if d < 0 else set().union(*[T[(w, q2, s4)] for (s4, q2) in R[(q, s3)]])
                if not new <= cur:
                    cur |= new
                    ch = True
        # calls reachable from the window graph
        CC = set()
        for cfg in seen:
            res = self.run_window(cfg)
            if res[0] == 'right':
                CC.add((cfg[3], res[2]))
        C = set()
        pre = {}
        for c in (0, 1):
            for q in range(n):
                pre.setdefault(phi[c][q], []).append((c, q))
        st = list(CC)
        seenC = set()
        work = [(c, q, s) for (p, s) in CC for (c, q) in pre.get(p, [])]
        while work:
            x = work.pop()
            if x in C:
                continue
            C.add(x)
            c, q, s = x
            tr = t[(s, c)]
            assert tr is not None, 'halt inside a call: model and least table disagree'
            w, d, s3 = tr
            if d > 0:
                if (q, s3) not in CC:
                    CC.add((q, s3))
                    work += [(c2, q2, s3) for (c2, q2) in pre.get(q, [])]
                for (s4, q2) in R[(q, s3)]:
                    work.append((w, q2, s4))
        # a call marked later may add returns that were already used: C is closed because R is final here
        return dict(machine=self.machine, side='R' if self.mirror else 'L', n=n, W=W, phi=phi,
                    runs=list(self.runs) if self.runs else None,
                    R=sorted([q, s, s2, q2] for (q, s), v in R.items() for (s2, q2) in v),
                    T=sorted([c, q, s, s2, p] for (c, q, s), v in T.items() for (s2, p) in v),
                    C=sorted(map(list, C)), CC=sorted(map(list, CC)),
                    window=[[''.join(map(str, w)), pos, s, q] for (w, pos, s, q) in sorted(seen)])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('machine')
    ap.add_argument('side', choices=['L', 'R'])
    ap.add_argument('n', type=int)
    ap.add_argument('W', type=int)
    ap.add_argument('--out')
    ap.add_argument('--solver', default='cadical153')
    ap.add_argument('--sym', action='store_true')
    ap.add_argument('--tlimit', type=float)
    ap.add_argument('--keys', help='file from ./keys: only these window situations may occur')
    ap.add_argument('--runs', help='b,Z,D: run-length structured classes (n is then ignored)')
    a = ap.parse_args()
    runs = tuple(map(int, a.runs.split(','))) if a.runs else None
    keys = None
    if a.keys:
        keys = set()
        for l in open(a.keys):
            f = l.split()
            keys.add((tuple(map(int, f[0])), int(f[1]), int(f[2])))
    e = Enc(a.machine, a.side == 'R', a.n, a.W, solver=a.solver, sym=a.sym, runs=runs, keys=keys)
    a.n = e.n
    cert = e.solve(tlimit=a.tlimit)
    if isinstance(cert, dict):
        print('CERT', a.machine, a.side, 'n=%d W=%d' % (a.n, a.W), 'facts R=%d' % len(cert['R']),
              'calls=%d' % len(cert['CC']), 'window=%d' % len(cert['window']))
        if a.out:
            json.dump(cert, open(a.out, 'w'))
    elif cert is None:
        print('NONE', a.machine, a.side, 'n=%d W=%d' % (a.n, a.W))
    else:
        print('TIMEOUT', a.machine, a.side, 'n=%d W=%d' % (a.n, a.W))


if __name__ == '__main__':
    main()
