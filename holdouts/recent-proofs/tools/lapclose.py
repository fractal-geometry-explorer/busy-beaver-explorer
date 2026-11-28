#!/usr/bin/env python3
"""lapclose: try to prove a 2-symbol Turing machine never halts with a lap-level, carry-annotated k-gram invariant.

A lap starts when the head stands on the outermost visited cell of the home side and steps away from it.
A row is the tape at a lap start.  Each cell is annotated with the crossing sequence (the carry) that the coming
lap leaves on its far boundary.  The invariant is the set of rows that have SOME annotation all of whose k-grams
lie in a finite set G.  The checker verifies
  (1) every k-gram of G is locally consistent with the machine (so any finite annotation built from G is the true
      lap, by the crossing-sequence argument, and the lap neither halts nor runs forever),
  (2) the first row is in the invariant,
  (3) for every annotated row over G, the row after the lap again has an annotation over G (NFA inclusion).
When (3) fails the counterexample row is simulated for one lap and its k-grams are added to G.
With J > 1 each cell carries the carries of the next J laps, which rules out rows that survive one lap but not J.
Usage: lapclose.py MACHINE SIDE(L|R) K J [SEEDSTEPS] [MAXROUNDS] [THETA] [SKIPSTEPS] [P]
P: each cell is also annotated with its distance from the lap's start cell modulo P.
SKIPSTEPS: the invariant starts from the first row after this many steps (the run before it is plain simulation).
THETA: a lap of the seed run ends only after the head has reached this fraction of the visited tape (0 = every return).
"""
import sys, time
from collections import deque

def parse(m, mirror):
    T = {}
    for s, part in enumerate(m.split('_')):
        for b in (0, 1):
            t = part[3*b:3*b+3]
            if t[0] == '-': T[(s, b)] = None
            else:
                d = 1 if t[1] == 'R' else -1
                T[(s, b)] = (int(t[0]), -d if mirror else d, ord(t[2]) - 65)
    return T

class Halt(Exception): pass
class TooLong(Exception): pass

THETA = 0.5
def run_lap(T, cells, q, cap=10**8):
    """cells[0] is the outermost visited cell (everything before it is unvisited), head there in state q,
    about to step away from home.  Returns (row, newcells, newq, steps); row = list of (c, mark, cs)."""
    tape = dict(enumerate(cells)); cs = {}
    p = 0; minp = 0; hi = len(cells) - 1; far = int(hi * THETA); s = q; n = 0; reached = far == 0
    while True:
        b = tape.get(p, 0); tr = T[(s, b)]
        if tr is None: raise Halt()
        if p == minp and tr[1] == 1 and n > 0 and reached: break
        if n == 0 and tr[1] != 1: raise ValueError('lap must start by stepping away')
        tape[p] = tr[0]; np_ = p + tr[1]; s = tr[2]
        bd = p if tr[1] == 1 else np_
        cs.setdefault(bd, []).append((s, tr[1]))
        p = np_
        if p < minp: minp = p
        if p > hi: hi = p
        if p >= far: reached = True
        n += 1
        if n > cap: raise TooLong()
    row = []
    for i in range(minp, hi + 1):
        c = 'U' if i < 0 else str(cells[i]) if i < len(cells) else 'V'
        row.append((c, q if i == 0 else -1, tuple(cs.get(i, ()))))
    newcells = [tape.get(i, 0) for i in range(minp, hi + 1)]
    return row, newcells, s, n

def first_row(T):
    tape = {}; p = 0; minp = 0; maxp = 0; s = 0
    while True:
        b = tape.get(p, 0); tr = T[(s, b)]
        if tr is None: raise Halt()
        if p == minp and tr[1] == 1: break
        tape[p] = tr[0]; p += tr[1]; s = tr[2]; minp = min(minp, p); maxp = max(maxp, p)
    return [tape.get(i, 0) for i in range(minp, maxp + 1)], s

PL1 = ('U', -1, ()); PR1 = ('V', -1, ())
J = 1
P = 1
def pads():
    return (PL1,) * J, (PR1,) * J
def isL(x): return x[:J] == (PL1,) * J
def isR(x): return x[:J] == (PR1,) * J

def cell_out(T, left, mid):
    """Local consistency of one cell given the letter to its left.  Returns (c', endmark) or None."""
    cl, ml, csl = left; c, m, csr = mid
    if c == 'U' and cl != 'U': return None
    if cl == 'V' and c != 'V': return None
    if c == 'V' and (cl == 'U' or m >= 0): return None
    if m >= 0 and (cl != 'U' or c == 'U'): return None
    if cl == 'U' and c != 'U' and m < 0: return None
    if ml >= 0 and c == 'U': return None
    pl = pr = 0; first = True
    if m >= 0: s = m
    else:
        if not csl and not csr: return (c, -1)
        lin = bool(csl) and csl[0][1] == 1; rin = bool(csr) and csr[0][1] == -1
        if lin and not rin and not (csr and csr[0][1] == -1):
            if c == 'U': return None
            s = csl[0][0]; pl = 1
        elif rin and not lin: s = csr[0][0]; pr = 1
        else: return None
        first = False
    v = 0 if c in 'UV' else int(c)
    for _ in range(100000):
        tr = T[(s, v)]
        if tr is None: return None
        if tr[1] == 1 and cl == 'U' and pl == 0 and not (first and m >= 0):
            if not csl and pr == len(csr): return (str(v), s)
        if first and tr[1] != 1: return None
        first = False
        v = tr[0]
        if tr[1] == 1:
            if pr >= len(csr) or csr[pr] != (tr[2], 1): return None
            pr += 1
            if pr == len(csr):
                if pl != len(csl): return None
                return (str(v), -1)
            if csr[pr][1] != -1: return None
            s = csr[pr][0]; pr += 1
        else:
            if pl >= len(csl) or csl[pl] != (tr[2], -1): return None
            pl += 1
            if pl == len(csl):
                if pr != len(csr): return None
                return (str(v), -1)
            if csl[pl][1] != 1: return None
            s = csl[pl][0]; pl += 1
    return None

class Closer:
    def __init__(self, T, k):
        global PL, PR
        PL, PR = pads()
        self.T = T; self.k = k; self.G = set(); self.lid = {}; self.letters = []
        self.outc = {}
    def L(self, x):
        i = self.lid.get(x)
        if i is None: i = self.lid[x] = len(self.letters); self.letters.append(x)
        return i
    def add_row(self, row):
        """row: letters (level triples..., idx)."""
        k = self.k
        i0 = row[0][-1]; i1 = row[-1][-1]
        ids = [self.L(PL + ((i0 - d) % P,)) for d in range(k, 0, -1)] + [self.L(x) for x in row] + [self.L(PR + ((i1 + d) % P,)) for d in range(1, k + 1)]
        new = 0
        for i in range(len(ids) - k + 1):
            g = tuple(ids[i:i+k])
            if g not in self.G:
                for j in range(1, k):
                    if self.out(g[j-1], g[j]) is None: raise AssertionError('inconsistent gram from a real lap: %r' % ([self.letters[x] for x in g],))
                self.G.add(g); new += 1
        return new
    def out(self, a, b):
        r = self.outc.get((a, b), 0)
        if r == 0:
            la = self.letters[a]; lb = self.letters[b]; r = None
            for l in range(J):
                o = cell_out(self.T, la[l], lb[l])
                if o is None or (l + 1 < J and (lb[l+1][0], lb[l+1][1]) != o): r = None; break
                if l == 0: r = o
            self.outc[(a, b)] = r
        return r
    def check(self, maxpairs=2000000, maxcex=50):
        """Returns list of counterexample rows (as letter lists); empty list means closed."""
        k = self.k; G = self.G
        succ = {}
        for g in G: succ.setdefault(g[:-1], []).append(g[1:])
        allst = set(succ) | {b for bs in succ.values() for b in bs}
        s0s = {a for a in allst if all(isL(self.letters[x]) for x in a)}; sFs = {a for a in allst if all(isR(self.letters[x]) for x in a)}
        # trim: forward and backward reachable
        fw = set(s0s); dq = list(s0s)
        while dq:
            a = dq.pop()
            for b in succ.get(a, ()):
                if b not in fw: fw.add(b); dq.append(b)
        pred = {}
        for a, bs in succ.items():
            for b in bs: pred.setdefault(b, []).append(a)
        bw = set(sFs); dq = list(sFs)
        while dq:
            a = dq.pop()
            for b in pred.get(a, ()):
                if b not in bw: bw.add(b); dq.append(b)
        live = fw & bw
        # shortest completion to the right pad, for turning a failing prefix into a full row
        nxt = {a: None for a in sFs}; dq2 = deque(sFs)
        while dq2:
            b = dq2.popleft()
            for a in pred.get(b, ()):
                if a in fw and a not in nxt: nxt[a] = b; dq2.append(a)
        def complete(st):
            out = []
            while nxt[st] is not None: st = nxt[st]; out.append(self.letters[st[-1]])
            return out
        states = list(live)
        sid = {s: i for i, s in enumerate(states)}
        # B transitions by read letter (c, m)
        proj = lambda x: (self.letters[x][0][0], self.letters[x][0][1])
        bt = {}
        asucc = {}
        for a in live:
            for b in succ.get(a, ()):
                if b in live:
                    bt.setdefault((sid[a], proj(b[-1])), set()).add(sid[b])
                    o = self.out(a[-1], b[-1]) if k >= 2 else None
                    asucc.setdefault(sid[a], []).append((sid[b], (o[0], o[1]), b[-1]))
        I0 = [sid[a] for a in s0s if a in sid]; IF = frozenset(sid[a] for a in sFs if a in sid)
        cex = []
        memo = {}
        def bstep(S, o):
            key = (S, o); r = memo.get(key)
            if r is None:
                acc = set()
                for b in S: acc.update(bt.get((b, o), ()))
                r = memo[key] = frozenset(acc)
            return r
        S0 = frozenset(I0)
        while True:  # the left pad is infinite: B may leave its pad at any earlier cell
            S1 = S0 | bstep(S0, ('U', -1))
            if S1 == S0: break
            S0 = S1
        seen = {(a, S0): None for a in I0}; dq = deque(seen)
        def word(node, extra):
            w = [extra] if extra is not None else []
            while seen[node] is not None:
                node, x = seen[node]; w.append(x)
            return [self.letters[x] for x in reversed(w)]
        while dq:
            node = dq.popleft(); a, S = node
            if a in IF:
                # image tail is all blank: B must be able to settle into its right pad
                X = S; vis = set(); ok = False
                while X not in vis:
                    if X & IF: ok = True; break
                    vis.add(X); X = bstep(X, ('V', -1))
                if not ok:
                    cex.append(word(node, None))
                    if len(cex) >= maxcex: break
            for b, o, x in asucc.get(a, ()):
                S2 = bstep(S, o)
                if not S2:
                    cex.append(word(node, x) + complete(states[b]))
                    if len(cex) >= maxcex: break
                    continue
                n2 = (b, S2)
                if n2 not in seen:
                    seen[n2] = (node, x); dq.append(n2)
            if len(cex) >= maxcex: break
            if len(seen) > maxpairs: return None
        self.npairs = len(seen); self.nlive = len(live)
        return cex
    def image(self, w):
        """Row after the lap described by annotated word w (letters)."""
        w = [PL + (0,)] + w + [PR + (0,)]
        cells = []; q = None
        for i in range(1, len(w)):
            o = cell_out(self.T, w[i-1][0], w[i][0])
            if o is None: raise AssertionError('inconsistent word')
            if o[1] >= 0:
                if q is not None: raise AssertionError('two end marks')
                q = o[1]; cells = []
            if q is not None:
                if o[0] != 'V': cells.append(int(o[0]))
            elif o[0] != 'U': raise AssertionError('visited cell before the end mark')
        if q is None: raise AssertionError('no end mark')
        return cells, q

def strip(row):
    while row and row[-1] == PR1: row = row[:-1]
    return row

def combine(rows):
    """rows: list of J (row, base) with base = absolute position of the row's first letter."""
    lo = min(b for _, b in rows); hi = max(b + len(r) for r, b in rows)
    out = []
    for p in range(lo, hi):
        out.append(tuple(r[p-b] if 0 <= p-b < len(r) else (PL1 if p < b else PR1) for r, b in rows) + (p % P,))
    return out

def multi(T, cells, q, cap):
    """Run J laps from a row; return the combined J-level annotated row and the total number of steps."""
    rows = []; base = 0; tot = 0
    for _ in range(J):
        row, cells, q, n = run_lap(T, cells, q, cap)
        u = sum(1 for x in row if x[0] == 'U'); rows.append((strip(row), base - u)); base -= u; tot += n
    return combine(rows), tot

def main():
    global J, THETA, P
    m = sys.argv[1]; side = sys.argv[2]; k = int(sys.argv[3]); J = int(sys.argv[4])
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 2000000
    rounds = int(sys.argv[6]) if len(sys.argv) > 6 else 200
    if len(sys.argv) > 7: THETA = float(sys.argv[7])
    skip = int(sys.argv[8]) if len(sys.argv) > 8 else 0
    P = int(sys.argv[9]) if len(sys.argv) > 9 else 1
    T = parse(m, side == 'R'); C = Closer(T, k)
    t0 = time.time()
    cells, q = first_row(T); steps = 0; laps = 0; maxlap = 1; win = deque(); base = 0
    while steps < seed:
        row, cells, q, n = run_lap(T, cells, q)
        u = sum(1 for x in row if x[0] == 'U'); win.append((strip(row), base - u)); base -= u
        if len(win) == J:
            if steps >= skip: C.add_row(combine(list(win)))
            win.popleft()
        steps += n; laps += 1; maxlap = max(maxlap, n)
    print('seed: %d laps, %d steps, %d letters, %d %d-grams, %.0fs' % (laps, steps, len(C.letters), len(C.G), k, time.time()-t0), flush=True)
    for r in range(rounds):
        cex = C.check()
        if cex is None: print('RESULT blowup (subset construction too large)'); return
        if not cex:
            print('RESULT CLOSED P=%d k=%d j=%d theta=%g grams=%d letters=%d live=%d pairs=%d rounds=%d %.0fs' % (P, k, J, THETA, len(C.G), len(C.letters), C.nlive, C.npairs, r, time.time()-t0)); return
        added = 0
        for w in cex:
            cells2, q2 = C.image(w)
            try: row, n = multi(T, cells2, q2, 50*maxlap+100000)
            except Halt:
                print('RESULT abstract-halt round=%d grams=%d' % (r, len(C.G))); return
            except TooLong:
                print('RESULT abstract-long round=%d grams=%d' % (r, len(C.G))); return
            added += C.add_row(row)
        print('round %d: %d counterexamples, +%d grams, total %d, pairs %d, %.0fs' % (r, len(cex), added, len(C.G), getattr(C, 'npairs', 0), time.time()-t0), flush=True)
        if added == 0: print('RESULT stuck (counterexample adds nothing)'); return
    print('RESULT open after %d rounds, grams=%d' % (rounds, len(C.G)))
main()
