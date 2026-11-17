"""Accelerated simulator for 1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB.

At a tick start the head, in A, reads 0 at the base cell b and turns right onto a 1.  Between rebuilds the cells
that change from one tick start to the next are the digits of two binary counters: L, digit pairs left of b (both
cells of a pair 00 or 11), and R, single cells right of b; every tick adds one to both.  The digit positions are
learned from the run (a carry into a cell not yet known is simulated directly and the new digits are appended), and
a tick costs G(k) steps left of b plus F(j) steps at or right of b, k and j the carry lengths of L and R; G and F are
learned from directly simulated ticks and checked on every later one.  Runs of ticks in which no carry leaves the
known digits are applied arithmetically; everything else (new digits, overflows, rebuilds) is simulated cell by cell.

A halt can only happen at the right end of the tape (D on 0, reached from F on 0 then E on 0); a tick applied
arithmetically never moves the head beyond the known digits, so the right end is only ever visited by directly
simulated steps.  `run` records every arrival of the head on a blank cell right of the last 1, with its state.

usage:
  python3 accel.py run TMAX [EVENTS_OUT]    run to TMAX steps, print a summary and the right-end arrivals
  python3 accel.py cert TMAX CERT_OUT       run to TMAX steps and write the certificate for lean/Cert.lean
  python3 accel.py check EVENTS             compare with the events of `tmrun MACHINE N at C L` where C reads 0
                                            (exact steps, z and W)
"""
import sys
from collections import Counter
M = "1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB"

def table(m):
    T = {}
    for i, s in enumerate(m.split('_')):
        for r in (0, 1):
            t = s[3*r:3*r+3]
            T[(i, r)] = None if t[2] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return T

class Halt(Exception): pass

def tz1(x):
    k = 0
    while x & 1: x >>= 1; k += 1
    return k

def count_ge(a, b, j):
    """#{t in [a, b): t has at least j trailing ones}"""
    if j == 0: return b - a
    p = 1 << j
    return b // p - a // p

def digits(cells):
    r = list(cells) + ([0] if len(cells) % 2 else [])
    return ''.join({(1, 0): '0', (1, 1): '1', (0, 0): '_', (0, 1): 'x'}[(r[i], r[i+1])] for i in range(0, len(r), 2))

class Acc:
    def __init__(s, m=M, log=print, zmin=5, verbose=False):
        s.T = table(m)
        s.c = {}; s.h = 0; s.q = 0; s.t = 0; s.lo = 0; s.hi = 0
        s.log = log; s.zmin = zmin; s.events = []; s.verbose = verbose
        s.batches = []; s.checks = 0; s.bad = 0; s.direct = 0; s.regimes = 0; s.left_steps = 0; s.base = None
    def get(s, p): return s.c.get(p, 0)
    def put(s, p, v):
        if v: s.c[p] = 1
        else: s.c.pop(p, None)
    def step(s):
        r = s.c.get(s.h, 0); a = s.T[(s.q, r)]
        if a is None: raise Halt(s.t + 1)
        w, d, q = a
        if w: s.c[s.h] = 1
        elif r: del s.c[s.h]
        h0 = s.h
        if s.base is not None and h0 < s.base: s.left_steps += 1
        s.h += d; s.q = q; s.t += 1; s.direct += 1
        if s.h < s.lo:
            s.lo = s.h
            if q == 2: s.record_event()
        if s.h > s.hi: s.hi = s.h
        return h0, r
    def record_event(s):
        if s.get(s.h) != 0: s.events.append((s.t, None, None)); return
        p = s.h + 1; z = 0
        while s.get(p) == 1 and s.get(p + 1) == 0: z += 1; p += 2
        hi = max(s.c)
        W = digits([s.get(j) for j in range(p, hi + 1)])
        s.events.append((s.t, z, W))
        if s.verbose: s.log('E', s.t, z, W)
        if getattr(s, 'evf', None): s.evf.write('%d %d %s\n' % (s.t, z, W)); s.evf.flush()
    def run_until(s, cond, maxsteps):
        for _ in range(maxsteps):
            q0 = s.q
            h0, r0 = s.step()
            if cond(h0, q0, r0): return True
        return False
    def is_turn(s, h0, q0, r0):
        return q0 == 0 and r0 == 0 and s.h == h0 + 1 and s.get(s.h) == 1
    def main(s, tmax=None, emax=None):
        # Wait for an overflow event with z >= zmin, so that the shuttle has settled, then take the most frequent
        # tick start of the next 64 as the base.  When a regime of many ticks ends (the base has moved), look for the
        # new base at once without waiting: the next event may be 2^z ticks away.
        wait = True
        while (tmax is None or s.t < tmax) and (emax is None or len(s.events) < emax):
            s.base = None
            ne = len(s.events)
            if wait:
                s.run_until(lambda h0, q0, r0: len(s.events) > ne and s.events[-1][1] is not None and s.events[-1][1] >= s.zmin and s.h == s.lo, 10**13)
            wait = True
            cnt = Counter(); nt = [0]
            def turn(h0, q0, r0):
                if s.is_turn(h0, q0, r0):
                    cnt[h0] += 1; nt[0] += 1
                    return nt[0] >= 64
            if not s.run_until(turn, 10**7): continue
            b = cnt.most_common(1)[0][0]
            if not s.run_until(lambda h0, q0, r0: h0 == b and s.is_turn(h0, q0, r0), 10**7): continue
            s.regimes += 1
            s.loops = 0
            s.regime(b, tmax)
            wait = s.loops < 16
    def direct_tick(s, b, maxsteps=10**7):
        t0 = s.t; l0 = s.left_steps
        ok = s.run_until(lambda h0, q0, r0: h0 == b and s.is_turn(h0, q0, r0), maxsteps)
        return ((s.t - t0) - (s.left_steps - l0), s.left_steps - l0) if ok else None
    def cells(s, b):
        lo = min(s.lo, min(s.c) if s.c else 0); hi = max(s.c) if s.c else 0
        return {p: s.get(p) for p in range(lo, hi + 3) if p != b}
    def regime(s, b, tmax):
        s.base = b
        Ls = []  # left cell of each L digit pair, from b outwards
        Rs = []  # R digit cells, from b outwards
        G = {}; F = {}  # carry length -> steps left of b / at or right of b
        while tmax is None or s.t < tmax:
            s.loops += 1
            L = sum(s.get(p) << i for i, p in enumerate(Ls)); R = sum(s.get(p) << i for i, p in enumerate(Rs))
            nl, nr = len(Ls), len(Rs)
            ks = next((x for x in range(nl) if x not in G), nl)
            js = next((x for x in range(nr) if x not in F), nr)
            dl = ((1 << ks) - 1 - L) % (1 << ks) if ks < nl else (1 << nl) - 1 - L
            dr = ((1 << js) - 1 - R) % (1 << js) if js < nr else (1 << nr) - 1 - R
            if True:  # noqa
                d = min(dl, dr)
                if d > 0:
                    cost = 0
                    for k in range(nl):
                        nk = count_ge(L, L + d, k) - count_ge(L, L + d, k + 1)
                        if nk: cost += G[k] * nk
                    for j in range(nr):
                        nj = count_ge(R, R + d, j) - count_ge(R, R + d, j + 1)
                        if nj: cost += F[j] * nj
                    L2, R2 = L + d, R + d
                    for i, p in enumerate(Ls): s.put(p, (L2 >> i) & 1); s.put(p + 1, (L2 >> i) & 1)
                    for i, p in enumerate(Rs): s.put(p, (R2 >> i) & 1)
                    s.batches.append((s.t, b, list(Ls), list(Rs), d, cost))
                    s.t += cost; L, R = L2, R2
            k = tz1(L) if L != (1 << nl) - 1 else None
            j = tz1(R) if R != (1 << nr) - 1 else None
            before = s.cells(b)
            res = s.direct_tick(b)
            if res is None:
                if s.verbose: s.log('regime ends (no tick start) at', s.t)
                return
            fr, gl = res
            after = s.cells(b)
            ch = sorted(p for p in set(before) | set(after) if before.get(p, 0) != after.get(p, 0))
            lch = [p for p in ch if p < b]; rch = [p for p in ch if p > b]
            # ---- right side
            okr = True; exp = set()
            if j is not None:
                exp = {Rs[i] for i in range(j + 1)}
                okr = set(rch) == exp
            else:
                new = [p for p in rch if p not in set(Rs)]
                if set(Rs) <= set(rch) and new and all(p > (Rs[-1] if Rs else b) for p in new) \
                        and all(s.get(p) == 0 for p in new[:-1]) and s.get(new[-1]) == 1:
                    Rs += new; j = len(Rs) - 1
                else:
                    okr = False
            if not okr:
                if s.verbose: s.log('R template change at', s.t, [p - b for p in rch][:16])
                bad = [p for p in rch if p not in exp]
                lowest = min(bad) if bad else b
                Rs = [p for p in Rs if p < lowest]; F = {x: F[x] for x in F if x < len(Rs)}
                j = None
            # ---- left side (pairs)
            okl = True; expl = set()
            if k is not None:
                for i in range(k + 1): expl |= {Ls[i], Ls[i] + 1}
                okl = set(lch) == expl
            else:
                known = set()
                for p in Ls: known |= {p, p + 1}
                new = [p for p in lch if p not in known]
                newp = sorted({p if (p - b) % 2 == 0 else p - 1 for p in new}, reverse=True)
                if known <= set(lch) and newp and all(p < (Ls[-1] if Ls else b) for p in newp) \
                        and all(s.get(p) == s.get(p + 1) for p in newp) and set(new) == {x for p in newp for x in (p, p + 1)} \
                        and all(s.get(p) == 0 for p in newp[:-1]) and s.get(newp[-1]) == 1:
                    Ls += newp; k = len(Ls) - 1
                else:
                    okl = False
            if not okl:
                if s.verbose: s.log('L template change at', s.t, [p - b for p in lch][:16])
                bad = [p for p in lch if p not in expl]
                highest = max(bad) if bad else b
                Ls = [p for p in Ls if p > highest + 1]; G = {x: G[x] for x in G if x < len(Ls)}
                k = None
            # ---- costs
            if k is not None:
                if k in G:
                    s.checks += 1
                    if G[k] != gl: s.bad += 1; s.log('G mismatch', s.t, k, G[k], gl); G.pop(k)
                else: G[k] = gl
            if j is not None:
                if j in F:
                    s.checks += 1
                    if F[j] != fr: s.bad += 1; s.log('F mismatch', s.t, j, F[j], fr); F.pop(j)
                else: F[j] = fr



def write_cert(batches, path):
    """The certificate checked by lean/Cert.lean, from the batches of a run.

    Lean's checker keeps the configuration as two lists, the cells left of the head (nearest first) and the head
    cell with the cells right of it.  A tick start there is the head on the base cell b in A, one step before the
    moment the batches are recorded at (the head on b + 1 in B).  Operations:
      D n          n plain steps
      L m g... ;   left layout: keep its first m entries, then g...; the layout is the length of the first gap
                   (cells from the head outwards before the first digit pair) and of the gaps between digit pairs
      R m g... ;   the same for the right side (cells after the base cell, single digits)
      B d          d ticks
    Returns the number of steps the certificate reaches."""
    out = []; t = 0; cur = {'L': [], 'R': []}
    for (tb, b, Ls, Rs, d, cost) in batches:
        start = tb - 1
        if start > t: out.append('D %d' % (start - t))
        Lpos = [b - 2 - p for p in Ls]; Rpos = [x - b - 1 for x in Rs]
        new = {'L': [Lpos[0]] + [y - x - 2 for x, y in zip(Lpos, Lpos[1:])],
               'R': [Rpos[0]] + [y - x - 1 for x, y in zip(Rpos, Rpos[1:])]}
        for tag in 'LR':
            if cur[tag] != new[tag]:
                m = 0
                while m < min(len(cur[tag]), len(new[tag])) and cur[tag][m] == new[tag][m]: m += 1
                out.append('%s %d %s ;' % (tag, m, ' '.join(map(str, new[tag][m:]))))
        cur = new
        out.append('B %d' % d)
        t = start + cost
    with open(path, 'w') as f: f.write('\n'.join(out) + '\n')
    return t


class Edges(Acc):
    """Acc that records each step onto a blank cell right of every 1: (step, state letter, last 24 cells)."""
    def __init__(s, *a, **k):
        super().__init__(*a, **k); s.edges = []
    def step(s):
        h0 = s.h
        r = super().step()
        if s.h > h0 and s.h >= s.hi and s.get(s.h) == 0 and s.h > max(s.c, default=0):
            s.edges.append((s.t, 'ABCDEF'[s.q], ''.join(str(s.get(p)) for p in range(s.h - 24, s.h))))
        return r


def main():
    import time
    from collections import Counter
    if len(sys.argv) >= 3 and sys.argv[1] == 'run':
        a = Edges(log=print)
        if len(sys.argv) > 3: a.evf = open(sys.argv[3], 'w')
        t0 = time.time()
        try: a.main(tmax=float(sys.argv[2]))
        except Halt as h: print('HALT at step', h)
        zs = [e for e in a.events if e[1] is not None]
        print('steps %d (%.3g), events %d, directly simulated steps %d, cost checks %d, mismatches %d, %.1fs'
              % (a.t, a.t, len(a.events), a.direct, a.checks, a.bad, time.time() - t0))
        print('rebuilds (z falls):', sum(1 for x, y in zip(zs, zs[1:]) if y[1] < x[1]),
              ' last z', zs[-1][1] if zs else None, ' W digits', len(zs[-1][2]) if zs else None)
        print('right-end arrivals by state:', dict(Counter(e[1] for e in a.edges)))
        for e in a.edges[-9:]: print('  %.6g %s ...%s' % e)
    elif len(sys.argv) == 4 and sys.argv[1] == 'cert':
        a = Acc(log=print)
        try: a.main(tmax=float(sys.argv[2]))
        except Halt as h: print('HALT at step', h); sys.exit(1)
        n = write_cert(a.batches, sys.argv[3])
        print('certificate: %d batches, %d steps (%.4g)' % (len(a.batches), n, n))
    elif len(sys.argv) == 3 and sys.argv[1] == 'check':
        sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
        from overflows import read_events
        ref = [(t, z, W) for t, r, z, W, _ in read_events(sys.argv[2]) if r == 0]  # C on 0 at the left end
        a = Acc(log=print)
        try: a.main(tmax=ref[-1][0] + 1)
        except Halt as h: print('HALT at step', h)
        got = [e for e in a.events if e[1] is not None][:len(ref)]
        bad = [(x, y) for x, y in zip(ref, got) if x != y]
        print('%d reference events, %d produced, %d differ, %d cost checks, %d mismatches'
              % (len(ref), len(got), len(bad) + abs(len(ref) - len(got)), a.checks, a.bad))
        for x, y in bad[:5]: print('  ref', x[:2], 'got', y[:2])
        sys.exit(1 if bad or len(got) < len(ref) or a.bad else 0)
    else:
        print(__doc__); sys.exit(2)


if __name__ == '__main__':
    main()
