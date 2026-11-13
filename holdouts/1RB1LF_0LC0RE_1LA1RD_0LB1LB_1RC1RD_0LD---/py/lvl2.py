"""lvl2.py MACHINE K MAXSTEPS [MODE] [SECONDS]: an exact simulator with two levels of acceleration.

Level 1 is the macro simulator of holdouts/1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA/c/msim.c, step for step: the
tape is two stacks of runs (word of K cells, count), one macro step runs the machine on a window of two blocks, and
a run of copies of one word that the head crosses in a steady state is crossed at once.

Level 2: after every macro step the shape (state, side, the words of all runs, without the counts) is looked up.
If the same shape was seen p macro steps ago and the counts differ by a vector d, the p macro steps are replayed
with the changing counts as unknowns x.  The replay takes the same branch as the real run at every test of a count
("is it 1, or at least 2"), and records each such test as an inequality f(x) >= 2 with f linear.  If the replay ends
in the same shape with counts x + d (and the other counts unchanged), then for every x satisfying the inequalities
p macro steps turn x into x + d.  So the cycle is applied n times at once, n the largest number for which the
inequalities hold at x, x + d, ..., x + (n-1) d.  The steps of one cycle are linear in x, so the steps of n cycles
are an exact sum.  Nothing is guessed: a cycle is applied only when the replay proves it for all n iterations.
(A cycle with no shrinking inequality would repeat for ever, a proof of non-halting; an exact repeat likewise.)
Only repeats of at least MINREP cycles are applied, so that short inner loops do not hide the long cycle around them.

The simulator stops at the first macro-step boundary at or after MAXSTEPS (written 1eN or as an integer), or after
SECONDS.  MODE: r / l print the tape each time the head enters a fresh blank block on the right / left (the records
of msim); v prints every applied repeat (steps before it, xN repeats, pP macro steps per cycle, tape, changes d);
t prints a tally of the applied repeats by (p, d); - prints only the end.

check_lvl2.py compares the result with msim (state, head side, the whole tape, the step count, the records).
"""
import sys
INF = None
MINREP = 12

class Form:
    __slots__ = ("a", "c")
    def __init__(s, a=None, c=0): s.a = a or {}; s.c = c
    def __add__(s, o):
        if isinstance(o, int): return Form(s.a, s.c + o)
        a = dict(s.a)
        for k, v in o.a.items():
            a[k] = a.get(k, 0) + v
            if a[k] == 0: del a[k]
        return Form(a, s.c + o.c)
    __radd__ = __add__
    def __sub__(s, o):
        assert isinstance(o, int); return Form(s.a, s.c - o)
    def __mul__(s, k):
        assert isinstance(k, int); return Form({r: v * k for r, v in s.a.items()} if k else {}, s.c * k)
    __rmul__ = __mul__
    def ev(s, x): return s.c + sum(v * x[r] for r, v in s.a.items())
    def const(s): return not s.a

class Abort(Exception): pass

class Sim:
    def __init__(s, machine, K):
        s.K = K; s.tr = []
        for part in machine.split("_"):
            row = []
            for y in range(2):
                t = part[3*y:3*y+3]
                row.append(None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65))
            s.tr.append(row)
        s.cache = {}
        s.L = [[0, INF]]; s.R = [[0, INF]]; s.st = 0; s.dir = 1; s.steps = 0
        s.sym = False; s.cons = []; s.x = None; s.halted = False

    def trans(s, st, d, top, beh):
        key = (st, d, top, beh); r = s.cache.get(key)
        if r is not None: return r
        K = s.K; lb, rb = (beh, top) if d else (top, beh)
        c = [(lb >> (K-1-i)) & 1 for i in range(K)] + [(rb >> (K-1-i)) & 1 for i in range(K)]
        p = K if d else K - 1; k = 0; res = None
        while 0 <= p < 2*K:
            if k > 1000000: res = 3; break
            t = s.tr[st][c[p]]
            if t is None: res = 2; break
            c[p] = t[0]; p += t[1]; st = t[2]; k += 1
        if res is None: res = 0 if ((p >= 2*K) if d else (p < 0)) else 1
        nl = int("".join(map(str, c[:K])), 2); nr = int("".join(map(str, c[K:])), 2)
        r = (res, st, nr if d else nl, nl if d else nr, k)
        s.cache[key] = r; return r

    # count predicates (concrete ints, or Forms in symbolic mode)
    def ge2(s, c):
        if isinstance(c, int): return c >= 2
        if c.const(): return c.c >= 2
        if c.ev(s.x) < 2: raise Abort()
        s.cons.append(c); return True

    def push(s, S, v, c):
        if S[-1][0] == v and S[-1][1] is not INF: S[-1][1] = S[-1][1] + c
        else: S.append([v, c])
    def pop1(s, S):
        if S[-1][1] is INF: return
        if s.ge2(S[-1][1]): S[-1][1] = S[-1][1] - 1
        else: S.pop()

    def step(s):
        F, B = (s.R, s.L) if s.dir else (s.L, s.R)
        top = F[-1][0]; beh = B[-1][0]; cnt = F[-1][1]; fresh = cnt is INF
        res, ns, nt, nb, k0 = s.trans(s.st, s.dir, top, beh)
        if res == 3: raise RuntimeError("loop")
        if res == 2: s.steps = s.steps + k0 + 1; s.halted = True; s.st = ns; return
        s.steps = s.steps + k0
        if res == 0:
            s.pop1(F); s.pop1(B); s.push(B, nb, 1); s.push(B, nt, 1)
            if ns == s.st and not fresh and s.ge2(cnt):
                u = s.trans(s.st, s.dir, top, nt)
                if u[0] == 0 and u[1] == s.st and u[2] == nt:
                    k = cnt - 1
                    assert F[-1][0] == top
                    F.pop()
                    s.pop1(B); s.push(B, u[3], k); s.push(B, nt, 1); s.steps = s.steps + k * u[4]
            s.st = ns
        else:
            s.pop1(F); s.pop1(B); s.push(F, nt, 1); s.push(F, nb, 1); s.st = ns; s.dir = 1 - s.dir
        return (1 if F is s.R else 2) if fresh else 0

    def sig(s):
        return (s.st, s.dir, tuple(r[0] for r in s.L), tuple(r[0] for r in s.R))
    def counts(s):
        return [r[1] for r in s.L] + [r[1] for r in s.R]
    def show(s, sym=None):
        K = s.K
        def f(r):
            w = format(r[0], "0%db" % K); return w if r[1] == 1 else "%s^%s" % (w, r[1])
        return "%s%s %s | %s" % ("ABCDEF"[s.st], "><"[1 - s.dir], " ".join(f(r) for r in s.L if r[1] is not INF),
                                 " ".join(f(r) for r in reversed(s.R) if r[1] is not INF))

    def try_accel(s, p, d):
        """The last p macro steps changed the counts by d and kept the shape.  Replay p steps with the changing counts
        as unknowns; if the shape and the changes come out the same for every value satisfying the recorded
        inequalities, apply the cycle as often as they stay true.  Returns the number of cycles applied (0: none)."""
        save = ([r[:] for r in s.L], [r[:] for r in s.R], s.st, s.dir, s.steps)
        c0 = s.counts(); nL = len(s.L)
        s.x = {i: c for i, c in enumerate(c0) if d[i] != 0}
        allr = s.L + s.R
        for i, r in enumerate(allr):
            if i in s.x: r[1] = Form({i: 1}, 0)
        sig0 = s.sig(); s.sym = True; s.cons = []; s.steps = Form()
        ok = True
        try:
            for _ in range(p):
                s.step()
                if s.halted: ok = False; break
        except Abort:
            ok = False
        if ok and s.sig() != sig0: ok = False
        if ok:
            for i, c in enumerate(s.counts()):
                if i in s.x:
                    if isinstance(c, int) or c.a != {i: 1} or c.c != d[i]: ok = False; break
                else:
                    cc = c.c if isinstance(c, Form) and c.const() else c
                    if cc != c0[i]: ok = False; break
        n = None
        if ok:
            for f in s.cons:
                e = sum(v * d[r] for r, v in f.a.items())
                if e < 0:
                    t = (f.ev(s.x) - 2) // (-e) + 1
                    n = t if n is None else min(n, t)
            if n is None: n = -1
        S = s.steps; cons = s.cons
        s.L, s.R, s.st, s.dir, s.steps = save; s.sym = False; s.halted = False
        if not ok or (n != -1 and n < MINREP): return 0
        if n == -1: return -1
        allr = s.L + s.R
        for i in s.x: allr[i][1] += n * d[i]
        e = sum(v * d[r] for r, v in S.a.items())
        s.steps += n * S.ev(s.x) + (n * (n - 1) // 2) * e
        return n

def run(machine, K, maxsteps, on_event=None, maxms=10**9, rec=None, tlimit=None):
    import time; t0 = time.time()
    s = Sim(machine, K); hist = {}; ms = 0; nacc = 0
    while s.steps < maxsteps and ms < maxms:
        if tlimit and ms % 4096 == 0 and time.time() - t0 > tlimit: break
        fr = s.step(); ms += 1
        if fr and rec is not None and ((s.L if s.dir else s.R)[-1][1] is not INF or True):
            rec(s, fr)
        if s.halted:
            return s, "HALT", ms, nacc
        g = s.sig(); c = s.counts(); h = hist.get(g)
        hist[g] = (ms, c)
        if h is not None:
            d = [0 if (a is INF) else a - b for a, b in zip(c, h[1])]
            if any(d):
                before = s.show() if on_event else None; st0 = s.steps
                n = s.try_accel(ms - h[0], d)
                if n == -1: return s, "NONHALT(cycle rule never stops)", ms, nacc
                if n:
                    nacc += 1; hist.clear()
                    if on_event: on_event(s, before, st0, n, ms - h[0], d)
            else:
                return s, "NONHALT(exact repeat)", ms, nacc
        if len(hist) > 200000: hist.clear()
    return s, "END", ms, nacc

if __name__ == "__main__":
    m, K = sys.argv[1], int(sys.argv[2]); a = sys.argv[3]
    mx = 10 ** int(a[2:]) if a.startswith('1e') else int(a)
    mode = sys.argv[4] if len(sys.argv) > 4 else ""
    import re; tally = {}; shapes = set()
    def ev(s, before, st0, n, p, d):
        if mode == "v":
            print(st0, "x%d p%d" % (n, p), before, " d=", [x for x in d if x], flush=True)
        if mode == "t":
            k = (p, tuple(x for x in d if x)); tally[k] = tally.get(k, 0) + 1
            shapes.add((re.sub(r"\^\d+", "^n", before), k))
    def rec(s, fr):
        if (mode == "r" and fr == 1) or (mode == "l" and fr == 2): print(s.steps, s.show(), flush=True)
    tl = float(sys.argv[5]) if len(sys.argv) > 5 else None
    s, why, ms, nacc = run(m, K, mx, ev if mode in ("v", "t") else None, rec=rec, tlimit=tl)
    print(why, "steps=%s digits=%d ms=%d accel=%d runs=%d" % (str(s.steps)[:40], len(str(s.steps)), ms, nacc, len(s.L)+len(s.R)-2)); print(s.show()[:600])
    if mode == "t":
        print("%d kinds of repeat (p, d), %d shapes" % (len(tally), len(shapes)))
        for k, v in sorted(tally.items(), key=lambda kv: -kv[1]): print("%6d  p=%d d=%s" % (v, k[0], list(k[1])))
