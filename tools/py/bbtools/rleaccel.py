"""An accelerated simulator for any two-symbol machine: the tape is run-length coded in blocks of K cells, a run
that the head crosses without changing state is crossed in one step (a chain step), and cycles are jumped: when the
same local shape (state, direction, the symbols of the W nearest runs on each side) comes back after the same number
of macro steps, one cycle is replayed symbolically with the run lengths as variables.  If the replay ends in the
same shape with every length changed by a constant, that is a proof of the one-cycle rule for all lengths above the
minimums the replay needed, so n cycles can be applied at once, with the exact step count.  Nothing is guessed: a
rule is used only after its symbolic proof, and only while its minimums hold.  If no length shrinks the rule repeats
forever and the machine is reported as not halting.

Trust level: trusted computation (Python).  `tools/tests/test_rleaccel.py` compares the tape and the step count with
a direct cell-by-cell run.

usage: python3 tools/py/bbtools/rleaccel.py MACHINE [K] [MACRO_STEPS]
"""
import sys

INF = -1


def parse(m):
    rows = m.split("_")
    T = {}
    for qi, row in enumerate(rows):
        for b in (0, 1):
            t = row[3 * b:3 * b + 3]
            if t[0] == "-":
                T[(qi, b)] = None
            else:
                T[(qi, b)] = (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T


class Macro:
    def __init__(self, m, k):
        self.T = parse(m)
        self.k = k
        self.memo = {}
        self.nstates = len(m.split("_"))

    def trans(self, q, sym, d):
        """head enters a k-block (value sym, bit i = cell i from the left... stored as tuple) moving in direction d.
        returns ('halt', steps, cells, q, pos) | ('loop',) | ('ok', newsym, newq, newd, steps)"""
        key = (q, sym, d)
        r = self.memo.get(key)
        if r is not None:
            return r
        k = self.k
        cells = [(sym >> (k - 1 - i)) & 1 for i in range(k)]
        pos = 0 if d == 1 else k - 1
        steps = 0
        seen = set()
        while True:
            st = (q, pos, tuple(cells))
            if st in seen:
                r = ("loop",)
                break
            seen.add(st)
            t = self.T[(q, cells[pos])]
            if t is None:
                r = ("halt", steps + 1, tuple(cells), q, pos)
                break
            cells[pos] = t[0]
            pos += t[1]
            q = t[2]
            steps += 1
            if pos < 0 or pos >= k:
                ns = 0
                for c in cells:
                    ns = ns * 2 + c
                r = ("ok", ns, q, 1 if pos >= k else -1, steps)
                break
        self.memo[key] = r
        return r


class Lin:
    """c + sum a_i x_i"""
    __slots__ = ("c", "a")

    def __init__(self, c=0, a=None):
        self.c = c
        self.a = a or {}

    def add(self, o, mul=1):
        if isinstance(o, int):
            return Lin(self.c + o * mul, self.a)
        a = dict(self.a)
        for v, k in o.a.items():
            a[v] = a.get(v, 0) + k * mul
            if a[v] == 0:
                del a[v]
        return Lin(self.c + o.c * mul, a)

    def __repr__(self):
        return "%d+%s" % (self.c, self.a)


class ProofFail(Exception):
    pass


class Sim:
    def __init__(self, m, k=1, prove=True, maxloop=4000, gen_thresh=4, verbose=False, W=8):
        self.mm = Macro(m, k)
        self.k = k
        self.L = [[0, INF]]
        self.R = [[0, INF]]
        self.q = 0
        self.d = 1
        self.steps = 0
        self.nmacro = 0
        self.halted = None
        self.nonhalt = None
        self.prove = prove
        self.past = {}
        self.rules = {}
        self.fails = {}
        self.maxloop = maxloop
        self.gen_thresh = gen_thresh
        self.verbose = verbose
        self.nrules = 0
        self.njumps = 0
        self.nproofs = 0
        self.W = W
        self.proofcost = 0

    # ---- concrete ----
    def sig(self):
        W = self.W
        return (self.q, self.d, tuple([r[0] for r in self.L[-W:]]), tuple([r[0] for r in self.R[-W:]]))

    def basic(self):
        if self.d == 1:
            stack, other = self.R, self.L
        else:
            stack, other = self.L, self.R
        top = stack[-1]
        sym, cnt = top
        tr = self.mm.trans(self.q, sym, self.d)
        if tr[0] != "ok":
            if tr[0] == "halt":
                self.steps += tr[1]
                self.halted = tr
            else:
                self.nonhalt = "in-block loop"
            return
        _, ns, nq, nd, st = tr
        if nq == self.q and nd == self.d:
            if cnt == INF:
                self.nonhalt = "runs off to infinity"
                return
            stack.pop()
            self.steps += cnt * st
            o = other[-1]
            if o[0] == ns:
                if o[1] != INF:
                    o[1] += cnt
            else:
                other.append([ns, cnt])
            return
        if cnt != INF:
            if cnt == 1:
                stack.pop()
            else:
                top[1] = cnt - 1
        tgt = other if nd == self.d else stack
        o = tgt[-1]
        if o[0] == ns:
            if o[1] != INF:
                o[1] += 1
        else:
            tgt.append([ns, 1])
        self.q = nq
        self.d = nd
        self.steps += st

    # ---- symbolic proof of one cycle ----
    def try_prove(self, sig, old, nloops):
        oq, od, oL, oR = old[:4]
        self.nproofs += 1
        nv = 0
        mins = []
        home = []  # (side, index)
        L = []
        R = []
        curL, curR = self.L[-self.W:], self.R[-self.W:]
        for side, src, cur, dst in ((0, oL, curL, L), (1, oR, curR, R)):
            for i, (s, c) in enumerate(src):
                if c != INF and (c != cur[i][1] or c >= self.gen_thresh):
                    dst.append([s, Lin(0, {nv: 1})])
                    mins.append(1)
                    home.append((side, i))
                    nv += 1
                else:
                    dst.append([s, c])
        q, d = oq, od
        steps = Lin(0)
        mm = self.mm

        def need_pos(e, extra):
            # ensure e >= 1 + extra under the current minimums
            if isinstance(e, int):
                return e >= 1 + extra
            lo = e.c
            for v, a in e.a.items():
                if a < 0:
                    raise ProofFail("neg coef")
                lo += a * mins[v]
            if lo >= 1 + extra:
                return True
            if len(e.a) == 1:
                (v, a), = e.a.items()
                if a == 1:
                    mins[v] = 1 + extra - e.c
                    return True
            raise ProofFail("cannot bound")

        def push(stack, ns, cnt):
            o = stack[-1] if stack else (None, None)
            if o[0] == ns:
                if o[1] != INF:
                    if isinstance(o[1], int) and isinstance(cnt, int):
                        o[1] += cnt
                    elif isinstance(o[1], int):
                        o[1] = cnt.add(o[1])
                    else:
                        o[1] = o[1].add(cnt)
            else:
                stack.append([ns, cnt])

        for _ in range(nloops):
            stack, other = (R, L) if d == 1 else (L, R)
            if not stack:
                raise ProofFail("left the window")
            top = stack[-1]
            sym, cnt = top
            tr = mm.trans(q, sym, d)
            if tr[0] != "ok":
                raise ProofFail("halt in proof")
            _, ns, nq, nd, st = tr
            if nq == q and nd == d:
                if cnt == INF:
                    raise ProofFail("inf")
                stack.pop()
                if isinstance(cnt, int):
                    steps = steps.add(cnt * st)
                else:
                    steps = steps.add(cnt, st)
                push(other, ns, cnt)
                continue
            if cnt != INF:
                if isinstance(cnt, int):
                    if cnt == 1:
                        stack.pop()
                    else:
                        top[1] = cnt - 1
                else:
                    need_pos(cnt, 1)
                    top[1] = cnt.add(-1)
            push(other if nd == d else stack, ns, 1)
            q, d = nq, nd
            steps = steps.add(st)
        if q != oq or d != od or len(L) != len(oL) or len(R) != len(oR):
            raise ProofFail("shape")
        deltas = [None] * nv
        spec = ([], [])
        vi = 0
        for side, fin, src in ((0, L, oL), (1, R, oR)):
            for i, (s, c) in enumerate(fin):
                if s != src[i][0]:
                    raise ProofFail("sym")
                if vi < nv and home[vi] == (side, i):
                    if isinstance(c, int) or len(c.a) != 1 or c.a.get(vi) != 1:
                        raise ProofFail("not own var")
                    deltas[vi] = c.c
                    spec[side].append(vi)
                    vi += 1
                else:
                    if c != src[i][1]:
                        raise ProofFail("const changed")
                    spec[side].append(None)
        consts = ([c for _, c in oL], [c for _, c in oR])
        rule = (spec, consts, mins, deltas, steps.c, [steps.a.get(v, 0) for v in range(nv)], home)
        return rule

    def apply_rule(self, rule):
        spec, consts, mins, deltas, sc, sa, home = rule
        L, R = self.L[-self.W:], self.R[-self.W:]
        xs = []
        for side, cur in ((0, L), (1, R)):
            sp = spec[side]
            cs = consts[side]
            for i in range(len(cur)):
                c = cur[i][1]
                v = sp[i]
                if v is None:
                    if c != cs[i]:
                        return False
                else:
                    if c == INF or c < mins[v]:
                        return False
                    xs.append(c)
        k = None
        for v, dl in enumerate(deltas):
            if dl < 0:
                kk = (xs[v] - mins[v]) // (-dl) + 1
                if k is None or kk < k:
                    k = kk
        if k is None:
            self.nonhalt = "cycle rule repeats forever"
            return True
        st = k * sc
        for v, dl in enumerate(deltas):
            side, i = home[v]
            (L if side == 0 else R)[i][1] = xs[v] + k * dl
            st += sa[v] * (k * xs[v] + dl * (k * (k - 1) // 2))
        self.steps += st
        self.njumps += 1
        return True

    def run(self, max_macro, stop=None):
        past = self.past
        rules = self.rules
        fails = self.fails
        while self.nmacro < max_macro and self.halted is None and self.nonhalt is None:
            self.nmacro += 1
            if self.prove:
                sig = self.sig()
                rl = rules.get(sig)
                done = False
                if rl:
                    for r in rl:
                        if self.apply_rule(r):
                            done = True
                            break
                if done:
                    past.clear()
                    continue
                old = past.get(sig)
                if old is not None:
                    nl = self.nmacro - old[4]
                    if (nl == old[6] and nl <= self.maxloop and fails.get(sig, 0) < 3
                            and self.proofcost <= 2 * self.nmacro + 100000):
                        self.proofcost += nl
                        try:
                            r = self.try_prove(sig, old, nl)
                            rules.setdefault(sig, []).append(r)
                            self.nrules += 1
                            if self.apply_rule(r):
                                past.clear()
                                continue
                        except ProofFail:
                            fails[sig] = fails.get(sig, 0) + 1
                past[sig] = (self.q, self.d, [r[:] for r in self.L[-self.W:]], [r[:] for r in self.R[-self.W:]], self.nmacro, self.steps,
                             self.nmacro - old[4] if old is not None else 0)
                if len(past) > 20000:
                    past.clear()
                if len(rules) > 200000:
                    rules.clear()
                    fails.clear()
            self.basic()
            if stop is not None and self.steps >= stop:
                break

    def tape_str(self, maxlen=300):
        k = self.k

        def w(s):
            return format(s, "0%db" % k)
        l = " ".join("%s^%d" % (w(s), c) for s, c in self.L[1:])
        r = " ".join("%s^%d" % (w(s), c) for s, c in reversed(self.R[1:]))
        st = "ABCDEFGH"[self.q]
        mid = (" %s> " % st) if self.d == 1 else (" <%s " % st)
        s = l + mid + r
        return s if len(s) <= maxlen else s[:maxlen // 2] + " ... " + s[-maxlen // 2:]

    def width(self):
        return self.k * (sum(c for _, c in self.L[1:]) + sum(c for _, c in self.R[1:]))


if __name__ == "__main__":
    m = sys.argv[1]
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    mx = int(float(sys.argv[3])) if len(sys.argv) > 3 else 10 ** 6
    s = Sim(m, k)
    import time
    t0 = time.time()
    chunk = max(1, mx // 20)
    while s.nmacro < mx and s.halted is None and s.nonhalt is None:
        s.run(min(mx, s.nmacro + chunk))
        print("macro steps %d, machine steps %d, cells %d, rules %d, jumps %d, %.1fs" % (
            s.nmacro, s.steps, s.width(), s.nrules, s.njumps, time.time() - t0), flush=True)
    if s.halted:
        print("HALTED after", s.steps, "steps")
    elif s.nonhalt:
        print("DOES NOT HALT:", s.nonhalt)
    else:
        print("no halt in the first", s.steps, "steps")
    print(s.tape_str())
