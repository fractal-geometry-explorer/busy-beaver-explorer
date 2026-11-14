"""A simulator on run lists whose rules are learned from direct simulation (machine-independent).

A configuration is the tape at a visit of the left end in a given state (a new leftmost cell reached in that state),
written as the lengths of its runs of 1s, left to right, with single 0s between runs (an empty run is a double 0),
run-length coded: tokens (pattern, count), e.g. `0 3 2^n 3^p (3 1)^K 3^X 0 3^k 1`.

The map from one visit to the next is not derived by hand.  For each *shape* (the token patterns, the small counts
literally, each large count or large run as a variable with its residue mod m) the rule is learned the first time
the shape occurs: the oracle (c/syn.c, the plain machine) is run on small instances of the shape, the result is
fitted (new counts: affine in the variables; steps: quadratic) and the fit is checked on further instances,
including far ones (`far`); a shape whose results do not fit is learned again from larger instances, and failing that
its smallest variable is taken literally.  Stretches of visits that repeat a cycle of rules, every count moving by a
constant, are jumped in closed form (three cycles are run first; the rules of the cycle must have integer
coefficients, so that the residues, hence the shapes, repeat).

Trust: a learned rule is an extrapolation from finitely many instances, so a run of this simulator is a computation
to be validated, not a proof.  It is validated against exact runs (the plain machine and the accelerated macro
machine of accel.py): see runlist.py.
"""
import subprocess, sys, itertools, random
from fractions import Fraction as Fr

DMAX = 4          # longest multi-run pattern grouped
CAPC = 12         # big counts are capped at this many copies when re-canonicalizing

def compress(runs):
    """list of ints -> tokens [(pattern tuple, count)] ; greedy, deterministic. Also returns spans."""
    out, spans, i, n = [], [], 0, len(runs)
    while i < n:
        k = 1
        while i + k < n and runs[i + k] == runs[i]:
            k += 1
        if k >= 2:
            out.append(((runs[i],), k)); spans.append((i, i + k)); i += k; continue
        done = False
        for d in range(2, DMAX + 1):
            pat = runs[i:i + d]
            if len(pat) < d: break
            k = 1
            while runs[i + k * d:i + (k + 1) * d] == pat:
                k += 1
            if k >= 3:
                out.append((tuple(pat), k)); spans.append((i, i + k * d)); i += k * d; done = True; break
        if not done:
            out.append(((runs[i],), 1)); spans.append((i, i + 1)); i += 1
    return out, spans

def expand(tokens):
    r = []
    for pat, c in tokens:
        r.extend(list(pat) * c)
    return r

def canon(tokens):
    """canonical token list equal to compress(expand(tokens)), computed with big counts capped."""
    runs, marks = [], []
    for pat, c in tokens:
        if c > CAPC:
            a = len(runs); runs.extend(list(pat) * CAPC); marks.append(((a + len(runs)) // 2, c - CAPC, len(pat)))
        else:
            runs.extend(list(pat) * c)
    toks, spans = compress(runs)
    toks = [list(t) for t in toks]
    for mid, extra, L in marks:
        for j, (a, b) in enumerate(spans):
            if a <= mid < b:
                d = len(toks[j][0])
                if L % d or toks[j][1] < 3 and d > 1:
                    raise ValueError(f"canon: cannot restore {extra} x len {L} into {toks[j]}")
                toks[j][1] += extra * (L // d); break
        else:
            raise ValueError("canon: mark not found")
    return [(p, c) for p, c in toks]

def fmt(tokens):
    def one(p, c):
        s = str(p[0]) if len(p) == 1 else "(" + " ".join(map(str, p)) + ")"
        return s if c == 1 else f"{s}^{c}"
    return " ".join(one(p, c) for p, c in tokens)

def parse(s):
    """'0 3 2^5 (3 1)^4 7' -> tokens"""
    toks, i, s = [], 0, s.strip()
    import re
    for m in re.finditer(r"\(([\d ]+)\)(?:\^(\d+))?|(\d+)(?:\^(\d+))?", s):
        if m.group(1) is not None:
            toks.append((tuple(int(x) for x in m.group(1).split()), int(m.group(2) or 1)))
        else:
            toks.append(((int(m.group(3)),), int(m.group(4) or 1)))
    return toks


class Sim:
    """the oracle: direct simulation from a run list to the next visit"""
    def __init__(self, machine, state="D", exe="./syn", maxsteps=2e8):
        self.machine, self.state, self.exe, self.maxsteps = machine, state, exe, maxsteps
        self.calls = 0
    def next(self, runlists):
        inp = "\n".join(" ".join(map(str, r)) for r in runlists) + "\n"
        out = subprocess.run([self.exe, self.machine, str(self.maxsteps), "f", self.state], input=inp,
                             capture_output=True, text=True).stdout.strip().split("\n")
        self.calls += len(runlists)
        res = []
        for l in out:
            f = l.split()
            if f[0] == "HALT": res.append(("HALT", int(f[1]))); continue
            if f[0] == "RUN": res.append(("RUN", None)); continue
            runs = []
            for t in f[1:]:
                if "^" in t:
                    v, c = t.split("^"); runs.extend([int(v)] * int(c))
                else: runs.append(int(t))
            while runs and runs[-1] == 0: runs.pop()
            res.append((int(f[0]), runs))
        return res


class Rule:
    pass


class RLS:
    def __init__(self, machine, state="D", T=8, TV=16, m=4, exe="./syn", verbose=False, far=12):
        self.sim = Sim(machine, state, exe)
        self.T, self.TV, self.m = T, TV, m
        self.rules = {}
        self.far = far
        self.maxbase = 0
        self.nfallback = 0
        self.verbose = verbose
        self.rng = random.Random(1)

    # ---- shapes
    def shape(self, tokens):
        key, vals = [], []
        for pat, c in tokens:
            kp = []
            for v in pat:
                if v >= self.TV: kp.append(("V", v % self.m)); vals.append(v)
                else: kp.append(v)
            if c >= self.T: kc = ("V", c % self.m); vals.append(c)
            else: kc = c
            key.append((tuple(kp), kc))
        return tuple(key), vals

    def instantiate(self, key, vals):
        it = iter(vals); toks = []
        for kp, kc in key:
            pat = tuple(next(it) if isinstance(v, tuple) else v for v in kp)
            c = next(it) if isinstance(kc, tuple) else kc
            toks.append((pat, c))
        return toks

    def _base(self, key):
        b = []
        for kp, kc in key:
            for v in kp:
                if isinstance(v, tuple):
                    x = self.TV + self.m; x += (v[1] - x) % self.m; b.append(x)
            if isinstance(kc, tuple):
                x = self.T + self.m; x += (kc[1] - x) % self.m; b.append(x)
        return b

    def learn(self, key):
        err = None
        for lift in (0, 2, 6, 14, 30, 62):
            try:
                r = self._learn(key, lift)
                self.maxbase = max([self.maxbase] + r.base)
                return r
            except RuntimeError as e:
                err = e
        raise err

    def _learn(self, key, lift):
        m = self.m
        base = [b + lift * m for b in self._base(key)]; d = len(base)
        pts = [tuple([0] * d)]
        for i in range(d):
            for x in (1, 2):
                p = [0] * d; p[i] = x; pts.append(tuple(p))
        for i in range(d):
            for j in range(i + 1, d):
                p = [0] * d; p[i] = 1; p[j] = 1; pts.append(tuple(p))
        extra = [tuple(self.rng.randint(0, 3) for _ in range(d)) for _ in range(3)] if d else []
        for i in range(d):
            p = [0] * d; p[i] = self.far; extra.append(tuple(p))
        if d > 1: extra.append(tuple([self.far // 2] * d))
        allp = pts + extra
        res = self.sim.next([expand(self.instantiate(key, [b + m * x for b, x in zip(base, p)])) for p in allp])
        r = Rule(); r.key = key; r.d = d; r.base = base
        kinds = set(x[0] if isinstance(x[0], str) else "OK" for x in res)
        if kinds == {"HALT"}:
            r.kind = "HALT"; r.out = []; r.struct = []
            S = [x[1] for x in res]; idx = {p: i for i, p in enumerate(allp)}
            self._fit_steps(r, S, idx, allp, d, key)
            return r
        if kinds != {"OK"}:
            raise RuntimeError(f"learn: mixed/failed results {kinds} for {key}")
        r.kind = "OK"
        outs = [compress(runs)[0] for _, runs in res]
        struct = [p for p, c in outs[0]]
        def vec(o):
            """numbers of an output: per token, pattern values that are 'big-like' and the count"""
            return o
        for o in outs:
            if [len(p) for p, c in o] != [len(p) for p in struct]:
                raise RuntimeError(f"learn: output structure varies for {key}: {fmt(outs[0])} | {fmt(o)}")
        # numbers: all pattern values and counts, as functions
        def nums(o):
            v = []
            for p, c in o:
                v.extend(p); v.append(c)
            return v
        N = [nums(o) for o in outs]
        S = [s for s, _ in res]
        idx = {p: i for i, p in enumerate(allp)}
        def fit_affine(col):
            f0 = Fr(col[0]); a = []
            for i in range(d):
                p = [0] * d; p[i] = 1
                a.append(Fr(col[idx[tuple(p)]] - col[0], m))
            return f0, a
        def ev_aff(f, p):
            return f[0] + sum(ai * m * x for ai, x in zip(f[1], p))
        r.out = []
        for j in range(len(N[0])):
            col = [n[j] for n in N]
            f = fit_affine(col)
            for p, y in zip(allp, col):
                if ev_aff(f, p) != y:
                    raise RuntimeError(f"learn: non-affine output {j} for {key}: {fmt(outs[0])}")
            r.out.append(f)
        r.struct = [len(p) for p in struct]
        self._fit_steps(r, S, idx, allp, d, key)
        return r

    def _fit_steps(self, r, S, idx, allp, d, key):
        # steps: quadratic in x (units of m)
        s0 = Fr(S[0]); lin = []; quad = {}
        for i in range(d):
            p1 = [0] * d; p1[i] = 1; p2 = [0] * d; p2[i] = 2
            y1 = S[idx[tuple(p1)]] - S[0]; y2 = S[idx[tuple(p2)]] - S[0]
            q = Fr(y2 - 2 * y1, 2); l = y1 - q
            lin.append(Fr(l)); quad[(i, i)] = q
        for i in range(d):
            for j in range(i + 1, d):
                p = [0] * d; p[i] = 1; p[j] = 1
                y = S[idx[tuple(p)]] - S[0]
                quad[(i, j)] = Fr(y) - lin[i] - quad[(i, i)] - lin[j] - quad[(j, j)]
        r.steps = (s0, lin, quad)
        for p, y in zip(allp, S):
            if self._ev_steps(r, p) != y:
                raise RuntimeError(f"learn: steps not quadratic for {key}")

    @staticmethod
    def _ev_steps(r, x):
        s0, lin, quad = r.steps
        return s0 + sum(l * xi for l, xi in zip(lin, x)) + sum(q * x[i] * x[j] for (i, j), q in quad.items())

    @staticmethod
    def literalize(key, vals, which):
        it = iter(range(len(vals))); nk, nv = [], []
        def one(slot):
            i = next(it)
            if i in which: return vals[i]
            nv.append(vals[i]); return slot
        for kp, kc in key:
            kp2 = tuple(one(v) if isinstance(v, tuple) else v for v in kp)
            kc2 = one(kc) if isinstance(kc, tuple) else kc
            nk.append((kp2, kc2))
        return tuple(nk), nv

    def apply(self, tokens):
        """one visit: returns (new tokens, steps, rule) or ('HALT', steps, rule)"""
        key, vals = self.shape(tokens)
        while True:
            r = self.rules.get(key)
            if r is None:
                try:
                    r = self.learn(key)
                except RuntimeError as e:
                    if not vals: raise
                    r = None
                    self.rules[key] = "FAIL"
                else:
                    self.rules[key] = r
                    if self.verbose: print("learned", len(self.rules), fmt(self.instantiate(key, r.base)), file=sys.stderr)
            if r == "FAIL": r = None
            if r is None:
                if not vals: raise RuntimeError("no rule for " + fmt(tokens)[:200])
                if min(vals) > 100000 or sum(c * len(p) for p, c in tokens) > 3000000: raise RuntimeError("cannot learn a rule for " + fmt(tokens)[:300])
                i = min(range(len(vals)), key=lambda j: vals[j])
                key, vals = self.literalize(key, vals, {i}); self.nfallback += 1
                continue
            low = {i for i, (v, b) in enumerate(zip(vals, r.base)) if v < b}
            if not low: break
            key, vals = self.literalize(key, vals, low)
        x = [Fr(v - b, self.m) for v, b in zip(vals, r.base)]
        st = self._ev_steps(r, x)
        assert st.denominator == 1
        if r.kind == "HALT":
            return "HALT", int(st), r
        nums = []
        for f0, a in r.out:
            y = f0 + sum(ai * self.m * xi for ai, xi in zip(a, x))
            assert y.denominator == 1 and y >= 0, (y, fmt(tokens))
            nums.append(int(y))
        toks, i = [], 0
        for L in r.struct:
            toks.append((tuple(nums[i:i + L]), nums[i + L])); i += L + 1
        toks = [(p, c) for p, c in toks if c > 0]
        return canon(toks), int(st), r

    @staticmethod
    def integral(r):
        return r is not None and all(ai.denominator == 1 for f0, a in r.out for ai in a)


class Runner:
    """iterates visits with cycle jumps"""
    def __init__(self, rls, tokens, steps=0, margin=None, jump=True):
        self.rls, self.tokens, self.steps, self.visits = rls, canon(tokens), steps, 0
        self.margin = margin if margin is not None else 3 * rls.m + 4
        self.hist = []          # (key, vals, steps, integral) of recent visits
        self.halted = False
        self.jumps = 0
        self.jump = jump
        self.last_rule = None
        self.limit = None

    def step(self):
        if self.halted: return False
        res = self.rls.apply(self.tokens)
        if res[0] == "HALT":
            self.halted = True; self.steps += res[1]; return False
        key, vals = self.rls.shape(self.tokens)
        self.hist.append((key, vals, self.steps, RLS.integral(res[2])))
        del self.hist[:-200]
        self.tokens, st, self.last_rule = res
        self.steps += st; self.visits += 1
        if self.jump: self.try_jump()
        return True

    def try_jump(self):
        key, vals = self.rls.shape(self.tokens)
        H = self.hist
        # find period P: key recurs at -P, -2P, -3P (hist entries are configs BEFORE each visit; current is 'now')
        for P in range(1, 49):
            if 3 * P > len(H): return
            if H[-P][0] != key or H[-2 * P][0] != key or H[-3 * P][0] != key: continue
            if any(H[-i][0] != H[-i - P][0] or H[-i][0] != H[-i - 2 * P][0] for i in range(1, P + 1)): continue
            if not all(h[3] for h in H[-3 * P:]): return
            v0, v1, v2 = H[-3 * P][1], H[-2 * P][1], H[-P][1]
            d = [a - b for a, b in zip(vals, v2)]
            if d != [a - b for a, b in zip(v2, v1)] or d != [a - b for a, b in zip(v1, v0)]: return
            S0, S1, S2 = H[-2 * P][2] - H[-3 * P][2], H[-P][2] - H[-2 * P][2], self.steps - H[-P][2]
            # also intermediate vars must stay large: bound by start values
            t = None
            # thresholds of each var
            ths = []
            for kp, kc in key:
                for v in kp:
                    if isinstance(v, tuple): ths.append(max(self.rls.TV, self.rls.maxbase))
                if isinstance(kc, tuple): ths.append(max(self.rls.T, self.rls.maxbase))
            if any(di != 0 and v < th for v, di, th in zip(vals, d, ths)): return
            for v, di, th in zip(vals, d, ths):
                if di < 0:
                    room = (v - th - self.margin * max(1, -di)) // (-di)
                    t = room if t is None else min(t, room)
            if t is None or t < 2: return
            if self.limit is not None:
                def tot0(n):
                    return n * S0 + n * (n - 1) // 2 * (S1 - S0) + n * (n - 1) * (n - 2) // 6 * ((S2 - S1) - (S1 - S0))
                lo, hi = 0, t
                while lo < hi:
                    mid = (lo + hi + 1) // 2
                    if self.steps + tot0(mid + 3) - tot0(3) <= self.limit: lo = mid
                    else: hi = mid - 1
                t = lo
                if t < 2: return
            # per-cycle steps: S(k) = S2 + (k+1) D1 + C(k+1,2) D2 ... use Newton from S0,S1,S2 at k=-3,-2,-1 -> next cycles k=0..t-1
            D1 = S1 - S0; D2 = (S2 - S1) - D1
            # S(j) for cycle index j (0 = first observed): S0 + j D1 + C(j,2) D2 ; sum_{j=3}^{t+2}
            def tot(n):  # sum_{j=0}^{n-1}
                return n * S0 + n * (n - 1) // 2 * D1 + n * (n - 1) * (n - 2) // 6 * D2
            add = tot(t + 3) - tot(3)
            newvals = [v + t * di for v, di in zip(vals, d)]
            self.tokens = canon(self.rls.instantiate(key, newvals))
            self.steps += add; self.visits += t * P; self.jumps += 1
            self.hist = []
            return
