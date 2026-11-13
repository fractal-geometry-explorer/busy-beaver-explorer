"""fitlib: fit a piecewise-affine frame map.  Each var of a frame is either a small value < T or 'big' (>= T)."""
import itertools
from fm import FM
class Fit:
    def __init__(s, M, FR, T=3, W=5, MOD=1, turns=False, canon_only=True):
        s.canon_only = canon_only
        s.F = FM(M, FR, turns); s.T = T; s.W = W; s.MOD = MOD; s.cases = {}; s.bad = []
        for n in s.F.frames:
            k = len(s.vars_of(n))
            for pat in itertools.product(*[list(range(T)) + [('big', r) for r in range(MOD)]] * k): s.fitcase(n, pat)
    def vars_of(s, n): return [t.split('^')[1] for t in s.F.frames[n][0] if '^' in t]
    def canon(s, n, vals):
        P = dict(zip(s.vars_of(n), vals)); tape, p, st = s.F.build(n, P)
        return s.F.match(tape, p, st) == (n, P)
    def run(s, n, vals):
        r = s.F.nxt(n, dict(zip(s.vars_of(n), vals)))
        if r is None: return ('NONE', (), 0)
        if r[0] == 'HALT': return ('HALT', (), r[1])
        return (r[0], tuple(r[1][v] for v in s.vars_of(r[0])), r[2])
    def rng(s, r):
        st = s.T + ((r - s.T) % s.MOD); return range(st, st + s.W * s.MOD, s.MOD)
    def fitaff(s, pts, big):
        from fractions import Fraction
        base, b0 = pts[0]; co = {}
        for i in big:
            for v, y in pts:
                if all(v[k] == base[k] for k in range(len(v)) if k != i) and v[i] == base[i] + s.MOD:
                    co[i] = Fraction(y - b0, s.MOD)
        c0 = b0 - sum(co.get(i, 0) * base[i] for i in big)
        return (c0, co)
    @staticmethod
    def ev(f, v):
        x = f[0] + sum(c * v[i] for i, c in f[1].items()); assert x == int(x); return int(x)
    def fitcase(s, n, pat):
        k = len(pat); big = [i for i in range(k) if isinstance(pat[i], tuple)]
        grid = [g for g in itertools.product(*[[pat[i]] if i not in big else s.rng(pat[i][1]) for i in range(k)])
                if (not s.canon_only) or s.canon(n, g)]
        if not grid: return
        res = [(g, s.run(n, g)) for g in grid]
        kinds = set(r[0] for _, r in res)
        if len(kinds) != 1: s.bad.append((n, pat, 'nonuniform', sorted(kinds))); return
        kd = kinds.pop(); m = len(res[0][1][1])
        fs = [s.fitaff([(g, r[1][j]) for g, r in res], big) for j in range(m)]
        fst = s.fitaff([(g, r[2]) for g, r in res], big)
        ok = all(tuple(s.ev(f, g) for f in fs) == r[1] and s.ev(fst, g) == r[2] for g, r in res)
        if not ok: s.bad.append((n, pat, 'nonlinear')); return
        s.cases[(n, pat)] = (kd, fs, fst)
    def pat_of(s, vals): return tuple(v if v < s.T else ('big', v % s.MOD) for v in vals)
    def predict(s, n, vals):
        c = s.cases.get((n, s.pat_of(vals)))
        if c is None: return None
        kd, fs, fst = c
        return kd, tuple(s.ev(f, vals) for f in fs), s.ev(fst, vals)
    def show(s, out=print):
        def sh(f, names):
            c0, co = f; t = ' + '.join((f'{c}*{names[i]}' if c != 1 else names[i]) for i, c in co.items() if c)
            return (t + (f' + {c0}' if c0 > 0 else f' - {-c0}' if c0 < 0 else '')) if t else str(c0)
        for (n, pat), (kd, fs, fst) in s.cases.items():
            vs = s.vars_of(n); lab = n + '(' + ', '.join(str(p) if not isinstance(p, tuple) else (vs[i] if s.MOD == 1 else f'{vs[i]}~{p[1]}') for i, p in enumerate(pat)) + ')'
            out(f"{lab:16s} -> {kd}({', '.join(sh(f, vs) for f in fs)})  [{sh(fst, vs)}]")
        for b in s.bad: out('BAD', b)
    def verify(s, R):   # check predictions on every canonical point with all vars < R
        bad = 0; n_ = 0
        for n in s.F.frames:
            for g in itertools.product(range(R), repeat=len(s.vars_of(n))):
                if not s.canon(n, g): continue
                p = s.predict(n, g); r = s.run(n, g); n_ += 1
                if p is None or p != r:
                    bad += 1
                    if bad < 10: print('MISMATCH', n, g, 'pred', p, 'got', r)
        print('verified', n_, 'points, bad', bad)
