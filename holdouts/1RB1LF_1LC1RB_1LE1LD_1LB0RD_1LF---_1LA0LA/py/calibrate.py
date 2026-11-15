"""Step constants of the recursion for a machine: fit on random words, then check exactly."""
import sys, random
from fractions import Fraction
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import geng
from geng import *
from msim import parse_machine

def visit_cost(M, ds, maxsteps=10**7):
    """direct simulation of one wall visit of the word with digits ds; (steps, new digits) or None"""
    T = parse_machine(M)
    tape = {}
    p = 2
    for i, d in enumerate(ds):
        for _ in range(d):
            tape[p] = 1; tape[p + 1] = 1; p += 2
        if i < len(ds) - 1:
            tape[p] = 1; tape[p + 1] = 0; p += 2
    pos, s = 1, 5
    for n in range(1, maxsteps):
        tr = T[s][tape.get(pos, 0)]
        if tr is None:
            return None
        tape[pos] = tr[0]; pos += tr[1]; s = tr[2]
        if s == 5 and pos == -1:
            hi = max(k for k, v in tape.items() if v)
            cells = [tape.get(k, 0) for k in range(0, hi + 1)]
            if len(cells) % 2: cells.append(0)
            out = []; y = 0
            for i in range(0, len(cells), 2):
                if cells[i] != 1: return None
                if cells[i + 1]: y += 1
                else: out.append(y); y = 0
            out.append(y)
            return n, out
        if pos < -1 or pos > 4000:
            return None
    return None

NAMES = ['g0', 'cend', 'c1', 'd1', 'd0']

def engine_cost(ds):
    geng.C[0] = 0
    T = G(from_digits(ds))
    return geng.C[0], to_digits(T)

def symbolic():
    for i, nm in enumerate(NAMES):
        geng.CST[nm] = Lin.var(i, 0)
    geng.CST['cR'] = geng.CST['d1'] + geng.CST['d0'] + geng.CST['g0'] + 8

def calibrate(M, seed=1, nfit=400, ncheck=3000):
    random.seed(seed)
    geng.ACCEL[0] = False
    symbolic()
    rows = []
    def rnd():
        return [random.choice([0, 0, 0, 1, 1, 2, 3, 4, 5, 7]) for _ in range(random.randint(1, 16))]
    while len(rows) < nfit:
        ds = rnd()
        if Gref(ds) is None: continue
        r = visit_cost(M, ds)
        assert r is not None and r[1] == Gref(ds), ds
        geng.Rec.cons = []; geng.Rec.work = 0; geng.Rec.limit = 10**9
        c, out = engine_cost(ds)
        geng.Rec.cons = None
        assert out == r[1]
        coef = [c.c.get(i, 0) for i in range(len(NAMES))] if isinstance(c, Lin) else [0]*len(NAMES)
        const = c.k if isinstance(c, Lin) else c
        rows.append((coef, r[0] - const))
    # solve exactly by Gaussian elimination on a full-rank subset
    n = len(NAMES)
    A = [[Fraction(x) for x in coef] + [Fraction(b)] for coef, b in rows]
    piv = []
    r0 = 0
    for col in range(n):
        pr = next((i for i in range(r0, len(A)) if A[i][col] != 0), None)
        if pr is None: continue
        A[r0], A[pr] = A[pr], A[r0]
        A[r0] = [x / A[r0][col] for x in A[r0]]
        for i in range(len(A)):
            if i != r0 and A[i][col] != 0:
                A[i] = [x - A[i][col] * y for x, y in zip(A[i], A[r0])]
        piv.append(col); r0 += 1
    incons = [row for row in A[r0:] if row[n] != 0]
    sol = {NAMES[c]: A[i][n] for i, c in enumerate(piv)}
    return sol, len(piv), len(incons)

def install(sol):
    for nm in NAMES:
        v = sol.get(nm, 0)
        assert v.denominator == 1
        geng.CST[nm] = int(v)
    geng.CST['cR'] = geng.CST['d1'] + geng.CST['d0'] + geng.CST['g0'] + 8

def check(M, n=3000, seed=7):
    random.seed(seed)
    ok = 0
    for acc in (False, True):
        geng.ACCEL[0] = acc
        for _ in range(n):
            ds = [random.choice([0, 0, 0, 1, 1, 2, 3, 4, 5, 7, 9]) for _ in range(random.randint(1, 20))]
            if Gref(ds) is None: continue
            r = visit_cost(M, ds)
            c, out = engine_cost(ds)
            assert out == r[1] and c == r[0], (ds, c, r[0])
            ok += 1
    geng.ACCEL[0] = True
    return ok

if __name__ == "__main__":
    MS={'1':"1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA",'2':"1RB1LF_1LC1RB_1LF1LD_1LE0RD_1LB---_1LA0LA"}
    M = MS[sys.argv[1]]
    sol, rank, incons = calibrate(M)
    print(sol, "rank", rank, "inconsistent rows", incons)
    if not incons:
        install(sol)
        print("checked on", check(M), "random words: engine cost == machine steps")
