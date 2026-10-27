"""Robustness of the exact endgame when the first wall is close to the gap (a fixed small) or to the second wall
(a = b - delta): close set and the worst 3 log2 R - 2 log2 |L| over closing paths."""
import sys, math, endsym
from fractions import Fraction as F
from endsym import Pos, cpos, Coset, Ctx, check_tape, Stop, NV
mode = sys.argv[1]; vals = range(int(sys.argv[2]), int(sys.argv[3]) + 1, 2); Rmax = int(sys.argv[4])
orig_search = endsym.search
def search_fixed(R, fixed):
    SC = F(2) ** 200
    av, bv, Ev = (x * SC for x in endsym.GEOS[0])
    var = lambda i, v: Pos([F(int(i == j)) for j in range(NV)] + [F(0)], v)
    b, E = var(1, bv), var(2, Ev)
    if mode == 'a': a = cpos(fixed)
    elif mode == 'b': a = b - fixed
    else:   # mode 'c': the second wall a fixed distance below the third, which is E - R - 1
        a = var(0, av); b = None
    return a, b, E
worst = (-99, None)
for v in vals:
    for R in range(2, Rmax + 1, 2):
        a, b, E = search_fixed(R, v)
        # reuse endsym.search's loop by temporarily replacing its start construction
        src_marks = None
        endsym.CLOSES.clear()
        def patched(R=R, a=a, b=b, E=E):
            c = E - (R + 1)
            if b is None: b = c - v
            st0 = {'W': E, 'marks': [{'t': 'G', 'p': cpos(1)}, {'t': 'W', 'p': a}, {'t': 'W', 'p': b}, {'t': 'W', 'p': c}],
                   'lastD': None, 'lastKind': None, 'chain': 0}
            return st0
        endsym.START = patched
        out = endsym.search(R, 0)
        for (RR, x0, B, shapes) in endsym.CLOSES:
            f = [F(0), F(147), F(-112), F(392 * RR - 186)]
            L0 = f[3] + sum(f[i] * x0[i] for i in range(3)); g = [sum(f[i] * B[i][k] for i in range(3)) for k in range(3)]
            mod = 0
            for t in g: mod = math.gcd(mod, int(t))
            r0 = int(L0) % mod
            m = min((x for x in range(-200000, 200001) if x % mod == r0 and x % 7 == 3), key=abs)
            val = 3 * math.log2(RR) - 2 * math.log2(abs(m))
            if val > worst[0]: worst = (val, (v, RR, r0, mod, abs(m), ' '.join(shapes)))
        bad = [k for k in out if k not in ('close', 'break', 'pass', 'notphase0')]
        if bad: print('fixed', v, 'R', R, 'other outcomes', {k: (float(out[k][0]), out[k][2][:2]) for k in bad})
    print('fixed', v, 'worst so far', worst, flush=True)
