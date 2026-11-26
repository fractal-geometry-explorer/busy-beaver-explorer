"""Counter programs transcribed from the Lean maps (holdouts/<machine>/lean/<file>).  Each entry:
vars, start, rules(vars) -> list of (guard, target) with target a tuple of next values or 'halt'.  Cases the Lean map
calls stuck/small are also 'halt' targets here (bad), so an invariant must exclude them too."""
from z3 import *
M = {}
def m1(v):
    a, c = v
    dom = And(a % 2 == 0, a >= 4, c >= 6)
    return [(Not(dom), 'halt'),
            (And(dom, c % 2 == 0, c <= a + 8), (a + 12 - c, 3 * c - 6)),
            (And(dom, c % 2 == 0, c > a + 8, c <= a + 12), 'halt'),
            (And(dom, c % 2 == 0, c > a + 12), (c - a - 10, 3 * a + 27)),
            (And(dom, c % 2 == 1, c + 5 <= a), (a - c - 1, 3 * c + 6)),
            (And(dom, c % 2 == 1, c + 5 > a, c < a), 'halt'),
            (And(dom, c % 2 == 1, c >= a), (c - a + 3, 3 * a))]
M['1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA'] = (2, (74, 30), m1)
def m2(v):
    p, r = v
    return [(Or(p < 1, r < 1), 'halt'),
            (And(p == 1, r >= 1), (r + 4, IntVal(1))),
            (And(p == 2, r >= 1, r % 3 == 1), (r + 5, IntVal(1))),
            (And(p == 2, r >= 1, r % 3 == 2), (r + 3, IntVal(2))),
            (And(p == 2, r >= 1, r % 3 == 0), 'halt'),
            (And(p >= 3, r >= 1, p % 3 == 0), (4 * (p / 3 - 1) + r + 6, IntVal(1))),
            (And(p >= 3, r >= 1, p % 3 == 1), (4 * ((p - 4) / 3) + r + 8, IntVal(1))),
            (And(p >= 3, r >= 1, p % 3 == 2), ((p - 5) / 3 + 1, 2 * ((p - 5) / 3) + r + 5))]
M['1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB'] = (2, (3, 1), m2)
def m3(v):
    p, r = v
    return [(Or(p < 1, r < 1), 'halt'), (And(p == 1, r >= 1), 'halt'),
            (And(p == 3, r >= 1, r % 2 == 1), (r + 5, IntVal(2))),
            (And(p == 3, r >= 1, r % 2 == 0), (r + 5, IntVal(1))),
            (And(p != 3, p >= 2, r >= 1, p % 2 == 0), (3 * ((p - 2) / 2) + r + 4, IntVal(1))),
            (And(p != 3, p >= 2, r >= 1, p % 2 == 1), ((p - 1) / 2 - 1, (p - 1) / 2 + r + 3))]
M['1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC'] = (2, (2, 2), m3)
def m4(v):
    a, b, c = v
    nn = And(a >= 0, b >= 0, c >= 0)
    R = [(And(nn, a >= 4), (a - 2, b + 3, c)), (And(nn, a == 3), (IntVal(1), b + 3, c)),
         (And(nn, a == 1, b >= 3, c >= 1), (b + 1, IntVal(4), c - 1)),
         (And(nn, a == 1, b == 1, c >= 1), (IntVal(2), IntVal(4), c - 1)),
         (And(nn, a == 1, b >= 3, c == 0), (b + 1, IntVal(3), IntVal(0))),
         (And(nn, a == 2, c >= 3), (b + 6, IntVal(4), c - 3)),
         (And(nn, a == 2, c == 2), (b + 6, IntVal(3), IntVal(0))),
         (And(nn, a == 2, c == 1), (b + 5, IntVal(3), IntVal(0))),
         (And(nn, a == 2, c == 0, b % 2 == 0), (IntVal(1), IntVal(1), b / 2 + 1)),
         (And(nn, a == 2, c == 0, b % 2 == 1), 'halt')]
    R.append((Not(Or([g for g, _ in R])), 'halt'))
    return R
M['1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA'] = (3, (1, 1, 4), m4)

def I(n): return IntVal(n)
# DeepMind acceleration map (cryptids), locations: 0 S0p(a,b,c) 1 S0z(a,c) 2 T1(j,m) 3 T0(j,m) 4 T11 5 T3 6 T10 7 sink (Tn, Ea..Ed)
def dm(v):
    l, x, y, z = v
    nn = And(x >= 0, y >= 0, z >= 0)
    R = [(And(l == 0, y == 0), (I(0), I(0), 2 * x + 1, z + 4)), (And(l == 0, y == 1), (I(0), x + 2, I(0), z + 2)),
         (And(l == 0, y == 2), (I(1), x + 2, z, I(0))), (And(l == 0, y >= 3), (I(0), x + 2, y - 3, z)),
         (And(l == 1, y == 0), (I(2), I(0), 2 * x + 3, I(0))), (And(l == 1, y >= 1), (I(0), I(0), 2 * x + 4, y - 1)),
         (And(l == 2, y == 0), (I(7), I(0), I(0), I(0))), (And(l == 2, y == 1), (I(4), I(0), 2 * x + 7, I(0))),
         (And(l == 2, y == 2), (I(0), I(0), 2 * x + 5, I(3))), (And(l == 2, y >= 3), (I(2), x + 2, y - 3, I(0))),
         (And(l == 3, y == 0), (I(1), x + 1, I(0), I(0))), (And(l == 3, y == 1), 'halt'),
         (And(l == 3, y == 2), (I(1), x + 2, I(0), I(0))), (And(l == 3, y >= 3), (I(3), x + 2, y - 3, I(0))),
         (And(l == 4, y == 0), (I(2), I(0), 2 * x + 6, I(0))), (And(l == 4, y == 1), (I(5), I(0), 2 * x + 7, I(0))),
         (And(l == 4, y == 2), (I(7), I(0), I(0), I(0))), (And(l == 4, y >= 3), (I(4), x + 2, y - 3, I(0))),
         (And(l == 5, y == 0), (I(2), I(0), 2 * x + 8, I(0))), (And(l == 5, y == 1), (I(6), I(0), 2 * x + 7, I(0))),
         (And(l == 5, y == 2), (I(7), I(0), I(0), I(0))), (And(l == 5, y >= 3), (I(5), x + 2, y - 3, I(0))),
         (And(l == 6, y == 0), (I(3), I(0), 2 * x + 6, I(0))), (And(l == 6, y == 1), 'halt'), (And(l == 6, y == 2), 'halt'),
         (And(l == 6, y >= 3), (I(6), x + 2, y - 3, I(0))), (l == 7, (I(7), I(0), I(0), I(0)))]
    return [(And(nn, g), t) for g, t in R]
M['1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---'] = (4, (0, 0, 1, 3), dm)
M['1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB'] = (4, (2, 0, 1, 0), dm)
def m7(v):      # Round.lean next (i, j, J)
    i, j, J = v
    ok = And(i >= 1, j >= 1, Or(J == 0, J == 1))
    return [(Not(ok), 'halt'), (And(ok, Or(i == j, i + 1 == j)), 'halt'),
            (And(ok, j + 2 <= i), (i - j - 1, 3 * j + 2 + J, J)),
            (And(ok, i == j + 1, J == 0), (3 * i - 3, I(3), I(1))), (And(ok, i == j + 1, J == 1), (3 * i, I(1), I(0))),
            (And(ok, i + 2 == j, J == 0), (3 * i + 3, I(1), I(0))), (And(ok, i + 2 == j, J == 1), (3 * i + 3, I(3), I(1))),
            (And(ok, i + 2 < j), (j - i - 2, 3 * i + 3 + 2 * J, 1 - J))]
M['1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE'] = (3, (3, 1, 0), m7)
def m8(v):      # Round.lean next (m, k)
    m, k = v
    nn = And(m >= 0, k >= 0)
    return [(And(nn, m % 3 == 0, k >= 1), (4 * (m / 3) + 4, k - 1)), (And(nn, m % 3 == 0, k == 0), (4 * (m / 3) + 4, I(0))),
            (And(nn, m % 3 == 1), (4 * (m / 3) + 4, k + 1)), (And(nn, m % 3 == 2, k == 0), 'halt'),
            (And(nn, m % 3 == 2, k >= 1), (4 * (m / 3) + 5, k + 1))]
M['1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC'] = (2, (8, 1), m8)
# validation: the "never stuck / never small" invariants that Lean proves by hand (orbit_dom, Good): halting cases are
# sent to a sink, only the stuck cases are bad.
def only_stuck(rules, n, stuck):
    def f(v):
        R = rules(v[:n]); out = []
        live = v[n] == 0
        for idx, (g, t) in enumerate(R):
            if t == 'halt':
                out.append((And(live, g), 'halt') if idx in stuck else (And(live, g), tuple(v[:n]) + (I(1),)))
            else: out.append((And(live, g), tuple(t) + (I(0),)))
        out.append((v[n] == 1, tuple(v[:n]) + (I(1),)))
        return out
    return f
M['check:orbit_dom:1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA'] = (3, (74, 30, 0), only_stuck(m1, 2, {0}))
M['check:Good:1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA'] = (4, (1, 1, 4, 0), only_stuck(m4, 3, {10}))
M['check:Valid:1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE'] = (4, (3, 1, 0, 0), only_stuck(m7, 3, {0}))
EXTRA = {'1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA': lambda v: [v[1] - v[0]],
         '1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE': lambda v: [v[1] - v[0]]}
