"""Exact maps of the route tree's leaves (the output of Pieces.lean): the return pieces of the two-marker state.

Each leaf's class is {(m0(y), E0(y))}; every position of its round start is an affine form in y, and since m0 and E0
are independent forms, every position is an exact affine function of the start's m and E.  A leaf that is a clean
tape with two markers is a return piece: G 1, M m, M E − 2 runs to G 1, M m', M E' − 2 with m' = a·m + b·E + c and
E' = E + e on the piece's class.  Untrusted (exact rationals, but no proof); `lean_maps/GmmMaps.lean` checks the main
pieces in Lean.

usage: python3 pieces.py DUMP [top]          how the start class splits, by digits; the largest pieces with their maps
       python3 pieces.py DUMP branching      how fast the classes of chains of returns multiply, per digit
       python3 pieces.py DUMP locks          the shape of all maps; fixed lines; which have integer points
       python3 pieces.py DUMP pairs N        fixed lines of the two-piece words of the N largest pieces
       python3 pieces.py DUMP halving J      the longest run of pure-halving pieces (m' = m/2^r), from E mod 2^J
       python3 pieces.py DUMP emit OUT W...  write the classes and maps of the pieces W... as JSON (for GmmMaps.lean)
"""
import json
import sys
from collections import defaultdict
from fractions import Fraction as F
from math import gcd


def form(s):
    k, a, b = (int(x) for x in s.split(','))
    return k, a, b


def parse(fn):
    head = None
    leaves = []
    for line in open(fn):
        if line.startswith('#'):
            head = line.strip()
            continue
        kind, D, r, word, m0, E0, W, marks = line.split()
        ms = []
        for x in marks.split(';'):
            t, f = x.split(':')
            ms.append((t, form(f)))
        leaves.append(dict(kind=kind, D=int(D), r=int(r), word=word.split('.'), m0=form(m0), E0=form(E0),
                           W=form(W), marks=ms))
    d = int(head.split('d = ')[1].split(':')[0])
    return head, d, leaves


def solve(m0, E0, p):
    """p = α m + β E + γ, with m = m0(y), E = E0(y)."""
    km, a0, a1 = m0
    kE, b0, b1 = E0
    kp, p0, p1 = p
    det = a0 * b1 - a1 * b0
    al = F(p0 * b1 - p1 * b0, det)
    be = F(a0 * p1 - a1 * p0, det)
    ga = kp - al * km - be * kE
    return al, be, ga


def fstr(x):
    return str(x) if x.denominator == 1 else f'{x.numerator}/{x.denominator}'


def affstr(al, be, ga, v1='m', v2='E'):
    parts = []
    if al:
        parts.append(f'{fstr(al)}·{v1}')
    if be:
        parts.append(f'{fstr(be)}·{v2}')
    if ga or not parts:
        parts.append(fstr(ga))
    return ' + '.join(parts).replace('+ -', '− ')


def egcd(a, b):
    """(u, v) with u·a + v·b = gcd(a, b) ≥ 0."""
    if b == 0:
        return (1 if a >= 0 else -1, 0)
    u, v = egcd(b, a % b)
    return v, u - (a // b) * v


def hnf(m0, E0):
    """The class {(m0(y), E0(y))} as m = km + h·s + x·t, E = kE + g·t over all integers s, t (small constants)."""
    km, a0, a1 = m0
    kE, b0, b1 = E0
    det = abs(a0 * b1 - a1 * b0)
    g = gcd(b0, b1)
    u, v = egcd(b0, b1)
    assert u * b0 + v * b1 == g
    h = det // g
    x = (u * a0 + v * a1) % h
    t0 = (kE % g - kE) // g
    kE2 = kE + t0 * g
    km2 = (km + x * t0) % h
    return km2, h, x, kE2, g


def class_str(m0, E0):
    km, h, x, kE, g = hnf(m0, E0)
    return f'E ≡ {kE} mod {g}, m ≡ {km} + {x}·(E − {kE})/{g} mod {h}'


def returns(leaves, d):
    """The return pieces: (measure, a, b, c, e, leaf)."""
    out = []
    for L in leaves:
        if L['kind'] != 'clean' or len(L['marks']) != 2:
            continue
        (_, p1), _ = L['marks']
        a, b, c = solve(L['m0'], L['E0'], p1)
        wa, wb, e = solve(L['m0'], L['E0'], L['W'])
        assert wa == 0 and wb == 1
        out.append((F(2 ** L['D'], 2 ** d), a, b, c, e, L))
    return out


def fixed_line(a, b, c, e):
    """The fixed line m = λE + μ of a piece repeated (it maps the line to itself, E moving by e)."""
    lam = b / (1 - a)
    return lam, (c - lam * e) / (1 - a)


def summary(fn, top):
    head, d, leaves = parse(fn)
    print(head)
    tot = F(0)
    bykind = defaultdict(F)
    bydig = defaultdict(lambda: defaultdict(F))
    pieces = defaultdict(lambda: [0, F(0), None])
    bad = 0
    for L in leaves:
        mu = F(2 ** L['D'], 2 ** d)
        tot += mu
        km, a0, a1 = L['m0']
        kE, b0, b1 = L['E0']
        if F(4, abs(a0 * b1 - a1 * b0)) != mu:
            bad += 1
        kind = L['kind']
        if kind == 'clean':
            kind = 'return' if len(L['marks']) == 2 else 'one-marker'
        bykind[kind] += mu
        bydig[kind][d - L['D']] += mu
        if kind == 'return':
            pc = pieces['.'.join(L['word'])]
            pc[0] += 1
            pc[1] += mu
            if pc[2] is None:
                pc[2] = L
    print(f'total measure {tot} (should be 1); classes whose index disagrees with their depth: {bad}')
    for k, v in sorted(bykind.items()):
        print(f'  {k}: {float(v):.6f}')
    print('measure by digits used, cumulative share of each kind ending by then:')
    acc = defaultdict(F)
    for dd in range(0, d + 1):
        row = []
        for k in ('return', 'one-marker', 'entry', 'cut'):
            acc[k] += bydig[k].get(dd, F(0))
            row.append(f'{k} {float(acc[k]):.4f}')
        if any(bydig[k].get(dd) for k in bydig):
            print(f'  {dd:2d} digits: ' + ', '.join(row))
    print(f'return pieces: {len(pieces)} words; the {top} largest by measure:')
    for w, (cnt, mu, L) in sorted(pieces.items(), key=lambda x: -x[1][1])[:top]:
        (_, p1), _ = L['marks']
        a, b, c = solve(L['m0'], L['E0'], p1)
        _, _, e = solve(L['m0'], L['E0'], L['W'])
        if b == 0 and c == 0:
            fix = 'm = 0 (pure halving: the marker runs into the gap)'
        else:
            lam, mu0 = fixed_line(a, b, c, e)
            fix = f'm = {affstr(lam, 0, mu0, "E")}'
        print(f'  {w}: {cnt} class(es), measure {float(mu):.6f} ({fstr(mu)}), {L["r"]} rounds')
        print(f"      m' = {affstr(a, b, c)}, E' = E + {fstr(e)};  class {class_str(L['m0'], L['E0'])};  "
              f'repeated: {fix}')


def branching(fn):
    """Chains of returns as a branching process: a piece of k digits has measure 2^-k; the classes of chains of
    returns at depth n multiply by g per digit and their measure falls by ρ = g/2, where Σ_pieces (2ρ)^-k = 1."""
    head, d, leaves = parse(fn)
    rs = returns(leaves, d)
    ks = defaultdict(int)
    for r in rs:
        ks[r[5]['D']] += 1
    ks = {d - D: c for D, c in ks.items()}

    def f(rho):
        return sum(c * (2 * rho) ** (-k) for k, c in ks.items())
    lo, hi = 0.5, 1.0
    for _ in range(100):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if f(mid) > 1 else (lo, mid)
    tot = sum(r[0] for r in rs)
    mean = sum(r[0] * (d - r[5]['D']) for r in rs) / tot
    print(f'{head}\nreturns: measure {float(tot):.5f}, {float(mean):.3f} digits per return on average; chains of '
          f'returns: classes multiply by {2 * lo:.4f} per digit, measure falls by {lo:.4f} per digit')


def locks(fn):
    head, d, leaves = parse(fn)
    rows = returns(leaves, d)
    tot = sum(r[0] for r in rows)
    print(f'{head}\nreturn pieces: {len(rows)} classes, measure {float(tot):.5f}')
    es = defaultdict(F)
    for r in rows:
        es[r[4]] += r[0]
    print("  E' − E (measure):", ', '.join(f'{fstr(k)}: {float(v):.4f}' for k, v in sorted(es.items())[:12]),
          '...' if len(es) > 12 else '')
    print("  E' − E always a multiple of 6:", all(r[4] % 6 == 0 for r in rows))
    print('  coefficient a of m always u/2^r with u odd:', all(r[1].numerator % 2 == 1 and r[1].denominator > 1 and
                                                              r[1].denominator & (r[1].denominator - 1) == 0
                                                              for r in rows),
          '; largest a:', fstr(max(r[1] for r in rows)), '; pieces with u = 1:',
          f'{float(sum(r[0] for r in rows if r[1].numerator == 1)):.5f} of the measure')
    halving = [r for r in rows if r[2] == 0 and r[3] == 0]
    other = [r for r in rows if not (r[2] == 0 and r[3] == 0)]
    print(f"  pure halving (m' = a·m): {len(halving)} classes, measure {float(sum(r[0] for r in halving)):.5f}; a in "
          f"{', '.join(fstr(x) for x in sorted(set(r[1] for r in halving), reverse=True)[:8])}, ...")
    print(f'  the rest: {len(other)} classes, measure {float(sum(r[0] for r in other)):.5f}, every one with b > 0:',
          all(r[2] > 0 for r in other))
    bes = defaultdict(F)
    for r in other:
        bes[min(int(r[2] * 8), 7)] += r[0]
    print('  where the rest put the marker, b = coefficient of E, by eighths (measure):',
          ', '.join(f'[{k}/8, {k + 1}/8): {float(v):.4f}' for k, v in sorted(bes.items())))
    integral = []
    mods = defaultdict(int)
    for r in other:
        mu, a, b, c, e, L = r
        lam, mu0 = fixed_line(a, b, c, e)
        q = lam.denominator
        if (q * mu0).denominator == 1:
            integral.append(('.'.join(L['word']), fstr(lam), fstr(mu0)))
        else:
            mods[(q * mu0).denominator] += 1
    print(f'  fixed lines with integer points among the rest: {len(integral)} of {len(other)} {integral[:5]}')
    print('  the countdowns\' moduli (denominator of q·μ, q the denominator of λ), most common:',
          sorted(mods.items(), key=lambda x: -x[1])[:8])


def in_class(L, m, E):
    km, a0, a1 = L['m0']
    kE, b0, b1 = L['E0']
    det = a0 * b1 - a1 * b0
    dm, dE = m - km, E - kE
    return (dm * b1 - a1 * dE) % det == 0 and (a0 * dE - b0 * dm) % det == 0


def pairs(fn, top):
    """Two-piece words AB of the `top` largest pieces: the fixed line of AB repeated, and whether it has an integer
    point (m, E) with (m, E) in A's class and A(m, E) in B's class (searched over one period of the classes)."""
    head, d, leaves = parse(fn)
    P = sorted(returns(leaves, d), key=lambda r: -r[0])[:top]
    print(f'{head}\nthe {len(P)} largest pieces cover measure {float(sum(r[0] for r in P)):.5f}')
    cand = 0
    hits = []
    for A in P:
        for B in P:
            _, a1, b1, c1, e1, LA = A
            _, a2, b2, c2, e2, LB = B
            a, b, c, e = a1 * a2, a2 * b1 + b2, a2 * c1 + b2 * e1 + c2, e1 + e2
            lam, mu = fixed_line(a, b, c, e)
            q = lam.denominator
            if (q * mu).denominator != 1:
                continue
            cand += 1
            per = q
            for L in (LA, LB):
                det = abs(L['m0'][1] * L['E0'][2] - L['m0'][2] * L['E0'][1])
                per = per * det // gcd(per, det)
            for E in range(1, min(per, 1 << 22) + 1, 2):
                m = lam * E + mu
                if m.denominator != 1 or not in_class(LA, int(m), E):
                    continue
                m1 = a1 * m + b1 * E + c1
                if m1.denominator == 1 and in_class(LB, int(m1), E + int(e1)):
                    hits.append(('.'.join(LA['word']), '.'.join(LB['word']), fstr(lam), fstr(mu), (int(m), E)))
                    break
    nz = [h for h in hits if h[2] != '0' or h[3] != '0']
    print(f'two-piece words whose fixed line has integer points: {cand}; with a point in both classes: {len(hits)}; '
          f'of those, fixed line other than m = 0 (the gap): {len(nz)} {nz[:5]}')


def halving(fn, J):
    """Runs of pure-halving pieces: each needs m ≡ 0 mod 2^(r+1) (any m with enough factors 2 will do) and E in a
    class mod 2^j, and moves E by e; follow E mod 2^J through all pure-halving pieces whose modulus is at most 2^J
    (larger moduli are allowed wherever they are consistent, which can only lengthen the runs)."""
    head, d, leaves = parse(fn)
    H = []
    for r in returns(leaves, d):
        mu, a, b, c, e, L = r
        if b == 0 and c == 0:
            km, h, x, kE, g = hnf(L['m0'], L['E0'])
            H.append((kE % g, g, int(e)))
    M = 1 << J
    adj = [[] for _ in range(M)]
    for (r, g, e) in H:
        gg = min(g, M)
        for x in range(r % gg, M, gg):
            adj[x].append((x + e) % M)
    sys.setrecursionlimit(1 << 20)
    state = [0] * M
    depth = [0] * M
    INF = 10 ** 9

    def dfs(x):
        state[x] = 1
        best = 0
        for y in adj[x]:
            if state[y] == 1:
                best = INF
            elif state[y] == 0:
                best = max(best, 1 + dfs(y))
            else:
                best = max(best, 1 + depth[y])
        state[x] = 2
        depth[x] = min(best, INF)
        return depth[x]
    mx = 0
    for x in range(1, M, 2):
        mx = max(mx, dfs(x) if state[x] == 0 else depth[x])
    print(f'{head}\n{len(H)} pure-halving classes (moduli of E up to {max(g for _, g, _ in H)}); following E mod 2^{J}: '
          f'longest run of pure-halving returns {"unbounded (a cycle)" if mx >= INF else mx}')


def emit(fn, out, words):
    head, d, leaves = parse(fn)
    found = {}
    for r in returns(leaves, d):
        mu, a, b, c, e, L = r
        w = '.'.join(L['word'])
        if w not in words:
            continue
        assert w not in found, ('piece with more than one class', w)
        km, h, x, kE, g = hnf(L['m0'], L['E0'])
        found[w] = dict(word=w, km=km, h=h, x=x, kE=kE, g=g, a=str(a), b=str(b), c=str(c), e=str(e), measure=str(mu))
    missing = [w for w in words if w not in found]
    assert not missing, missing
    json.dump([found[w] for w in words], open(out, 'w'), indent=1)
    print(f'wrote {out}: {len(words)} pieces')


if __name__ == '__main__':
    fn = sys.argv[1]
    mode = sys.argv[2] if len(sys.argv) > 2 else '30'
    if mode == 'branching':
        branching(fn)
    elif mode == 'locks':
        locks(fn)
    elif mode == 'pairs':
        pairs(fn, int(sys.argv[3]))
    elif mode == 'halving':
        halving(fn, int(sys.argv[3]))
    elif mode == 'emit':
        emit(fn, sys.argv[3], sys.argv[4:])
    else:
        summary(fn, int(mode))
