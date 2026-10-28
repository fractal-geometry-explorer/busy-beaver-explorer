"""Which halting lanes can the chain's last pass start be on, by R'^3/L1'^2 at the route's re-entry?  (Untrusted;
`../lean/END_TO_END.md`, "The chain ends at a right end of at least 769".)

`reentry.py sigma` with the forms of the halting-classes census read from its files (`halting-classes/routes` in the
project files): `lanes_r770_1004_forms.txt` (every path of the census at R = 770 to 1,004, its three-wall starts with
W', R' = N/2^m and L1' affine in the start's (b, W, R)) and `lanes_r294_486.json` (the lanes delta and epsilon).  At
the last start of a path the run goes on by full passes, which keep R'^3/L1'^2, to a halting class with right end r;
there R'^3/L1'^2 = r^3/l^2 with l = 3 (mod 7), so at most r^3/9 for the ends r that R' = 16^p r allows among the right
ends of the halting classes (2, 4, 6, 8, 16, 32, 48; and at least 176^3/256^2, `sigma_close`), and at most 177^3/9
for any end below 178 (`noSmall_sigma`).  On a lane value N = c 2^e (c = 1 or 3) R' is fixed, and the pass starts with
R >= 769, every gap at least 448, width at least 2^41 and 15W <= 64(W - b), the shape `blank_halt_open_big` gives
the chain's last pass start, form a polygon in (R, W) on which |L1'| is convex, so its least R'^3/L1'^2 is at a corner.
A path that begins with the loop's own half pass (round 2, R' = R/2) is taken at its landing, the chain's last pass
start there: its forms are rewritten in the landing's coordinates (b = 2b' - W' + 2R' - 4, W = W' - 6, R = 2R').

usage: python3 lane_sigma.py lanes_r770_1004_forms.txt lanes_r294_486.json
"""
import re
import sys
import json
from fractions import Fraction as Fr
from math import log2

G = 2 ** 41
RLO = 769  # `blank_halt_open_big`: the chain's last pass start has R >= 769
HALT_R = (2, 4, 6, 8, 16, 32, 48)  # the right ends of the halting classes (`../lean/thm/PassHaltClasses.lean`)
CLOSE = Fr(176 ** 3, 256 ** 2)  # `sigma_close`: a close right at the chain's end
SIG = Fr(177 ** 3, 9)  # `noSmall_sigma`: full passes end below 178 only if R^3/L^2 <= 177^3/9


def lin(s):
    """'(−b + W + 2R + 22)/64' -> ({'b': -1, 'W': 1, 'R': 2, '1': 22}, 64)"""
    body, den = re.fullmatch(r'\((.*)\)/(\d+)', s.replace('−', '-').replace(' ', '')).groups()
    f = {'b': 0, 'W': 0, 'R': 0, '1': 0}
    for sg, num, v in re.findall(r'([+-]?)(\d*)([bWR]?)', body):
        if num or v:
            f[v or '1'] += (-1 if sg == '-' else 1) * (int(num) if num else 1)
    return f, int(den)


def at_landing(f):
    """a form in the start's (b, W, R), written in its half-pass landing's coordinates"""
    return {'b': 2 * f['b'], 'W': f['W'] - f['b'], 'R': 2 * (f['b'] + f['R']), '1': f['1'] - 4 * f['b'] - 6 * f['W']}


def routes(forms_fn, json_fn):
    """(name, round, R' form, L1' form) at the last three-wall start of each path"""
    paths = []
    for line in open(forms_fn):
        if line.startswith('class'):
            rs = sorted(set(int(r) for r in re.findall(r'\((\d+), \d+, \d+, -?\d+\)', line.split('census')[1])))
            paths.append(('R = ' + ', '.join(map(str, rs)), []))
        elif 'R′' in line:
            m = re.search(r'r(\d+): W′ = W \+ \d+\s+R′ = (\(.*?\)/\d+)\s+L₁′ = (\(.*?\)/\d+)', line)
            paths[-1][1].append((int(m.group(1)), lin(m.group(2)), lin(m.group(3))))
    out = []
    for name, starts in paths:
        if not starts:
            print('%s: no three-wall start after round 0' % name)
            continue
        rnd, Rf, Lf = starts[-1]
        if starts[0][0] == 2:
            if len(starts) == 1:
                print('%s: the half pass is its only three-wall start' % name)
                continue
            Rf, Lf, name = (at_landing(Rf[0]), Rf[1]), (at_landing(Lf[0]), Lf[1]), name + ', at the half-pass landing'
        out.append((name, rnd, Rf, Lf))
    for x in json.load(open(json_fn)):
        if x['lane'] in ('delta', 'epsilon'):
            s = x['three-wall starts (forms in b, W, R of the start; Q = W - b + 2R + 22)'][-1]
            out.append((x['lane'], s['round'], lin(s['R1']), lin(s['L1'])))
    return out


def sigma_min(Rf, Lf, N):
    """least R'^3/L1'^2 over the pass starts of the lane value N (None: there are none).  N = k D + rho R + n0 with
    D = W - b fixes D on each R; R runs from RLO to where the third gap D - R - 1 is 448, and W from max(D + 898, G)
    to 64D/15"""
    (n, dn), (l, dl) = Rf, Lf
    k, rho, n0 = n['W'], n['R'], n['1']
    assert k > 0 and n['b'] == -k
    d0, d1 = Fr(N - n0, k), Fr(-rho, k)  # D = d0 + d1 R
    if d1 >= 1 or (d0 - 449) / (1 - d1) < RLO:
        return None
    Rmax = (d0 - 449) / (1 - d1)
    lines = [(d0 + 898, d1), (Fr(G), Fr(0)), (64 * d0 / 15, 64 * d1 / 15)]
    Rs = {Fr(RLO), Rmax}
    for i in range(len(lines)):
        for j in range(i + 1, len(lines)):
            (a0, a1), (b0, b1) = lines[i], lines[j]
            if a1 != b1 and RLO <= (b0 - a0) / (a1 - b1) <= Rmax:
                Rs.add((b0 - a0) / (a1 - b1))
    mx = None
    for R in Rs:
        D = d0 + d1 * R
        if max(D + 898, G) <= 64 * D / 15:
            for W in (max(D + 898, G), 64 * D / 15):
                L = abs(l['b'] * (W - D) + l['W'] * W + l['R'] * R + l['1']) / dl
                mx = L if mx is None else max(mx, L)
    return None if mx is None else (Fr(N) / dn) ** 3 / mx ** 2


def end_bound(Rp):
    """the largest r^3/9 over the right ends r of the halting classes with R' = 16^p r, and at least sigma_close"""
    rs = [r for r in HALT_R if any(Rp == r * 16 ** p for p in range(64))]
    return max([Fr(r ** 3, 9) for r in rs] + [CLOSE])


def lane(Rf):
    """R''s numerator as kQ + aR + c (Q = W - b + 2R + 22), divided by its largest power of two s"""
    n = Rf[0]
    k, a, c = n['W'], n['R'] - 2 * n['W'], n['1'] - 22 * n['W']
    s = 1
    while k % (2 * s) == 0 and a % (2 * s) == 0 and c % (2 * s) == 0:
        s *= 2
    k, a, c = k // s, a // s, c // s
    txt = '%dQ' % k if k != 1 else 'Q'
    if a:
        txt += (' %s %dR' % ('+' if a > 0 else '-', abs(a))).replace(' 1R', ' R')
    if c:
        txt += ' %s %d' % ('+' if c > 0 else '-', abs(c))
    return txt, s


def main():
    seen = set()
    for name, rnd, Rf, Lf in routes(*sys.argv[1:3]):
        key = (tuple(Rf[0].values()), Rf[1], tuple(Lf[0].values()), Lf[1])
        if key in seen:
            continue
        seen.add(key)
        form, s = lane(Rf)
        vals, below177, belowEnd = [], {1: [], 3: []}, {1: [], 3: []}
        for c in (1, 3):
            for e in range(20, 110):
                sg = sigma_min(Rf, Lf, c * 2 ** e * s)
                if sg is None:
                    continue
                vals.append(sg)
                Rp = Fr(c * 2 ** e * s, Rf[1])
                wmax = log2(64 * Fr(c * 2 ** e * s - Rf[0]['R'] * RLO - Rf[0]['1'], Rf[0]['W']) / 15)
                if sg <= SIG:
                    below177[c].append((e, wmax))
                if Rp.denominator == 1 and sg <= end_bound(Rp):
                    belowEnd[c].append((e, wmax))
        print('%s, round %d: %s = 2^j or 3 * 2^j (%d values), least R\'^3/L1\'^2 %.4g' %
              (name, rnd, form, len(vals), float(min(vals))))
        for what, low in (('177^3/9', below177), ('the end\'s r^3/9', belowEnd)):
            top = max([w for c in low for _, w in low[c]], default=None)
            print('   at most %s at 2^j for j in %s, 3 * 2^j for j in %s%s' % (
                what, [e for e, _ in low[1]] or 'none', [e for e, _ in low[3]] or 'none',
                '' if top is None else ' (widths up to 2^%.1f)' % top))


if __name__ == '__main__':
    main()
