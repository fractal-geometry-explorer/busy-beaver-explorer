#!/usr/bin/env python3
"""Build pages/holdouts/doucette-family.html from tools/doucette/results/ and page_template.html.

usage: python3 tools/doucette/build_page.py

results/run_NAME.json   the longest run of each map (djump.py --out), checkpoints included
results/tree_NAME_N.json  depth and size of the backward tree of b^n for n <= N (tree.py)
results/pairs_NAME.json   a run with --pairs (consecutive valuations), optional
"""
import json, math, os, glob

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
RES = os.path.join(HERE, 'results')


def growth(b, alpha):
    """Expected digits (base b) gained per step if the valuations are geometric."""
    g = 0.0
    for v in range(200):
        p = (b - 1) / b ** (v + 1)
        g += p * math.log(1 + alpha / b ** (v + 1), b)
    return g


MACHINES = {
    'SN': dict(tnf='1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD', nick='Space Needle (mxdys, 2025)', base=2,
               stands='b + 3 at the visits X(b, 1)', rule='D + 3a + v', exc='none',
               halts='D a power of 2', seq='6, 10, 17, 41, 101, 251, 626, ...',
               lean='halts_iff_pow2 (lean/Collatz.lean)',
               last='2<sup>n+1</sup> &equiv; 2v &minus; 3 (mod 2<sup>v+1</sup> + 3). So v = 1, 4, 7 are impossible, and '
                    'v = 0 needs n &equiv; 0 (mod 4), v = 2 needs n &equiv; 9 (mod 10), v = 3 needs n &equiv; 12 (mod 18), '
                    'v = 5, 6, 8: one class mod 66, 130, 204. Further v (computed): 9, 10, 12, 13, 18, 19, 21-26, ... impossible.',
               never='about 60% of exponents below 400 (no rule as simple as the others)',
               lastLean='last_step_congr, last_step_small (lean/Preimage.lean)',
               preNote='There is no simple pattern here: each possible v contributes one class of n modulo the order of 2 mod 2^(v+1) + 3.'),
    'M31': dict(tnf='1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE', nick='', base=2,
                stands='p + 3 at the samples K(p, 1)', rule='D + a + v', exc='D = 3&middot;2<sup>v</sup>: D + v + 3',
                halts='D a power of 2', seq='5, 7, 10, 13, 19, 28, 33, ...',
                lean='halts_iff_doucette (lean/Doucette.lean)',
                last='v = 0 and n even (D = (2<sup>n+1</sup> + 1)/3), or v = 1 and n &equiv; 3 (mod 4) '
                     '(D = 2(2<sup>n+1</sup> &minus; 1)/5). The exception never steps onto a power of 2.',
                never='n &equiv; 1 (mod 4)', lastLean='last_step, no_pow2_one_mod_four (lean/Preimage.lean)',
                preNote='Exactly the n = 1 mod 4 are missing (no_pow2_one_mod_four).'),
    'M53': dict(tnf='1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC', nick='', base=2,
                stands='p + 3 at the samples S(p, r) that start a run of halvings', rule='D + a + v + r (r = 1 after the start)',
                exc='D = 3&middot;2<sup>v</sup>: D + v + r + 1, next r = 1 or 2', halts='D a power of 2',
                seq='(5, r = 2), 9, 14, 19, 29, 44, ...', lean='halts_iff_doucette (lean/Doucette.lean)',
                last='r = 1: v = 0 and n odd, v = 1 and n &equiv; 2 (mod 4), or v = 2 and n &equiv; 4 (mod 6); r = 2: v = 2 and '
                     'n &equiv; 3 (mod 6), or v = 3 and n &equiv; 6 (mod 8); the exception only from (12, 1) to 16.',
                never='n &equiv; 0 or 8 (mod 12), n &gt; 4', lastLean='last_step, no_pow2_mod_twelve (lean/Preimage.lean)',
                preNote='Exactly the n = 0, 8 mod 12 are missing (no_pow2_mod_twelve).'),
    'M14': dict(tnf='1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB', nick='', base=2,
                stands='n + 2 at the end of each pass P(n)', rule='D + a + v + 2',
                exc='D = 3&middot;2<sup>v</sup>, v even &ge; 2: (3D + 3v + 10)/2', halts='D a power of 2',
                seq='6, 10, 15, 24, 30, 40, 47, ...', lean='halts_iff_doucette (lean/Doucette.lean)',
                last='v = 2 and n &equiv; 3 (mod 6), or v = 3 and n &equiv; 6 (mod 8). The exception never steps onto a power of 2.',
                never='all n except n &equiv; 3 (mod 6) and n &equiv; 6 (mod 8): 17 in every 24',
                lastLean='last_step, halting_exponent (lean/Preimage.lean)',
                preNote='Only n = 3 mod 6 and n = 6 mod 8 survive (halting_exponent).'),
    'M86': dict(tnf='1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB', nick='the base-3 member', base=3,
                stands='p + 1 at the samples S(p, r) that start a run of divisions', rule='D + a + v + r + &rho; + 1',
                exc='D = 3<sup>v</sup>: halts if v + r &equiv; 1 (mod 3), else goes on', halts='D = 3<sup>v</sup> with v + r &equiv; 1 (mod 3)',
                seq='4, 8, 13, 17, 24, 33, ...', lean='halts_iff_doucette (lean/Doucette.lean)',
                last='r = 1: v = 1 (exactly one factor 3), n &equiv; 3 (mod 4) if &rho; = 1 and n &equiv; 0 (mod 4) if &rho; = 2; r = 2: '
                     'v = 0, or v = 2 with &rho; = 2 and n &equiv; 4 (mod 6). The next r is 1, and a halt needs 3 | n.',
                never='with r = 1: every halting value has n &equiv; 0 or 3 (mod 12)',
                lastLean='last_step, halt_from_r1 (lean/Preimage.lean)',
                preNote='Shown: powers of 3 with a predecessor (r = 1); a halt at 3^n also needs 3 | n.'),
}

FILES = [
    ('The fast orbit computation (Python + GMP), with --check against the plain map', 'tools/doucette/djump.py'),
    ('The shift identity and the jump, kernel-checked, no dependencies', 'tools/doucette/lean/Shift.lean'),
    ('Backward trees of the powers', 'tools/doucette/tree.py'),
    ('Run results, checkpoints and hashes', 'tools/doucette/results/'),
    ('The last-step lemmas, one per machine', 'holdouts/&lt;machine&gt;/lean/Preimage.lean (with PowMod.lean)'),
    ('Notes', 'tools/doucette/README.md'),
]


def main():
    data = {'machines': {}, 'runs': {}, 'trees': {}, 'files': FILES}
    alpha = {'SN': 3, 'M31': 1, 'M53': 1, 'M14': 1, 'M86': 1}
    for k, d in MACHINES.items():
        d = dict(d)
        d['short'] = d['tnf']
        d['growth'] = growth(d['base'], alpha[k])
        pf = os.path.join(RES, 'pairs_%s.json' % k)
        if os.path.exists(pf):
            p = json.load(open(pf))['pairs']
            tot = sum(p.values())
            row = {}
            for key, c in p.items():
                a, b = map(int, key.split(','))
                row.setdefault(a, {})[b] = c
            # P(v' = 0 | v) for v = 0..3: should be (b-1)/b for every v
            parts = []
            for a in range(4):
                s = sum(row.get(a, {}).values())
                if s:
                    parts.append('%.4f' % (row[a].get(0, 0) / s))
            d['pairs'] = ('Consecutive terms look independent: over %s pairs, P(next v = 0 | v = 0, 1, 2, 3) = %s '
                          '(independence: %.4f each).' % (f'{tot:,}', ', '.join(parts), (d['base'] - 1) / d['base']))
        data['machines'][k] = d
        rf = os.path.join(RES, 'run_%s.json' % k)
        if os.path.exists(rf):
            r = json.load(open(rf))
            data['runs'][k] = {x: r[x] for x in ('steps', 'digits', 'vmax', 'vrecords', 'hist', 'seconds',
                                                 'final_sha256')}
            if 'seconds_total' in r:
                data['runs'][k]['seconds'] = r['seconds_total']
        tf = sorted(glob.glob(os.path.join(RES, 'tree_%s_*.json' % k)))
        if tf:
            t = json.load(open(tf[-1]))
            data['trees'][k] = [[int(n), dv[0]] for n, dv in sorted(t.items(), key=lambda x: int(x[0]))]
    steps = [data['runs'][k]['steps'] for k in data['runs']]
    sn = data['runs'].get('SN', {}).get('steps', 0)
    data['headline'] = (f'{min(steps):,}' + (f' (Space Needle: {sn:,})' if sn > min(steps) else '')) if steps else ''
    tpl = open(os.path.join(HERE, 'page_template.html')).read()
    out = tpl.replace('/*DATA*/null', json.dumps(data, separators=(',', ':')))
    dst = os.path.join(REPO, 'pages', 'holdouts', 'doucette-family.html')
    open(dst, 'w').write(out)
    print('wrote', dst, len(out), 'bytes')


if __name__ == '__main__':
    main()
