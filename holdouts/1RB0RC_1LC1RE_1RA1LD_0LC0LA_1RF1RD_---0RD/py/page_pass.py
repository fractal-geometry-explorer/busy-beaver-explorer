"""page_pass.py: write the explainer section "passes" of status.json from the files it rests on.

    python3 py/page_pass.py && python3 holdouts/build_pages.py 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD

Sources: the pass panel (py/pass_panel.js, on the jump panel of the section "jumps"), the long run of c/prun.c
(c/run_pass.txt: checkpoint lines "passes frames steps tag a j r ..." and lines "close pass P tag(a,j,r) d D"), the
statistics near the boundary (c/near_1e11.txt, read by py/near.py) and the random orbits (c/rate.txt, prun rate).
"""
import json, math, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import near
from page_jumps import sci

ROOT = os.path.join(HERE, '..')


def load_run():
    checks, close = [], []
    for line in open(os.path.join(ROOT, 'c', 'run_pass.txt')):
        p = line.split()
        if not p:
            continue
        if p[0] == 'close':
            tag = p[3][0]
            a, j, r = (int(v) for v in p[3][2:-1].split(','))
            close.append((int(p[2]), tag, a, j, r, int(p[5])))
        elif p[0].isdigit():
            checks.append((int(p[0]), int(p[1]), int(p[2]), p[3], int(p[4]), int(p[5]), int(p[6])))
    return checks, close


def load_rate():
    by = {}
    for line in open(os.path.join(ROOT, 'c', 'rate.txt')):
        if line.startswith('rate'):
            p = line.split()
            n0 = int(p[p.index('N0') + 1].rstrip(':'))
            h, s = by.get(n0, (0, 0.0))
            by[n0] = (h + int(p[p.index('halts') + 1]), s + float(p[p.index('1/N') + 1]))
    rates = [h / s for h, s in by.values()]
    return sum(h for h, s in by.values()), sum(s for h, s in by.values()), min(rates), max(rates)


def cobweb_svg():
    X = lambda x: 20 + 260 * x
    Y = lambda y: 20 + 260 * (1 - y)
    o = ['<svg class="cob" viewBox="0 0 300 318" role="img" aria-label="the map x to 4x/3 or 4x - 3 with the orbit of '
         'the run" style="width:100%;max-width:340px;height:auto;font:10px var(--mono);">',
         f'<rect x="20" y="20" width="260" height="260" fill="none" stroke="var(--line)"/>',
         f'<line x1="{X(0)}" y1="{Y(0)}" x2="{X(1)}" y2="{Y(1)}" stroke="var(--line)"/>',
         f'<line x1="{X(0)}" y1="{Y(0)}" x2="{X(0.75)}" y2="{Y(1)}" stroke="var(--accent)" stroke-width="2"/>',
         f'<line x1="{X(0.75)}" y1="{Y(0)}" x2="{X(1)}" y2="{Y(1)}" stroke="var(--computed)" stroke-width="2"/>',
         f'<line x1="{X(0.75)}" y1="{Y(0)}" x2="{X(0.75)}" y2="{Y(1)}" stroke="var(--open)" stroke-dasharray="4 3"/>',
         f'<text x="{X(0.75) + 4}" y="{Y(0.62)}" fill="var(--open)">halting</text><text x="{X(0.75) + 4}" y="{Y(0.62) + 12}" fill="var(--open)">rows</text>',
         f'<text x="{X(0.3)}" y="{Y(0.55)}" fill="var(--accent)">growth 4x/3</text>',
         f'<text x="{X(0.79)}" y="{Y(0.08)}" fill="var(--computed)">drain 4x&minus;3</text>',
         f'<text x="{X(0)}" y="{Y(0) + 32}" fill="var(--muted)">0</text>',
         f'<text x="{X(0.75)}" y="{Y(0) + 32}" text-anchor="middle" fill="var(--muted)">3/4</text>',
         f'<text x="{X(1)}" y="{Y(0) + 32}" text-anchor="end" fill="var(--muted)">1</text>',
         f'<text x="{X(0.06)}" y="{Y(0.95)}" fill="var(--muted)">x = a/(a + j + r)</text>',
         '<path class="web" d="" fill="none" stroke="var(--heur)" stroke-width="1"/>',
         '<g class="dots"></g></svg>']
    return ''.join(o)


def build():
    checks, close = load_run()
    P, F, S = checks[-1][0], checks[-1][1], checks[-1][2]
    hexp, h2, hist, end = near.load(os.path.join(ROOT, 'c', 'near_1e11.txt'))
    Ssum = sum(hexp)
    by_d = {}
    for (t, d), v in hist.items():
        by_d[d] = by_d.get(d, 0) + sum(v)
    nd = sum(by_d.get(d, 0) for d in range(-16, 17))
    nall = sum(sum(v) for (t, e, jp, dl), v in h2.items() if -16 <= dl <= 16)
    rall = nall / (33 * 0.75 * Ssum)
    halts, Srate, rmin, rmax = load_rate()
    ratio = nd / (33 * 0.25 * Ssum)
    lam = 0.25 * ratio
    Sfrom1000 = sum(hexp[10:])
    rows = ''.join(f'<tr><td>{p:,}</td><td>{sci(f)}</td><td>{sci(s)}</td><td><code>{t}({a:,}, {j:,}, {r:,})</code></td></tr>'
                   for p, f, s, t, a, j, r in [c for c in checks if c[0] in (10 ** 10, 10 ** 11, 10 ** 12) or c is checks[-1]])
    near_rows = ''.join(f'<tr><td>{p:,}</td><td><code>{t}({a:,}, {b:,}, {r:,})</code></td><td>{d:+d}</td></tr>'
                        for p, t, a, b, r, d in close if abs(d) <= 2)
    style = ('<style>#passPanel .pstate{font-family:var(--mono);font-size:.85rem;overflow-wrap:anywhere}'
             '#passPanel .pcount{font-size:.85rem;color:var(--fg2);margin-top:6px}'
             '#passPanel .plog{font-family:var(--mono);font-size:.78rem;max-height:260px;overflow:auto;'
             'border-top:1px solid var(--line);margin-top:12px;padding-top:8px;overflow-wrap:anywhere}</style>')
    panel = open(os.path.join(HERE, 'pass_panel.js')).read()
    sec = {
        'id': 'passes', 'eyebrow': 'Macro structure', 'heading': 'Passes: the whole run as a map of one number',
        'html': [
            '<p>A <b>pass</b> runs from one zigzag start to the next: a zigzag, a few single frames and a sweep. Away '
            'from the line where both blocks run out together it is one affine map, proved for all sizes in '
            '<code>lean/Pass.lean</code> (13 theorems, each a chain of the jump lemmas, with its exact frame count). '
            'Write the zigzag start <code>t(a, j, r)</code> with <code>t</code> = y or Y and <code>a = 3q + e</code>:</p>',
            '<pre>drain   r &le; q &minus; 1:  t(a, j, r)  &rarr;  t(a &minus; 3r + 1, 0, 4r + 2j + 2)       drain_y, drain_Y\n'
            'growth  r &ge; q + 7:  t(a, j, r)  &rarr;  t\'(4q + 2j + c, 0, r &minus; q &minus; d)       grow_*\n\n'
            '        t e  j even: t\' c d   j odd: t\' c d\n'
            '        y 0          y  2 1          y  5 4\n'
            '        y 1          y  7 4          y  4 1\n'
            '        y 2          Y  2 1          Y  5 4\n'
            '        Y 0          y  5 1          y  8 4\n'
            '        Y 1          y 11 5          y  8 2\n'
            '        Y 2          y(5, j + 2q + 2, r &minus; q &minus; 1)  (a short zigzag follows)</pre>',
            '<p>Only within 6 of the line <code>r = q</code> does the run go back to jumps, and that is where all five '
            'halting rows lie (<code>d</code> = 0 means <code>r &minus; q</code> = 2 for y and 3 for Y). In the run '
            'from blank tape that happens about once in 10<sup>8</sup> passes. <code>pass</code> is the 13 cases where '
            'they apply and a jump elsewhere; <code>pass_sound</code> proves each pass is that many frames of the '
            'frame map, and <code>native_decide</code> runs 10<sup>8</sup> passes (<code>passes_frames</code>): '
            '<b>no halt in the first 3.9&middot;10<sup>15</sup> frames</b> (<code>no_halt_passes</code>, '
            '1.1&middot;10<sup>23</sup> machine steps), against 1.5&middot;10<sup>14</sup> by 10<sup>8</sup> jumps.</p>',
            '<p><b>One number.</b> In both cases the total <code>N = a + j + r</code> (j is 0 at almost every start) changes by a few cells only, so the '
            'state is essentially the fraction <code>x = a/N</code>, and a pass is the map '
            '<code>x &rarr; 4x/3</code> (growth, x &lt; 3/4) or <code>x &rarr; 4x &minus; 3</code> (drain): two '
            'full branches of slopes 4/3 and 4, whose invariant density is uniform. The epochs of the section above '
            'are runs of the first branch ended by one step of the second. A halt needs <code>x</code> to land '
            'exactly on the branch point 3/4, to the cell. The panel runs the pass map from blank tape (BigInt; the '
            'same passes as <code>c/prun.c</code> on the first 300,000, <code>py/pass_panel_test.js</code>) and '
            'draws the last 40 values of <code>x</code>:</p>',
            style,
            '<div class="panel" id="passPanel">' + cobweb_svg() + '<div class="controls">'
            '<button type="button" class="p1 primary">1 pass</button> <button type="button" class="p10">10</button> '
            '<button type="button" class="p1k">1,000</button> <button type="button" class="p100k">100,000</button> '
            '<button type="button" class="preset">Reset</button></div>'
            '<div class="pstate"></div><div class="pcount"></div><div class="plog"></div>'
            '<div class="cap"><span class="ev k">Kernel</span> The 13 cases are theorems of <code>lean/Pass.lean</code>; '
            'near the boundary the panel takes the jumps of the section above.</div></div>',
            '<script>' + panel + '</script>',
            f'<p><b>The run.</b> <code>c/prun.c</code> iterates the pass map with 64-bit sizes and 128-bit step '
            f'counts, 5.7 times as fast as the jump map, and agrees with <code>frun</code> pass by pass on the first '
            f'2&middot;10<sup>10</sup> passes (<code>prun check</code>) and on the frame, frame count and step count '
            f'after 10<sup>9</sup> jumps. It ran {sci(P)} passes, {sci(F)} frames, <b>{sci(S)} machine steps</b>, '
            'without a halt:</p>',
            '<div style="overflow-x:auto"><table class="tbl"><thead><tr><th>passes</th><th>frames</th><th>steps</th>'
            '<th>zigzag start</th></tr></thead><tbody>' + rows + '</tbody></table></div>',
            '<p>Zigzag starts within 2 of a halting row:</p>'
            '<div style="overflow-x:auto"><table class="tbl"><thead><tr><th>pass</th><th>zigzag start</th><th>d</th>'
            '</tr></thead><tbody>' + near_rows + '</tbody></table></div>',
            f'<p><b>How likely is a halt.</b> If <code>x</code> were spread uniformly at the scale of one cell, a pass '
            'would land on a given row with chance about 1/(4N), and N grows by about 2 a pass, so the expected '
            'number of hits grows like the logarithm of the pass count (not like ln ln J: an epoch lasts a bounded '
            f'number of passes on average). The run follows this model: the first 10<sup>11</sup> passes have {nall} '
            f'zigzag starts within 16 of the boundary, {rall:.2f} of the uniform count, and {nd} within 16 of a row, '
            f'{ratio:.2f} of it (<code>py/near.py</code>; N = a + j + r). That gives a halting hazard of {lam:.2f} '
            'per unit of &Sigma;1/N. Random orbits of the same map (<code>prun rate</code>, '
            f'{int(halts):,} halts, every one right after a start with <code>d = 0</code>) give between {rmin:.2f} '
            f'and {rmax:.2f} depending on the size, as orbits of the map merge and are far from independent. '
            f'For the run from blank tape &Sigma;1/N is '
            f'{Sfrom1000:.1f} from pass 1,000 to 10<sup>11</sup>, so about {lam * Sfrom1000:.1f} hits were expected '
            f'there (chance of none {math.exp(-lam * Sfrom1000):.0%}); each further factor 10 of passes adds about '
            f'{lam * math.log(10) / 2.08:.2f}. If that holds the machine halts with probability 1, with a median around '
            f'10<sup>{math.log10(P) + math.log(2) / (lam / 2.08) / math.log(10):.0f}</sup> passes and '
            f'10<sup>{math.log10(S) + 3 * math.log(2) / (lam / 2.08) / math.log(10):.0f}</sup> steps, '
            f'which the pass map reaches in about {10 ** (math.log10(P) + math.log(2) / (lam / 2.08) / math.log(10)) / 7.5e7 / 86400:.0f} days of one core '
            '(the earlier estimate was 10<sup>53</sup> steps).</p>',
        ]}
    return sec, (P, F, S, lam, Sfrom1000, ratio)


if __name__ == '__main__':
    sec, nums = build()
    p = os.path.join(ROOT, 'status.json')
    st = json.load(open(p))
    secs = [s for s in st['explainer']['sections'] if s['id'] != 'passes']
    i = next(k for k, s in enumerate(secs) if s['id'] == 'close') + 1
    secs[i:i] = [sec]
    st['explainer']['sections'] = secs
    json.dump(st, open(p, 'w'), indent=1, ensure_ascii=False)
    open(p, 'a').write('\n')
    print('passes %d frames %d steps %d; hazard %.3f, sum 1/N from pass 1000 %.2f, near ratio %.2f' % nums)
