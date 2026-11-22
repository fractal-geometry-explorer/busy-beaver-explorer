"""page_jumps.py: write the explainer sections "jumps" and "close" of status.json from the files they rest on.

    python3 py/page_jumps.py && python3 holdouts/build_pages.py 1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD

Sources: the 78 cases (py/gen_js.py, read from the Lean files), the jump map and panel (py/jumps_panel.js), and the
long run of c/frun.c in close mode (c/run_close.txt: checkpoint lines "jumps frames steps tag l j r" and lines
"close jump J tag(a,j,r) d D").
"""
import json, math, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_js

ROOT = os.path.join(HERE, '..')


def sci(x, digits=2):
    x = int(x)
    if x < 10 ** 6:
        return f'{x:,}'
    e = len(str(x)) - 1
    m = x / 10 ** e
    return f'{m:.{digits - 1}f}&middot;10<sup>{e}</sup>'


def load_run():
    checks, close = [], []
    for line in open(os.path.join(ROOT, 'c', 'run_close.txt')):
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


def svg_close(close, jmax, D=16):
    """|d| against log10 J for the close calls with |d| <= D."""
    W, H, x0, y0, x1, y1 = 560, 230, 46, 16, 545, 196
    lx = lambda j: x0 + (x1 - x0) * math.log10(max(j, 1)) / math.log10(jmax)
    ly = lambda d: y1 - (y1 - y0) * d / D
    o = [f'<svg viewBox="0 0 {W} {H}" role="img" aria-label="close calls: distance to a halting row against jump number"'
         ' style="width:100%;max-width:560px;height:auto;font:11px var(--mono);">',
         f'<line x1="{x0}" x2="{x1}" y1="{y1}" y2="{y1}" stroke="var(--line)"/>',
         f'<line x1="{x0}" x2="{x0}" y1="{y0}" y2="{y1}" stroke="var(--line)"/>']
    for e in range(0, int(math.log10(jmax)) + 1, 2):
        x = lx(10 ** e)
        o.append(f'<line x1="{x:.1f}" x2="{x:.1f}" y1="{y1}" y2="{y1 + 4}" stroke="var(--line-strong)"/>'
                 f'<text x="{x:.1f}" y="{y1 + 16}" text-anchor="middle" fill="var(--muted)">10^{e}</text>')
    for d in (0, 4, 8, 12, 16):
        o.append(f'<text x="{x0 - 6}" y="{ly(d) + 4:.1f}" text-anchor="end" fill="var(--muted)">{d}</text>')
    o.append(f'<line x1="{x0}" x2="{x1}" y1="{ly(0):.1f}" y2="{ly(0):.1f}" stroke="var(--open)" stroke-dasharray="4 3"/>')
    o.append(f'<text x="{x1}" y="{ly(0) - 5:.1f}" text-anchor="end" fill="var(--open)">d = 0 halts</text>')
    for j, tag, a, b, r, d in close:
        if abs(d) <= D:
            col = 'var(--accent)' if tag == 'y' else 'var(--heur)'
            o.append(f'<circle cx="{lx(j):.1f}" cy="{ly(abs(d)):.1f}" r="3.2" fill="{col}">'
                     f'<title>jump {j:,}: {tag}({a:,}, {b:,}, {r:,}), d = {d:+d}</title></circle>')
    o.append(f'<text x="{(x0 + x1) / 2:.0f}" y="{H - 2}" text-anchor="middle" fill="var(--muted)">jump number (log scale)</text>')
    o.append('</svg>')
    return ''.join(o)


def heuristic(close, jmax, D=16, j0=1000):
    ev = [c for c in close if abs(c[5]) <= D and c[0] >= j0]
    dl = math.log(math.log(jmax)) - math.log(math.log(j0))
    lam = len(ev) / dl / (2 * D + 1)
    exp_seen = lam * (math.log(math.log(jmax)) - math.log(math.log(10)))
    med = math.log(math.log(jmax)) + math.log(2) / lam
    return lam, exp_seen, med, len(ev)


def build():
    checks, close = load_run()
    J, F, S = checks[-1][0], checks[-1][1], checks[-1][2]
    lam, exp_seen, med, nev = heuristic(close, J)
    cases = gen_js.build()
    panel = open(os.path.join(HERE, 'jumps_panel.js')).read()
    near = [c for c in close if abs(c[5]) <= 2]
    rows = ''.join(f'<tr><td>{j:,}</td><td><code>{t}({a:,}, {b:,}, {r:,})</code></td><td>{d:+d}</td></tr>'
                   for j, t, a, b, r, d in near)
    style = ('<style>#jumpPanel .jbars{display:flex;height:14px;border-radius:4px;overflow:hidden;margin:10px 0;'
             'background:var(--sunk)}#jumpPanel .jb{display:block;height:100%}#jumpPanel .jb.l{background:var(--accent)}'
             '#jumpPanel .jb.j{background:var(--heur)}#jumpPanel .jb.r{background:var(--computed)}'
             '#jumpPanel .jlog{font-family:var(--mono);font-size:.78rem;max-height:300px;overflow:auto;'
             'border-top:1px solid var(--line);margin-top:12px;padding-top:8px;overflow-wrap:anywhere}'
             '#jumpPanel .jstate{font-family:var(--mono);font-size:.85rem;overflow-wrap:anywhere}'
             '#jumpPanel .jcount{font-size:.85rem;color:var(--fg2);margin-top:6px}</style>')
    jumps = {
        'id': 'jumps', 'eyebrow': 'Macro structure', 'heading': 'Whole sweeps as one jump',
        'html': [
            '<p>Almost every frame of the map repeats one of a few cases, and the repeats add up in closed form, proved '
            'for all sizes in <code>lean/Jump.lean</code>:</p>',
            '<pre>w(l, j + 2k, r + 1)      k frames, 6k steps              w(l + 4k, j, r + 1)     w_sweep (also W)\n'
            'u(l, j + k, r)           k frames, 4k steps              u(l, j, r + 2k)         u_sweep (also U)\n'
            'y(a + 3k, j, r + 1 + k)  2k frames, k(4j+9) + 4k(k-1)    y(a, j + 2k, r + 1)     y_zigzag (also Y)</pre>',
            '<p>A <b>jump</b> takes a whole sweep or zigzag at once and is one case of the map otherwise '
            '(<code>jump</code>, <code>jump_sound</code>). The run from blank tape is then about 10<sup>8</sup> jumps '
            'per 1.5&middot;10<sup>14</sup> frames, and the shape of the run becomes visible. Write the tape as a '
            'solid block <code>1^l</code> (blue below), an alternating block <code>(10)^j</code> (purple) and a solid '
            'block <code>1^r</code> (amber). An <b>epoch</b> has two phases:</p>',
            '<ul><li><b>Growth.</b> A zigzag turns the left block into alternating cells (each round eats 3 of the '
            'left block and 1 of the right block), and a <code>w</code> sweep turns them back into a left block 4/3 '
            'as long. The left block grows by 4/3 a pass and the right block pays a third of it, until the right '
            'block runs out in the middle of a zigzag.</li>'
            '<li><b>Drain.</b> A <code>u</code> sweep moves the alternating block into the right block, and the '
            'zigzags now stop when the right block runs out, each pass multiplying it by about 4 and eating three '
            'times as much of the left block, until the left block is gone and a new epoch starts.</li></ul>',
            '<p>Inside a phase the ratios are fixed. What is chaotic is where the phases end: the remainders at the '
            'crossovers. The tape grows by a few cells a pass, so the sizes grow about linearly in the number of '
            'jumps and the step count like its cube.</p>',
            style,
            '<div class="panel" id="jumpPanel"><div class="controls">'
            '<button type="button" class="j1 primary">1 jump</button> <button type="button" class="j10">10</button> '
            '<button type="button" class="j1k">1,000</button> <button type="button" class="j100k">100,000</button> '
            '<button type="button" class="jreset">Reset</button></div>'
            '<div class="jstate"></div><div class="jbars"></div><div class="jcount"></div><div class="jlog"></div>'
            '<div class="cap"><span class="ev k">Kernel</span> The jumps are theorems of <code>lean/Jump.lean</code>; '
            'the panel computes them with BigInt from the 78 Lean cases and agrees with <code>c/frun.c</code> on the '
            'first 200,000 jumps (<code>py/jumps_panel_test.js</code>).</div></div>',
            '<script>' + cases + '\n' + panel + '</script>',
        ]}
    closes = {
        'id': 'close', 'eyebrow': 'Halting', 'heading': 'The halting rows and the close calls',
        'html': [
            '<p>A zigzag stops when the left block is below 3 or the right block is down to 1. When both run out '
            'together, three more frames and a sweep decide, and five rows end in a frame where the map is undefined '
            '(<code>halt_y</code>, <code>halt_Y</code>, <code>halt_y0</code>, <code>halt_y2</code>, '
            '<code>halt_Y0</code> in <code>lean/Jump.lean</code>):</p>',
            '<div style="overflow-x:auto"><table class="tbl"><thead><tr><th>zigzag start</th><th>then</th></tr></thead><tbody>'
            '<tr><td><code>y(3k+1, 2m, k+2)</code></td><td>k rounds to <code>y(1, ., 2)</code>, <code>z(0, ., 1)</code>, '
            '<code>w(0, even, 1)</code>, a sweep to <code>w(., 0, 1)</code>: halt</td></tr>'
            '<tr><td><code>Y(3k+1, 2m, k+3)</code></td><td>k rounds to <code>Y(1, ., 3)</code>, <code>z(2, ., 2)</code>, '
            '<code>y(0, odd, 2)</code>, <code>z(0, ., 1)</code>, <code>w(0, even, 1)</code>, a sweep: halt</td></tr>'
            '<tr><td><code>y(3k, 2m+1, k+2)</code>, <code>y(3k+2, 2m+1, k+2)</code>, <code>Y(3k, 2m+1, k+2)</code></td>'
            '<td>the same with an odd alternating block</td></tr></tbody></table></div>',
            '<p>From every frame with all three numbers below 60, every halt within 400 jumps comes before the first '
            'zigzag or right after a zigzag start in one of these rows (<code>frun rows 60</code>; not proved for all '
            'frames). In the run from blank tape every zigzag start so far has an even alternating block, so only the '
            'first two rows can be met: the machine halts if a crossover lands on <code>y(a, 2m, R)</code> with '
            '<code>a = 3R &minus; 5</code> or <code>Y(a, 2m, R)</code> with <code>a = 3R &minus; 8</code>. Call '
            '<code>d</code> the distance to the row (<code>d = R &minus; &lfloor;a/3&rfloor; &minus; 2</code>, or '
            '&minus;3 for Y, at starts with <code>a &equiv; 1 mod 3</code>).</p>',
            f'<p>The jump map in C (<code>c/frun.c</code>) ran {sci(J)} jumps, {sci(F)} frames, '
            f'<b>{sci(S)} machine steps</b>, without a halt (the earlier accelerated run stopped at '
            '3.58&middot;10<sup>22</sup>). Every zigzag start within 16 of a halting row (blue: y, purple: Y; hover for '
            'the frame):</p>',
            svg_close(close, J),
            '<div style="overflow-x:auto"><table class="tbl"><thead><tr><th>jump</th><th>zigzag start</th><th>d</th>'
            '</tr></thead><tbody>' + rows + '</tbody></table></div>',
            f'<p><b>Heuristic.</b> At a crossover the ratio of the blocks lands anywhere in a range of fixed relative '
            'width, so the chance of <code>d = 0</code> is about c/R per epoch; R is about a tenth of the jump number '
            'J and an epoch is about log J jumps, so the expected number of hits up to J grows like ln ln J: without '
            f'bound, but very slowly. The close calls above give about {lam:.1f} expected hits per unit of ln ln J '
            f'({nev} starts with |d| &le; 16 since jump 1,000), so about {exp_seen:.1f} were expected so far and none '
            f'came. If this is right the machine halts with probability 1, with a median around '
            f'ln ln J &asymp; {med:.1f}, J &asymp; 10<sup>{math.exp(med) / math.log(10):.0f}</sup> jumps and about '
            f'10<sup>{3 * math.exp(med) / math.log(10):.0f}</sup> steps. The calls closest to <code>d = 0</code> '
            'are fewer than the rate predicts, which may be chance or a structure not found yet.</p>',
        ]}
    return jumps, closes, (J, F, S, lam, exp_seen, med)


if __name__ == '__main__':
    jumps, closes, nums = build()
    p = os.path.join(ROOT, 'status.json')
    st = json.load(open(p))
    secs = [s for s in st['explainer']['sections'] if s['id'] not in ('jumps', 'close')]
    i = next(k for k, s in enumerate(secs) if s['id'] == 'rules') + 1
    secs[i:i] = [jumps, closes]
    st['explainer']['sections'] = secs
    json.dump(st, open(p, 'w'), indent=1, ensure_ascii=False)
    open(p, 'a').write('\n')
    print('jumps %d frames %d steps %d; heuristic rate %.2f, expected so far %.2f, median lnlnJ %.2f' % nums)
