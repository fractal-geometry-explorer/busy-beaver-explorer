"""SVG chart from `lturn` output (lines `k t L=.. lo=.. hi=..`): the right end and the cell where each leftward
sweep turns, against the sweep number.  usage: python3 py/chart37.py lturn.txt [every] > chart.svg"""
import sys, re
rows = []
for line in open(sys.argv[1]):
    m = re.match(r'(\d+) (\d+) L=(-?\d+) lo=(-?\d+) hi=(-?\d+)\s*$', line)
    if m:
        rows.append(tuple(int(x) for x in m.groups()))
ev = int(sys.argv[2]) if len(sys.argv) > 2 else 1
rows = rows[::ev]
K = max(r[0] for r in rows); Hm = max(r[4] for r in rows); Lm = min(min(r[2], r[3]) for r in rows)
step = 100000
lo_t = (Lm // step) * step
W, H, ml, mb = 560, 260, 56, 30
X = lambda k: ml + (W - ml - 10) * k / K
Y = lambda v: H - mb - (H - mb - 24) * (v - lo_t) / (Hm - lo_t)
o = [f'<svg viewBox="0 0 {W} {H}" role="img" aria-label="turning point and right end against sweep number" '
     f'style="width:100%;max-width:{W}px;height:auto;font:11px var(--mono);">']
v = lo_t
while v <= Hm:
    o.append(f'<line x1="{ml}" x2="{W-10}" y1="{Y(v):.1f}" y2="{Y(v):.1f}" stroke="var(--line)"/>'
             f'<text x="{ml-4}" y="{Y(v)+4:.1f}" text-anchor="end" fill="var(--muted)">{v//1000}k</text>')
    v += step
for i in range(0, 5):
    k = K * i / 4
    o.append(f'<text x="{X(k):.1f}" y="{H-mb+16}" text-anchor="middle" fill="var(--muted)">{int(k/1000)}k</text>')
kb = 49300
o.append(f'<line x1="{X(kb):.1f}" x2="{X(kb):.1f}" y1="24" y2="{H-mb}" stroke="var(--muted)" stroke-dasharray="3 3"/>'
         f'<text x="{X(kb)+4:.1f}" y="{H-mb-6}" fill="var(--muted)">bouncer from here</text>')
def path(idx, col):
    pts = ' L'.join(f'{X(r[0]):.1f},{Y(r[idx]):.1f}' for r in rows)
    return f'<path d="M{pts}" fill="none" stroke="{col}" stroke-width="1.5"/>'
o.append(path(4, 'var(--head)')); o.append(path(2, 'var(--accent)'))
o.append(f'<text x="{W-10}" y="14" text-anchor="end" fill="var(--fg2)"><tspan fill="var(--head)">&#9632; right end</tspan>'
         f'  <tspan fill="var(--accent)">&#9632; where the leftward sweep turns</tspan>  (sweeps across)</text>')
o.append('</svg>')
print(''.join(o))
