"""Write pages/holdouts/number-theory.html from ranking.json (and the CSS of the Doucette page).

usage: python3 tools/number-theory/build_page.py
"""
import html
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
OUT = os.path.join(REPO, "pages", "holdouts", "number-theory.html")

TIERS = [("A", "a route with no number theory may exist"),
         ("B", "a simple invariant (parity, residue) is plausible"),
         ("C", "Collatz-type; a Lean step that sharpens the question is open or just done"),
         ("D", "Collatz-type; known methods shown not to work"),
         ("E", "Antihydra type, or not fully reduced"),
         ("F", "probably halts, out of reach of computation")]

EXTRA_CSS = """
.chips { display: flex; flex-wrap: wrap; gap: 6px; }
.chip { font-family: var(--font-display); font-size: 0.72rem; border: 1px solid var(--rule); background: var(--surface);
  color: var(--ink); border-radius: 999px; padding: 3px 10px; cursor: pointer; }
.chip[aria-pressed="true"] { background: var(--link); border-color: var(--link); color: var(--surface); }
.tier { font-family: var(--font-display); font-weight: 700; font-size: 0.75rem; border-radius: 4px; padding: 0 6px; }
.tA { color: var(--kernel); background: var(--kernel-bg); } .tB { color: var(--comp); background: var(--comp-bg); }
.tC { color: var(--heur); background: var(--heur-bg); } .tD { color: var(--native); background: var(--native-bg); }
.tE, .tF { color: var(--open); background: var(--open-bg); }
.rk td { vertical-align: top; } .rk .why { min-width: 26ch; }
input[type=search], input[type=number] { font: inherit; padding: 4px 8px; border: 1px solid var(--rule); border-radius: var(--r);
  background: var(--surface); color: var(--ink); }
button.b { font: inherit; font-size: 0.85rem; padding: 4px 12px; border: 1px solid var(--rule); border-radius: var(--r);
  background: var(--surface); color: var(--ink); cursor: pointer; }
button.b:hover { border-color: var(--link); }
.stack { display: flex; flex-wrap: wrap; align-items: flex-end; gap: 6px; min-height: 64px; }
.item { font-family: var(--font-display); font-size: 0.72rem; border: 2px solid var(--c1); border-radius: 4px; padding: 2px 6px;
  background: var(--surface); }
.item.closed { border-color: var(--c4); border-style: dashed; }
.item.wall { border-color: var(--muted); }
.log { font-family: var(--font-display); font-size: 0.72rem; max-height: 180px; overflow: auto; white-space: pre; }
"""


def build():
    rank = json.load(open(os.path.join(HERE, "ranking.json")))
    css = re.search(r"<style>(.*?)</style>",
                    open(os.path.join(REPO, "pages", "holdouts", "doucette-family.html")).read(), re.S).group(1)
    data = json.dumps([{k: x[k] for k in ("rank", "m", "cls", "tier", "why", "next")} for x in rank])
    legend = "".join(f'<li><span class="tier t{t}">{t}</span> {html.escape(d)} '
                     f'({sum(1 for x in rank if x["tier"] == t)})</li>' for t, d in TIERS)
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Solvable Collatz-like holdouts?</title>
<meta name="description" content="The 40 BB(6) holdouts whose halting Lean reduces to a question about a map, ranked by how likely a proof is, with the best candidate's free-parity wall search and the three machines that iterate one function.">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Atkinson+Hyperlegible:ital,wght@0,400;0,700;1,400&family=Martian+Mono:wght@400;500;700&display=swap">
<style>{css}{EXTRA_CSS}</style>
</head>
<body>
<main class="wrap">
<header class="top">
  <p class="crumb"><a href="../index.html">Busy Beaver Explorer</a> / <a href="index.html">holdouts</a> / number theory</p>
  <p class="eyebrow">40 machines, ranked</p>
  <h1>Which Collatz-like holdouts could be solved?</h1>
  <p>For each of these 40 machines Lean already proves "the machine halts if and only if this map does something".
  What is left is a question about the map: will an orbit ever land on a sparse set, or a counter ever hit zero?
  This page ranks the 40 by how likely a proof is and shows what was tried. The ranking is a judgement, not a result.
  For the 39 below the top one, the <a href="open-problems.html">open-problems page</a> writes out the exact question each
  reduces to and the known problem it resembles.</p>
</header>

<section class="verdict">
  <p><b>None is decided.</b> One machine stands out, and two smaller results are new:</p>
  <ul>
    <li><span class="tag t-comp">computed</span> <b>1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC</b> is the best candidate.
    Its wall changes only through the parity of N, so a closed set of walls would prove non-halting with no number theory.
    Under every parity sequence, the stack of counters never goes negative (29,195 walls to 30,000 cells). What is left is a
    2-adic coincidence that the reachable walls get at most 10% of the way towards.</li>
    <li><span class="tag t-kernel">kernel</span> Three machines iterate one function, f(n) = 3n &minus; 10&middot;2<sup>k</sup> + 3k + 14.
    Lean now proves the closed form for every n in all three (<code>lean/Closed.lean</code>).</li>
    <li><span class="tag t-comp">computed</span> The subtract-and-multiply maps have no residue invariant modulo any 2<sup>a</sup>3<sup>b</sup> up to 7,776.</li>
  </ul>
</section>

<section>
  <h2>The ranking</h2>
  <ul class="prose">{legend}</ul>
  <div class="controls">
    <div class="chips" id="tierchips"></div>
    <input type="search" id="q" placeholder="filter: machine, class, word" aria-label="filter the table">
  </div>
  <div class="scroll"><table class="tbl rk"><thead><tr><th>#</th><th>tier</th><th>machine</th><th>class</th>
  <th class="why">why</th><th>next step</th></tr></thead><tbody id="rows"></tbody></table></div>
</section>

<section>
  <h2>The best candidate: a stack of counters under free parities</h2>
  <div class="prose">
  <p>For 1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC, each step starts at <code>W A&gt; 0 b<sup>N</sup> 1</code> (b = 110),
  and the next wall W&prime; depends only on W and N mod 2. Every wall seen is <code>1</code> followed by counters:
  open <code>K(k) = b<sup>k</sup> 1<sup>3</sup> b 1</code> or closed <code>K&prime;(k) = b<sup>k</sup> 1<sup>6</sup></code>.
  A step sends the parity into the top counter. An open counter closes on an even parity and grows by about 3/2 on an odd one.
  When it grows, it passes its own parity down and pays for the counter below. Choose the parities yourself below and try to
  drive a count below zero. That would need the counter above to stay odd for about as many steps as its own value.</p>
  </div>
  <div class="panel">
    <div class="controls">
      <button class="b" id="ev">N even</button><button class="b" id="od">N odd</button>
      <button class="b" id="rn">10 random</button><button class="b" id="ao">odd until the top is even</button>
      <button class="b" id="rs">reset</button>
    </div>
    <div class="stack" id="stk"></div>
    <p class="small" id="stat"></p>
    <div class="log" id="log"></div>
  </div>
</section>

<section>
  <h2>Three machines, one function</h2>
  <div class="prose">
  <p>With h<sub>k</sub> = 5&middot;2<sup>k</sup> &minus; k &minus; 6 (3, 12, 31, 70, 149, &hellip;), set
  f(n) = 3n &minus; 10&middot;2<sup>k</sup> + 3k + 14 for h<sub>k</sub> &lt; n &lt; h<sub>k+1</sub>, and let f halt at n = h<sub>k</sub>.
  Then 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE is the orbit of 4, 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE the orbit of 10
  (in its coordinate N = 2n + 2), and 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE the orbit of 1. Each machine halts if and only if its orbit lands on some h<sub>k</sub>.
  The three orbits share no value in their first 20,000 terms.</p>
  </div>
  <div class="panel">
    <div class="controls"><label>start <input type="number" id="f0" value="4" min="1"></label>
    <button class="b" id="fgo">iterate 40</button></div>
    <div class="scroll"><table class="tbl"><thead><tr><th>i</th><th>n</th><th>level k</th><th>distance to the next h</th></tr></thead>
    <tbody id="frows"></tbody></table></div>
  </div>
</section>

<section class="prose">
  <h2>Sources</h2>
  <p>Ranking, scripts and notes: <a href="https://github.com/fractal-geometry-explorer/busy-beaver-explorer/tree/main/tools/number-theory">tools/number-theory</a>
  (<code>ranking.json</code>, <code>wallstack.py</code>, <code>samemap.py</code>, <code>residues.py</code>). Generated by <code>tools/number-theory/build_page.py</code>.</p>
</section>
</main>
<script>
const R = {data};
const TIERS = {json.dumps([t for t, _ in TIERS])};
let on = new Set(TIERS);
const chips = document.getElementById('tierchips');
for (const t of TIERS) {{
  const b = document.createElement('button'); b.className = 'chip'; b.textContent = 'tier ' + t;
  b.setAttribute('aria-pressed', 'true');
  b.onclick = () => {{ if (on.has(t)) on.delete(t); else on.add(t); b.setAttribute('aria-pressed', on.has(t)); draw(); }};
  chips.appendChild(b);
}}
const esc = s => s.replace(/[&<>]/g, c => ({{'&': '&amp;', '<': '&lt;', '>': '&gt;'}}[c]));
function draw() {{
  const q = document.getElementById('q').value.toLowerCase();
  document.getElementById('rows').innerHTML = R.filter(x => on.has(x.tier) &&
      (x.m + ' ' + x.cls + ' ' + x.why + ' ' + x.next).toLowerCase().includes(q)).map(x =>
    `<tr><td>${{x.rank}}</td><td><span class="tier t${{x.tier}}">${{x.tier}}</span></td>` +
    `<td><a href="${{x.m}}/explainer.html"><code>${{x.m}}</code></a></td><td>${{esc(x.cls)}}</td>` +
    `<td>${{esc(x.why)}}</td><td>${{esc(x.next)}}</td></tr>`).join('');
}}
document.getElementById('q').oninput = draw; draw();

// the stack model of holdouts/1RB1LF_1LC1RD_1RA1LA_0RA0RE_0RC---_1RF0LC/py/stackmodel.py, with BigInt counts
function step(lv, s) {{
  if (lv.length === 0) return s === 0 ? [[], 2n, 2n] : [[[0n, false]], 0n, 0n];
  const [k, pr] = lv[lv.length - 1], V = lv.slice(0, -1);
  if (!pr) {{
    if (s === 0) return [V.concat([[k, true]]), 2n, 2n];
    const r = step(V, Number(k % 2n)); if (r === null) return null;
    const k2 = 3n * k / 2n + r[1]; if (k2 < 0n) return null;
    const o = -(k2 - k) + r[2]; return [r[0].concat([[k2, false]]), o, o];
  }}
  if (k === 0n && s === 1) return [V.concat([[0n, true], [0n, false]]), 0n, 0n];
  const r = step(V, Number((k + BigInt(s)) % 2n)); if (r === null) return null;
  const c = 2n + BigInt(s) * (1n + k % 2n);
  return [r[0], r[1] + 3n * k / 2n + c, r[2] + k + 2n];
}}
let lv = [], n = 0, dead = false, lines = [];
function show() {{
  const el = document.getElementById('stk');
  el.innerHTML = '<span class="item wall">1</span>' + lv.map(([k, pr]) =>
    `<span class="item ${{pr ? 'closed' : ''}}">${{pr ? "K'" : 'K'}}(${{k}})</span>`).join('');
  let ratio = null;
  for (let i = 0; i + 1 < lv.length; i++) if (lv[i][0] > 0n) {{
    const q = Number(lv[i + 1][0]) / Number(lv[i][0]); if (ratio === null || q < ratio) ratio = q; }}
  document.getElementById('stat').textContent = dead ? 'A count would go below zero: the model stops here (never seen from the wall 1).' :
    `${{n}} steps, ${{lv.length}} counters` + (ratio === null ? '' : `, smallest counter/lower ratio ${{ratio.toFixed(2)}}`);
  document.getElementById('log').textContent = lines.slice(-200).join('\\n');
}}
function go(s) {{
  if (dead) return; const r = step(lv, s);
  if (r === null) {{ dead = true; show(); return; }}
  lv = r[0]; n++; lines.push(`${{n}}: N ${{s ? 'odd ' : 'even'}} -> ` + (lv.map(([k, p]) => (p ? "K'" : 'K') + k).join(' ') || '1'));
}}
document.getElementById('ev').onclick = () => {{ go(0); show(); }};
document.getElementById('od').onclick = () => {{ go(1); show(); }};
document.getElementById('rn').onclick = () => {{ for (let i = 0; i < 10; i++) go(Math.random() < 0.5 ? 0 : 1); show(); }};
document.getElementById('ao').onclick = () => {{ let g = 0;
  do {{ go(1); g++; }} while (!dead && g < 200 && lv.length && !lv[lv.length - 1][1] && lv[lv.length - 1][0] % 2n === 1n); show(); }};
document.getElementById('rs').onclick = () => {{ lv = []; n = 0; dead = false; lines = []; show(); }};
show();

// the shared function f
const h = k => 5n * (1n << BigInt(k)) - BigInt(k) - 6n;
function level(x) {{ let k = 0; while (h(k + 1) <= x) k++; return k; }}
document.getElementById('fgo').onclick = () => {{
  let x = BigInt(Math.max(1, parseInt(document.getElementById('f0').value) || 1)), out = [];
  for (let i = 0; i < 40; i++) {{
    const k = level(x);
    if (x === h(k) && k >= 1) {{ out.push(`<tr><td>${{i}}</td><td>${{x}}</td><td>${{k}}</td><td>halts: n = h<sub>${{k}}</sub></td></tr>`); break; }}
    out.push(`<tr><td>${{i}}</td><td>${{x}}</td><td>${{k}}</td><td>${{h(k + 1) - x}}</td></tr>`);
    x = 3n * x - 10n * (1n << BigInt(k)) + 3n * BigInt(k) + 14n;
  }}
  document.getElementById('frows').innerHTML = out.join('');
}};
document.getElementById('fgo').click();
</script>
</body>
</html>
"""


if __name__ == "__main__":
    with open(OUT, "w") as f:
        f.write(build())
    print("wrote", OUT)
