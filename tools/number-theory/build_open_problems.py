"""Write pages/holdouts/open-problems.html from open_problems.json (and the CSS of the Doucette page).

For each of the 39 Collatz-hard machines of ranking.json (ranks 2 to 40): the map Lean reduces it to, the halting
condition, the Lean theorem, a heuristic for halting, related known problems, and a runner for the simpler maps.

usage: python3 tools/number-theory/build_open_problems.py
"""
import html
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
OUT = os.path.join(REPO, "pages", "holdouts", "open-problems.html")

LEVELS = {"iff": ("kernel", "t-kernel", "halts iff the map's condition"),
          "oneway": ("one way", "t-native", "the map's condition never met implies no halt"),
          "partial": ("partial", "t-open", "pieces proved, the map not yet")}

EXTRA_CSS = """
.chips { display: flex; flex-wrap: wrap; gap: 6px; }
.chip { font-family: var(--font-display); font-size: 0.72rem; border: 1px solid var(--rule); background: var(--surface);
  color: var(--ink); border-radius: 999px; padding: 3px 10px; cursor: pointer; }
.chip[aria-pressed="true"] { background: var(--link); border-color: var(--link); color: var(--surface); }
input[type=search], input[type=text], select { font: inherit; padding: 4px 8px; border: 1px solid var(--rule);
  border-radius: var(--r); background: var(--surface); color: var(--ink); max-width: 100%; }
button.b { font: inherit; font-size: 0.85rem; padding: 4px 12px; border: 1px solid var(--rule); border-radius: var(--r);
  background: var(--surface); color: var(--ink); cursor: pointer; }
button.b:hover { border-color: var(--link); }
.fam { background: var(--surface); border: 1px solid var(--rule); border-radius: var(--r); padding: 14px 16px;
  display: grid; gap: 8px; }
.fam .q { font-weight: 700; }
.fam .n { font-family: var(--font-display); font-size: 0.72rem; color: var(--muted); }
.mc { background: var(--surface); border: 1px solid var(--rule); border-radius: var(--r); }
.mc summary { cursor: pointer; padding: 10px 14px; display: flex; flex-wrap: wrap; gap: 8px; align-items: baseline; }
.mc summary code { font-size: 0.78rem; }
.mc .body { padding: 0 14px 14px; display: grid; gap: 8px; }
.mc dl { display: grid; grid-template-columns: minmax(7em, max-content) 1fr; gap: 6px 12px; margin: 0; }
.mc dt { font-family: var(--font-display); font-size: 0.72rem; color: var(--muted); padding-top: 3px; }
.mc dd { margin: 0; overflow-wrap: anywhere; }
@media (max-width: 560px) { .mc dl { grid-template-columns: 1fr; } .mc dt { padding-top: 6px; } }
.rk { font-family: var(--font-display); font-size: 0.72rem; color: var(--muted); }
.list { display: grid; gap: 8px; }
.out { font-family: var(--font-display); font-size: 0.72rem; }
.out td { white-space: nowrap; }
.hit { color: var(--open); font-weight: 700; }
section > *, .panel > * { min-width: 0; }
#rsel { width: 100%; }
"""

RUNNER_JS = r"""
// Each runner: init(text) -> state; step(state) -> {s: next state, row: [cells], stop: message or null}
const B = BigInt;
const big = x => { const s = x.toString(); return s.length > 36 ? s.slice(0, 12) + '…' + s.slice(-8) + ' (' + s.length + ' digits)' : s; };
const nums = t => t.split(',').map(x => x.trim());
function v2(D) { let v = 0n; while (D > 0n && D % 2n === 0n) { D /= 2n; v++; } return [v, D]; }
const isPow2 = D => D > 0n && (D & (D - 1n)) === 0n;
const hk = k => 5n * (1n << B(k)) - B(k) - 6n;
const RUN = {
  f: { cols: ['n', 'level k', 'distance to h(k+1)'], init: t => B(nums(t)[0]),
    step(n) { let k = 0; while (hk(k + 1) <= n) k++;
      if (k >= 1 && n === hk(k)) return { row: [big(n), k, '0'], stop: 'n = h(' + k + '): the machine halts' };
      const n2 = 3n * n - 10n * (1n << B(k)) + 3n * B(k) + 14n; return { s: n2, row: [big(n), k, big(hk(k + 1) - n)] }; } },
  F14: { cols: ['t', 'parity', 'next'], init: t => B(nums(t)[0]),
    step(t) {
      const small = { 0: 19n, 1: 19n, 2: 6n, 4: 7n, 5: 20n };
      if (t === 3n) return { row: ['3', 'odd', ''], stop: 'Z(3) halts' };
      if (t < 6n) return { s: small[Number(t)], row: [big(t), t % 2n ? 'odd' : 'even', big(small[Number(t)])] };
      if (t % 2n === 0n) { const n = t % 4n === 0n ? 3n * t / 2n + 1n : 3n * t / 2n + 3n; return { s: n, row: [big(t), 'even', big(n)] }; }
      let a = 1n, d = (t + 3n) / 2n;
      for (;;) {
        if (d === 0n) return { row: [big(t), 'odd', ''], stop: 't = 2^(j+1) − 2j − 7: the machine halts' };
        if (d < a) { const x = a - 1n - d, y = 2n * d + 2n; const n = x % 2n === 0n ? 2n * y + 1n + 3n * x : 2n * y + 3n + 3n * x;
          return { s: n, row: [big(t), 'odd', big(n)] }; }
        if (d === a) { const n = 4n * a + 4n; return { s: n, row: [big(t), 'odd', big(n)] }; }
        if (d === a + 1n) { d = 2n * a + 3n; a = 1n; continue; }
        const a0 = a; a = 2n * a + 3n; d = d - a0 - 2n;
      } } },
  odo: { cols: ['reset', 'operations', 'v', '2u − v', '(2u − v)/v'], init: t => { const [c, u, v] = nums(t).map(B); return { c, u, v, ops: 0, r: 0 }; },
    step(S) { let { c, u, v, ops, r } = S;
      for (let i = 0; i < 2000000; i++) { ops++;
        if (2n * u < v) { u = 2n * u; v = v + 1n; continue; }
        if (c >= 1n) { if (2n * u === v) { u = 1n; v = v + 2n; } else { u = 2n * u - v; v = v + 1n; } c--; continue; }
        if (2n * u === v) return { row: [r + 1, ops, big(v), '0', '0'], stop: 'a reset with 2u = v: the machine halts' };
        const w = 2n * u - v; const row = [r + 1, ops, big(v), big(w), (Number(w) / Number(v)).toFixed(4)];
        c = 2n * (v - u - 1n); u = w; v = u + 3n; return { s: { c, u, v, ops, r: r + 1 }, row }; }
      return { s: { c, u, v, ops, r }, row: ['—', ops, big(v), '', ''] }; } },
  r18: { cols: ['a', 'c', 'c − a'], init: t => nums(t).map(B),
    step([a, c]) { const d = c - a, row = [big(a), big(c), big(d)];
      if (c % 2n === 0n) { if (d === 10n || d === 12n) return { row, stop: 'c − a = ' + d + ': the machine halts' };
        return { s: d <= 8n ? [a - c + 12n, 3n * c - 6n] : [c - a - 10n, 3n * a + 27n], row }; }
      if (d === -1n || d === -3n) return { row, stop: 'a − c = ' + (-d) + ': the machine halts' };
      return { s: c <= a - 5n ? [a - c - 1n, 3n * c + 6n] : [c - a + 3n, 3n * a], row }; } },
  r19: { cols: ['p', 'r', 'r − p − 1'], init: t => nums(t).map(B),
    step([p, r]) { const row = [big(p), big(r), big(r - p - 1n)];
      if (r === p + 1n) return { row, stop: 'r = p + 1: the machine halts' };
      if (r >= p + 2n) return { s: [2n * p + 2n, r - p - 1n], row };
      if (r === p) return { s: [2n, 4n * p + 1n], row };
      return { s: [p - r, 4n * r + 2n], row }; } },
  r20: { cols: ['shape', 'u', 'v', 'u − v'], init: t => { const x = nums(t); return [x[0], B(x[1]), B(x[2])]; },
    step([k, u, v]) { const row = [k, big(u), big(v), big(u - v)];
      if (u === v || u === v + 1n) return { row, stop: 'u = v or u = v + 1: the machine halts' };
      if (u < v) return { s: [k, 3n * u + (k === 'P' ? 2n : 3n), v - u - 1n], row };
      return { s: [k === 'P' ? 'Q' : 'P', 3n * v + (k === 'P' ? 3n : 5n), u - v - 2n], row }; } },
  r21: { cols: ['i', 'j', 'J', 'i − j'], init: t => nums(t).map(B),
    step([i, j, J]) { const row = [big(i), big(j), J, big(i - j)];
      if (i === j || i + 1n === j) return { row, stop: 'i = j or i + 1 = j: the machine halts' };
      if (i >= j + 2n) return { s: [i - j - 1n, 3n * j + 2n + J, J], row };
      if (i === j + 1n) return { s: J ? [3n * i, 1n, 0n] : [3n * i - 3n, 3n, 1n], row };
      if (i + 2n === j) return { s: J ? [3n * i + 3n, 3n, 1n] : [3n * i + 3n, 1n, 0n], row };
      return { s: [j - i - 2n, 3n * i + 3n + 2n * J, 1n - J], row }; } },
  douc: { cols: ['D', 'v', 'a'], init: t => { const x = nums(t); return [B(x[0]), B(x[1]), x[2] || '']; },
    step([D, c, mode]) { const [v, o] = v2(D), a = (o - 1n) / 2n, row = [big(D), v.toString(), big(a)];
      if (isPow2(D)) return { row, stop: 'D is a power of two: the machine halts' };
      if (a === 1n && (mode !== 'even' || (v > 0n && v % 2n === 0n)))
        return { row, stop: 'D = 3·2^v: a special rule applies here (not modelled; never seen in the first 20,000 terms)' };
      return { s: [D + a + v + c, c, mode], row }; } },
  sn: { cols: ['D', 'v', 'a'], init: t => B(nums(t)[0]),
    step(D) { const [v, o] = v2(D), a = (o - 1n) / 2n, row = [big(D), v.toString(), big(a)];
      if (isPow2(D)) return { row, stop: 'D is a power of two: the machine halts' };
      return { s: D + v + 3n * a, row }; } },
  w28: { cols: ['n', 'counter m'], init: t => nums(t).map(B),
    step([n, m]) { const row = [big(n), m.toString()];
      if (n % 2n === 1n && m === -1n) return { row, stop: 'odd n with m = −1: the machine halts' };
      return { s: n % 2n === 0n ? [3n * n / 2n + 2n, m + 2n] : [(3n * n + 7n) / 2n, m - 1n], row }; } },
  w29: { cols: ['m', 'm mod 3', 'counter k'], init: t => nums(t).map(B),
    step([m, k]) { const r = m % 3n, t = m / 3n, row = [big(m), r.toString(), k.toString()];
      if (r === 2n && k === 0n) return { row, stop: 'm ≡ 2 (mod 3) with k = 0: the machine halts' };
      if (r === 0n) return { s: [4n * t + 4n, k > 0n ? k - 1n : 0n], row };
      return { s: [4n * t + (r === 1n ? 4n : 5n), k + 1n], row }; } },
  w30: { cols: ['z', 'z mod 3', 'counter y'], init: t => nums(t).map(B),
    step([z, y]) { const r = z % 3n, k = z / 3n, row = [big(z), r.toString(), y.toString()];
      if (y === 0n && r !== 0n) return { row, stop: 'y = 0 with 3 ∤ z: the orbit leaves the rules (the machine may halt here)' };
      return { s: r === 0n ? [4n * k + 1n, y + 4n] : r === 1n ? [4n * k + 5n, y + 6n] : [4n * k + 8n, y - 1n], row }; } },
  w31: { cols: ['x', 'parity', 'counter p'], init: t => { const [p, x] = nums(t).map(B); return [x, p]; },
    step([x, p]) { const row = [big(x), x % 2n ? 'odd' : 'even', p.toString()];
      if (x % 2n === 1n && p === 0n) return { row, stop: 'the counter would go below 0: the machine halts' };
      return { s: [3n * x / 2n, x % 2n ? p - 1n : p + 2n], row }; } },
};
"""


def esc(s):
    return html.escape(s, quote=True)


def build():
    D = json.load(open(os.path.join(HERE, "open_problems.json")))
    rank = {x["m"]: x for x in json.load(open(os.path.join(HERE, "ranking.json")))}
    fams = {f["key"]: f for f in D["families"]}
    rel = D["related"]
    ms = D["machines"]
    css = re.search(r"<style>(.*?)</style>",
                    open(os.path.join(REPO, "pages", "holdouts", "doucette-family.html")).read(), re.S).group(1)
    nlev = {k: sum(1 for x in ms if x["leanLevel"] == k) for k in LEVELS}

    famhtml = []
    for f in D["families"]:
        mem = [x for x in ms if x["family"] == f["key"]]
        rl = ", ".join(f'<a href="#rel-{r}">{esc(rel[r]["name"].split(" (")[0])}</a>' for r in f["related"])
        famhtml.append(f"""<div class="fam" id="fam-{f['key']}">
  <h3>{esc(f['name'])}</h3>
  <p class="n">{len(mem)} machine{'s' if len(mem) != 1 else ''}: ranks {', '.join(str(x['rank']) for x in mem)}</p>
  <p class="q">{esc(f['question'])}</p>
  <p><b>Heuristic.</b> {esc(f['heuristic'])}</p>
  <p class="small">Related: {rl}</p>
</div>""")

    cards = []
    for x in ms:
        lv, cl, _ = LEVELS[x["leanLevel"]]
        f = fams[x["family"]]
        run = ""
        if x.get("runner"):
            run = (f'<p><button class="b" data-run="{x["runner"]}" data-start="{esc(x["runnerStart"])}" '
                   f'data-m="{x["m"]}">run this map</button></p>')
        rk = rank.get(x["m"], {})
        cards.append(f"""<details class="mc" data-fam="{x['family']}" data-text="{esc((x['m'] + ' ' + x['map'] + ' ' + x['halt'] + ' ' + f['name']).lower())}" id="m-{x['rank']}">
<summary><span class="rk">#{x['rank']}</span> <code>{x['m']}</code> <span class="tag {cl}">{lv}</span>
<span class="small">{esc(f['name'])}</span></summary>
<div class="body"><dl>
<dt>tape</dt><dd>{esc(x['state'])}</dd>
<dt>map</dt><dd>{esc(x['map'])}</dd>
<dt>halts iff</dt><dd>{esc(x['halt'])}</dd>
<dt>start</dt><dd>{esc(x['start'])}</dd>
<dt>Lean</dt><dd><code>{esc(x['lean'])}</code></dd>
<dt>heuristic</dt><dd>{esc(x['heuristic'])}</dd>
<dt>checked</dt><dd>{esc(x['evidence'])}</dd>
<dt>not proved</dt><dd>{esc(x['gap'])}</dd>
<dt>ranking</dt><dd>tier {esc(rk.get('tier', '?'))}, {esc(rk.get('cls', ''))}. Next step: {esc(rk.get('next', ''))}</dd>
</dl>
<p class="small"><a href="{x['m']}/explainer.html">explainer</a> · <a href="{x['m']}/proof-status.html">proof status</a> ·
<a href="https://github.com/fractal-geometry-explorer/busy-beaver-explorer/tree/main/holdouts/{x['m']}">folder</a></p>
{run}</div></details>""")

    relhtml = "".join(f'<li id="rel-{k}"><b>{esc(v["name"])}.</b> {esc(v["text"])}</li>' for k, v in rel.items())
    runopts = "".join(f'<option value="{x["rank"]}">#{x["rank"]} {x["m"]}</option>' for x in ms if x.get("runner"))
    runners = json.dumps({str(x["rank"]): [x["runner"], x["runnerStart"], x["m"]] for x in ms if x.get("runner")})
    famchips = json.dumps([[f["key"], f["name"]] for f in D["families"]])

    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Open problems behind the holdouts</title>
<meta name="description" content="For each of the 39 Collatz-hard BB(6) holdouts: the map Lean reduces it to, the exact halting condition, a probabilistic heuristic, and the known open problem it resembles, with a runner for the simpler maps.">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Atkinson+Hyperlegible:ital,wght@0,400;0,700;1,400&family=Martian+Mono:wght@400;500;700&display=swap">
<style>{css}{EXTRA_CSS}</style>
</head>
<body>
<main class="wrap">
<header class="top">
  <p class="crumb"><a href="../index.html">Busy Beaver Explorer</a> / <a href="index.html">holdouts</a> / open problems</p>
  <p class="eyebrow">39 machines, 7 kinds of question</p>
  <h1>Which open problem does each holdout reduce to?</h1>
  <p>The <a href="number-theory.html">number-theory ranking</a> judged 39 holdouts to be genuinely Collatz-hard.
  For each one, Lean proves that the machine halts if and only if an explicit map does something specific. This page
  writes each of those questions down exactly: the map, the halting condition, how far it has been checked, a
  probabilistic guess, and the known problem it most resembles. None of the 39 is decided.</p>
</header>

<section class="verdict">
  <p><b>The 39 questions fall into seven kinds.</b> Every one of them asks about one specific orbit of a map of the kind
  Conway showed can be undecidable in general. The strongest known results, like Tao's on Collatz, cover almost all
  starting values but never one given orbit.</p>
  <ul>
    <li><span class="tag t-kernel">kernel</span> For {nlev['iff']} machines Lean proves "halts if and only if the map's
    condition is met", with no unproved assumption.</li>
    <li><span class="tag t-native">one way</span> For {nlev['oneway']}, Lean proves the direction that matters for
    non-halting: if the condition is never met, the machine never halts.</li>
    <li><span class="tag t-open">partial</span> For {nlev['partial']}, the rules of a period are proved but the reset
    table is still measured.</li>
    <li><span class="tag t-heur">heuristic</span> 31 are expected never to halt. In each case the estimated chance
    of a later halt is small and shrinks as the orbit grows, down to 2<sup>-800,000</sup>. The 8 "epoch" machines are
    expected to halt eventually, but only after an epoch whose outcome no computation can reach.</li>
  </ul>
</section>

<section>
  <h2>The seven kinds of question</h2>
  <div class="list">{''.join(famhtml)}</div>
</section>

<section>
  <h2>The 39 machines</h2>
  <div class="prose"><p>Open a machine to see its question. "kernel" means the halts-iff statement is a Lean theorem
  checked by the kernel. The heuristic is a model, not a theorem.</p></div>
  <div class="controls">
    <div class="chips" id="famchips"></div>
    <input type="search" id="q" placeholder="filter: machine, map, word" aria-label="filter the machines">
  </div>
  <div class="list" id="cards">{''.join(cards)}</div>
</section>

<section id="runner">
  <h2>Run a map</h2>
  <div class="prose"><p>The simpler maps can be iterated here, with exact big integers. Each row is one step of the
  map as Lean states it, and the last column shows how close the orbit is to its halting set. A machine halts exactly
  when its row says so. Starting from another value shows how sparse the halting set is.</p></div>
  <div class="panel">
    <div class="controls">
      <select id="rsel" aria-label="machine">{runopts}</select>
      <label>start <input type="text" id="rstart" size="14"></label>
      <button class="b" id="rgo">50 steps</button><button class="b" id="rmore">50 more</button>
    </div>
    <p class="small" id="rmsg"></p>
    <div class="scroll"><table class="tbl out"><thead id="rhead"></thead><tbody id="rrows"></tbody></table></div>
  </div>
</section>

<section class="prose">
  <h2>Known problems these resemble</h2>
  <ul>{relhtml}</ul>
</section>

<section class="prose">
  <h2>Sources</h2>
  <p>Each machine's folder <code>holdouts/&lt;machine&gt;/</code> has the Lean files named above and a README with the
  derivation. The data for this page is in <a href="https://github.com/fractal-geometry-explorer/busy-beaver-explorer/blob/main/tools/number-theory/open_problems.json">tools/number-theory/open_problems.json</a>,
  and the page is generated by <code>tools/number-theory/build_open_problems.py</code>.</p>
</section>
</main>
<script>
{RUNNER_JS}
const RUNNERS = {runners};
const FAMS = {famchips};
let on = new Set(FAMS.map(f => f[0]));
const chips = document.getElementById('famchips');
for (const [k, n] of FAMS) {{
  const b = document.createElement('button'); b.className = 'chip'; b.textContent = n; b.setAttribute('aria-pressed', 'true');
  b.onclick = () => {{ if (on.has(k)) on.delete(k); else on.add(k); b.setAttribute('aria-pressed', on.has(k)); filt(); }};
  chips.appendChild(b);
}}
function filt() {{
  const q = document.getElementById('q').value.toLowerCase();
  for (const c of document.querySelectorAll('#cards .mc'))
    c.style.display = on.has(c.dataset.fam) && c.dataset.text.includes(q) ? '' : 'none';
}}
document.getElementById('q').oninput = filt;

let cur = null, st = null, done = false, count = 0;
function setup(rank) {{
  const [r, s] = RUNNERS[rank]; cur = RUN[r];
  document.getElementById('rstart').value = s;
  document.getElementById('rhead').innerHTML = '<tr><th>step</th>' + cur.cols.map(c => `<th>${{c}}</th>`).join('') + '</tr>';
}}
function go(fresh) {{
  const msg = document.getElementById('rmsg'), body = document.getElementById('rrows');
  if (fresh) {{ try {{ st = cur.init(document.getElementById('rstart').value); }} catch (e) {{ msg.textContent = 'could not read the start value'; return; }}
    body.innerHTML = ''; done = false; count = 0; msg.textContent = ''; }}
  if (done) return;
  let out = '';
  for (let i = 0; i < 50 && !done; i++) {{
    const r = cur.step(st);
    out += `<tr${{r.stop ? ' class="hit"' : ''}}><td>${{count}}</td>` + r.row.map(c => `<td>${{c}}</td>`).join('') + '</tr>';
    count++;
    if (r.stop) {{ done = true; msg.textContent = r.stop; }} else st = r.s;
  }}
  body.insertAdjacentHTML('beforeend', out);
  if (!done) msg.textContent = `${{count}} steps, no halt`;
}}
const sel = document.getElementById('rsel');
sel.onchange = () => {{ setup(sel.value); go(true); }};
document.getElementById('rgo').onclick = () => go(true);
document.getElementById('rmore').onclick = () => go(false);
for (const b of document.querySelectorAll('button[data-run]')) b.onclick = () => {{
  const rank = b.closest('.mc').id.slice(2); sel.value = rank; setup(rank);
  document.getElementById('rstart').value = b.dataset.start; go(true);
  document.getElementById('runner').scrollIntoView({{ behavior: 'smooth' }});
}};
setup(sel.value); go(true);
</script>
</body>
</html>
"""


if __name__ == "__main__":
    with open(OUT, "w") as f:
        f.write(build())
    print("wrote", OUT)
