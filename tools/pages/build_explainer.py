"""Build a machine's interactive explainer page from its status.json.

usage: python3 tools/pages/build_explainer.py STATUS.json OUT.html

Every machine studied here wants the same first page: the transition table, where a halt can come from, the real
machine running in the browser, a space-time diagram and the records of its run, and a ledger of what is known sorted
by what it rests on. This writes that page for any two-symbol machine, from the same status.json that
`build_status.py` reads, so a new machine has an explainer on day one and the ledger never drifts from the
proof-status page.

What is about one machine only goes in the optional "explainer" object of the JSON:

  title       the page's h1 (default "Does this machine ever halt?")
  lede        the paragraph under it
  facts       [{level, value, text}]: headline cards (level as in build_status.LEVELS)
  presets     [steps]: buttons that jump the simulator to these step counts
  spacetime   {steps, rows}: the default range of the space-time diagram
  (top level) elsewhere  [{kind, title, text}]: proofs and labels from outside the machine's own ledger, shown
              in a box under the headline cards (kind "proof", "report" or "label"); see build_status.py
  sections    [{id, eyebrow, heading, html}]: hand-written sections (HTML) placed after the generated ones, for the
              macro structure once it is found; `html` may be a list of strings, joined with newlines

The generated parts are the transition table, the state diagram (which follows the simulator and counts how
often each transition has fired), the halting analysis (which transitions lead into each halting
transition, and so which local pattern halts), the simulator, the diagram and records, the ledger and the check
commands. The simulator's engine is the `<script id="engine">` block; tools/tests/test_tools.py runs it in Node
against tools/py/bbtools on random machines.
"""
import html
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "py"))

from bbtools.machine import STATES, Machine  # noqa: E402

LEVELS = [
    ("kernel", "k", "Kernel", "proved in Lean, checked by the kernel only"),
    ("native", "n", "native_decide", "proved in Lean, one evaluation trusts the compiler"),
    ("trusted", "c", "Computed", "C or Python in the repository, tested but not proved"),
    ("heuristic", "h", "Heuristic", "evidence and estimates"),
    ("open", "o", "Open", "not known"),
]
LEVEL = {k: (cls, name) for k, cls, name, _ in LEVELS}

CSS = """
:root{
  --bg:#f5f6f8; --surface:#ffffff; --sunk:#eceef2; --line:#d9dce3; --line-strong:#b9bec9;
  --fg:#14171d; --fg2:#4a505c; --muted:#7a808c; --accent:#2350a8; --accent-soft:#e3eaf8;
  --ink:#1b2230; --cell0:#ffffff; --head:#d2551f;
  --kernel:#1c7a4d; --kernel-bg:#e2f3ea; --native:#2350a8; --native-bg:#e3eaf8;
  --computed:#9a6400; --computed-bg:#fbf0d9; --heur:#7a4fb5; --heur-bg:#efe8f8; --open:#b3363a; --open-bg:#f8e3e3;
  --display:"Bricolage Grotesque", "Avenir Next", system-ui, sans-serif;
  --body:"IBM Plex Sans", system-ui, -apple-system, "Segoe UI", sans-serif;
  --mono:"JetBrains Mono", ui-monospace, "SFMono-Regular", Menlo, monospace;
  color-scheme:light;
}
@media (prefers-color-scheme: dark){ :root:not([data-theme="light"]){
  --bg:#11141a; --surface:#181c24; --sunk:#0d1015; --line:#2a303b; --line-strong:#3c4452;
  --fg:#e9ecf2; --fg2:#b4bac6; --muted:#858c99; --accent:#8fb0f0; --accent-soft:#1d2a44;
  --ink:#dfe5f0; --cell0:#11141a; --head:#f08a55;
  --kernel:#5cc893; --kernel-bg:#14301f; --native:#8fb0f0; --native-bg:#1d2a44;
  --computed:#e7b453; --computed-bg:#33280f; --heur:#b99cf0; --heur-bg:#2a2040; --open:#f08488; --open-bg:#3a1c1e;
  color-scheme:dark; } }
:root[data-theme="dark"]{
  --bg:#11141a; --surface:#181c24; --sunk:#0d1015; --line:#2a303b; --line-strong:#3c4452;
  --fg:#e9ecf2; --fg2:#b4bac6; --muted:#858c99; --accent:#8fb0f0; --accent-soft:#1d2a44;
  --ink:#dfe5f0; --cell0:#11141a; --head:#f08a55;
  --kernel:#5cc893; --kernel-bg:#14301f; --native:#8fb0f0; --native-bg:#1d2a44;
  --computed:#e7b453; --computed-bg:#33280f; --heur:#b99cf0; --heur-bg:#2a2040; --open:#f08488; --open-bg:#3a1c1e;
  color-scheme:dark; }
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);font:16px/1.62 var(--body);
  padding-left:max(16px, env(safe-area-inset-left, 0px));padding-right:max(16px, env(safe-area-inset-right, 0px));padding-block:0 64px}
.wrap{max-width:1080px;margin:0 auto}
.col{max-width:68ch}
h1,h2,h3{font-family:var(--display);text-wrap:balance;line-height:1.15;margin:0}
h1{font-size:clamp(2rem,5vw,3.3rem);font-weight:700;letter-spacing:-.01em}
h2{font-size:clamp(1.45rem,3vw,1.95rem);font-weight:700;margin-bottom:.6rem}
h3{font-size:1.12rem;font-weight:700;margin:1.4rem 0 .4rem}
p{margin:.65rem 0}
a{color:var(--accent)}
code,.mono{font-family:var(--mono);font-size:.86em}
code{background:var(--sunk);padding:.08em .32em;border-radius:4px;overflow-wrap:anywhere}
section{padding-block:44px 8px;border-top:1px solid var(--line)}
.eyebrow{font:600 .74rem/1 var(--body);letter-spacing:.12em;text-transform:uppercase;color:var(--muted);margin-bottom:.7rem;display:block}
.lede{font-size:1.14rem;color:var(--fg2)}
.small{font-size:.88rem;color:var(--fg2)}
.ev{display:inline-flex;align-items:center;gap:.35em;font:600 .72rem/1 var(--body);letter-spacing:.04em;text-transform:uppercase;
  padding:.32em .55em;border-radius:999px;white-space:nowrap;vertical-align:.12em}
.ev.k{color:var(--kernel);background:var(--kernel-bg)} .ev.k::before{content:"\\25C6"}
.ev.n{color:var(--native);background:var(--native-bg)} .ev.n::before{content:"\\25C8"}
.ev.c{color:var(--computed);background:var(--computed-bg)} .ev.c::before{content:"\\25B2"}
.ev.h{color:var(--heur);background:var(--heur-bg)} .ev.h::before{content:"\\2248"}
.ev.o{color:var(--open);background:var(--open-bg)} .ev.o::before{content:"?"}
header.hero{padding-block:48px 28px}
.crumb{font-size:.88rem;color:var(--muted);overflow-wrap:anywhere;margin:0 0 18px}
.machine-id{font-family:var(--mono);font-size:clamp(.78rem,2.2vw,1rem);color:var(--fg2);word-break:break-all;margin:.8rem 0 0}
.facts{display:grid;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:12px;margin-top:26px}
.fact{background:var(--surface);border:1px solid var(--line);border-radius:10px;padding:14px 16px;display:flex;flex-direction:column;gap:6px;align-items:flex-start}
.fact b{font:700 1.4rem/1.15 var(--display)}
.else{display:grid;grid-template-columns:repeat(auto-fit,minmax(280px,1fr));gap:12px;margin-top:18px}
.else>div{background:var(--surface);border:1px solid var(--line);border-left:4px solid var(--heur);border-radius:10px;padding:12px 16px;font-size:.93rem}
.else>div.proof{border-left-color:var(--kernel)} .else>div.report{border-left-color:var(--native)}
.else strong{display:block;font-family:var(--display);font-size:1rem;margin-bottom:.2rem}
.sg{display:grid;grid-template-columns:minmax(0,420px) minmax(240px,1fr);gap:22px;align-items:start}
@media (max-width:760px){ .sg{grid-template-columns:1fr} }
.sg svg{width:100%;height:auto;display:block}
.sg svg text{font-family:var(--mono);fill:var(--fg2)}
.sg .node circle{fill:var(--surface);stroke:var(--line-strong);stroke-width:1.5}
.sg .node text{font-weight:700;font-size:15px;fill:var(--fg)}
.sg .node.on circle{fill:var(--head);stroke:var(--head)} .sg .node.on text{fill:var(--surface)}
.sg .edge path{fill:none;stroke:var(--line-strong);stroke-width:1.4}
.sg .edge.s1 path{stroke-dasharray:5 3}
.sg .edge text{font-size:10px}
.sg .edge.next path{stroke:var(--head);stroke-width:3}
.sg .edge.next text{fill:var(--head);font-weight:700}
.sg .edge.halt path{stroke:var(--open)} .sg .edge.halt text{fill:var(--open);font-weight:700}
.sg .edge.dim{opacity:.18}
.use{display:grid;gap:3px;font-family:var(--mono);font-size:.8rem}
.use div{display:grid;grid-template-columns:5.6em minmax(0,1fr) 6.5em;gap:8px;align-items:center;padding:1px 4px;border-radius:4px;cursor:default}
.use div.next{background:var(--accent-soft)}
.use div.halt span:first-child{color:var(--open);font-weight:600}
.use i{display:block;height:9px;background:var(--accent);border-radius:2px;min-width:0}
.use div.never i{background:transparent}
.use .t{text-align:right;color:var(--fg2)}
table.tt td.next{background:var(--accent-soft);outline:2px solid var(--head);outline-offset:-2px}
.key{display:flex;flex-wrap:wrap;gap:10px 18px;margin-top:22px;align-items:center}
.key div{display:flex;gap:8px;align-items:center;font-size:.86rem;color:var(--fg2)}
nav.toc{margin-top:26px;display:flex;flex-wrap:wrap;gap:6px}
nav.toc a{font-size:.84rem;text-decoration:none;color:var(--fg2);border:1px solid var(--line);border-radius:999px;padding:.25em .7em;background:var(--surface)}
nav.toc a:hover{border-color:var(--accent);color:var(--accent)}
.tw{overflow-x:auto;margin:1rem 0}
table{border-collapse:collapse;font-size:.92rem;font-variant-numeric:tabular-nums}
th,td{text-align:left;padding:.42rem .8rem;border-bottom:1px solid var(--line);vertical-align:top}
th{font-weight:600;color:var(--fg2);font-size:.8rem;letter-spacing:.03em}
table.tt td{text-align:center;font-family:var(--mono)} table.tt th{text-align:center}
td.halt{color:var(--open);font-weight:600}
.grid2{display:grid;grid-template-columns:repeat(auto-fit,minmax(300px,1fr));gap:22px}
.grid2>*{min-width:0}
.panel{background:var(--surface);border:1px solid var(--line);border-radius:12px;padding:18px;margin:22px 0}
.controls{display:flex;flex-wrap:wrap;gap:8px;align-items:center}
button,select,input[type=text]{font:500 .9rem var(--body);color:var(--fg);background:var(--surface);border:1px solid var(--line-strong);border-radius:8px;padding:.45em .8em}
button{cursor:pointer}
button:hover{border-color:var(--accent)}
button.primary{background:var(--accent);border-color:var(--accent);color:var(--surface)}
button:focus-visible,select:focus-visible,input:focus-visible,a:focus-visible{outline:2px solid var(--accent);outline-offset:2px}
input[type=text]{font-family:var(--mono);min-width:0;width:11em;max-width:100%}
.readout{display:flex;flex-wrap:wrap;gap:6px 22px;margin:14px 0 6px;font-size:.9rem;color:var(--fg2)}
.readout b{font-family:var(--mono);color:var(--fg);font-weight:600}
.statechip{display:inline-block;min-width:1.6em;text-align:center;font:700 .9rem var(--mono);color:var(--surface);background:var(--head);border-radius:5px;padding:0 .3em}
.cells{display:flex;gap:2px;justify-content:center;margin:14px 0 4px;overflow:hidden}
.cell{width:22px;height:30px;flex:0 0 22px;border:1px solid var(--line-strong);border-radius:3px;background:var(--cell0);position:relative}
.cell.one{background:var(--ink);border-color:var(--ink)}
.cell.out{border-style:dashed;opacity:.5}
.cell.hd{outline:2px solid var(--head);outline-offset:2px}
.cell.hd::after{content:attr(data-s);position:absolute;top:-24px;left:50%;transform:translateX(-50%);font:700 .8rem var(--mono);color:var(--head)}
.cellwrap{padding-top:22px}
.config{font-family:var(--mono);font-size:.82rem;background:var(--sunk);border-radius:8px;padding:10px 12px;overflow-wrap:anywhere;margin-top:10px}
canvas{display:block;max-width:100%}
.stwrap{overflow-x:auto;margin-top:12px}
.cap{font-size:.8rem;color:var(--muted);margin-top:6px}
.log{font-family:var(--mono);font-size:.8rem;max-height:300px;overflow:auto;border-top:1px solid var(--line);margin-top:12px;padding-top:8px}
.log div{display:grid;grid-template-columns:7.5em 1.5em 3.5em minmax(0,1fr);gap:10px;padding:2px 0}
.log div span:last-child{overflow-wrap:anywhere}
.log .t{color:var(--muted);text-align:right}
.claim{border-left:3px solid var(--line-strong);padding:.15rem 0 .15rem .9rem;margin:1rem 0}
.claim.k{border-color:var(--kernel)} .claim.n{border-color:var(--native)} .claim.c{border-color:var(--computed)}
.claim.h{border-color:var(--heur)} .claim.o{border-color:var(--open)}
.claim .where{font-size:.8rem;color:var(--muted);margin-top:.2rem}
.claim p{margin:.35rem 0}
.lfilter{display:flex;flex-wrap:wrap;gap:6px;margin:12px 0}
.lfilter button{font-size:.8rem;padding:.3em .7em;border-radius:999px}
.lfilter button[aria-pressed="true"]{background:var(--fg);color:var(--bg);border-color:var(--fg)}
.litem{display:grid;grid-template-columns:8.5em minmax(0,1fr);gap:12px;padding:10px 0;border-bottom:1px solid var(--line)}
.litem .w{font-size:.78rem;color:var(--muted);overflow-wrap:anywhere}
.litem p{margin:.25rem 0}
pre{font-family:var(--mono);font-size:.8rem;background:var(--sunk);border-radius:8px;padding:12px;overflow-x:auto;line-height:1.5}
footer.foot{border-top:1px solid var(--line);padding-top:18px;margin-top:40px;font-size:.9rem;color:var(--fg2)}
@media (max-width:560px){ .litem{grid-template-columns:1fr;gap:4px} .log div{grid-template-columns:6em 1.2em 3em minmax(0,1fr)} }
@media (prefers-reduced-motion:reduce){ *{scroll-behavior:auto!important;transition:none!important} }
"""

FONTS = ('<link rel="preconnect" href="https://fonts.googleapis.com">\n'
         '<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>\n'
         '<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Bricolage+Grotesque:opsz,wght@12..96,500;'
         '12..96,700&family=IBM+Plex+Sans:ital,wght@0,400;0,500;0,600;1,400&family=JetBrains+Mono:wght@400;600'
         '&display=swap">')

# The simulator. Kept free of the DOM so that tests can run it in Node: `BB.parse`, `BB.Run`, `BB.records`,
# `BB.formatConfig` mirror tools/py/bbtools/machine.py (same step counts, same configuration strings).
ENGINE = r"""
var BB = (function () {
  "use strict";
  var STATES = "ABCDEFGHIJ";
  function parse(text) {
    var groups = text.trim().split("_"), n = groups.length, table = [];
    for (var s = 0; s < n; s++) {
      var g = groups[s], row = [];
      if (g.length !== 6) throw new Error("bad group " + g);
      for (var y = 0; y < 2; y++) {
        var t = g.substr(3 * y, 3), q = STATES.indexOf(t[2]);
        if (t === "---" || q < 0 || q >= n) { row.push(null); continue; }
        row.push([+t[0], t[1] === "R" ? 1 : -1, q]);
      }
      table.push(row);
    }
    return { text: text.trim(), n: n, table: table };
  }
  function Run(m) {
    this.m = m; this.cells = new Uint8Array(1024); this.off = 512;
    this.lo = 0; this.hi = 0; this.head = 0; this.state = 0; this.steps = 0; this.halted = false; this.nOnes = 0;
  }
  Run.prototype.get = function (p) { var i = p + this.off; return i < 0 || i >= this.cells.length ? 0 : this.cells[i]; };
  Run.prototype.grow = function () {
    var n = this.cells.length, c = new Uint8Array(3 * n);
    c.set(this.cells, n); this.cells = c; this.off += n;
  };
  Run.prototype.step = function () {
    if (this.halted) throw new Error("halted");
    var i = this.head + this.off, y = this.cells[i], tr = this.m.table[this.state][y];
    this.steps++;
    if (tr === null) { this.halted = true; return false; }
    this.nOnes += tr[0] - y; this.cells[i] = tr[0];
    this.head += tr[1]; this.state = tr[2];
    if (this.head < this.lo) this.lo = this.head;
    if (this.head > this.hi) this.hi = this.head;
    i = this.head + this.off;
    if (i < 1 || i >= this.cells.length - 1) this.grow();
    return true;
  };
  Run.prototype.run = function (max) { while (this.steps < max) if (!this.step()) return true; return false; };
  Run.prototype.ones = function () { return this.nOnes; };
  Run.prototype.word = function (lo, hi) { var w = []; for (var p = lo; p <= hi; p++) w.push(this.get(p)); return w; };
  Run.prototype.configStr = function () {
    return formatConfig(this.word(this.lo, this.hi), this.head - this.lo, STATES[this.state]);
  };
  function rle(cells) {
    var out = [], i = 0;
    while (i < cells.length) {
      var j = i; while (j < cells.length && cells[j] === cells[i]) j++;
      out.push(j - i > 1 ? cells[i] + "^" + (j - i) : String(cells[i])); i = j;
    }
    return out;
  }
  function formatConfig(cells, h, state) {
    return rle(cells.slice(0, h)).concat([state + ">" + cells[h]], rle(cells.slice(h + 1))).join(" ");
  }
  // [steps, "L"|"R", hi - lo, config] each time the head reaches a new cell, at most k of them.
  function records(m, maxSteps, k) {
    var r = new Run(m), out = [];
    while (r.steps < maxSteps && out.length < k) {
      var lo = r.lo, hi = r.hi;
      if (!r.step()) break;
      if (r.lo < lo) out.push([r.steps, "L", r.hi - r.lo, r.configStr()]);
      else if (r.hi > hi) out.push([r.steps, "R", r.hi - r.lo, r.configStr()]);
    }
    return { records: out, run: r };
  }
  return { STATES: STATES, parse: parse, Run: Run, rle: rle, formatConfig: formatConfig, records: records };
})();
if (typeof module !== "undefined") module.exports = BB;
"""

UI = r"""
(function () {
  "use strict";
  var spec = JSON.parse(document.getElementById("spec").textContent);
  var M = BB.parse(spec.machine), $ = function (id) { return document.getElementById(id); };
  var css = function (v) { return getComputedStyle(document.documentElement).getPropertyValue(v).trim(); };
  var fmt = function (n) { return n.toLocaleString("en-US"); };
  // simulator
  var r = new BB.Run(M), playing = false, raf = 0, cnt = new Float64Array(2 * M.n);
  // state diagram: nodes on a circle; the arrow for (state, symbol) bends to the left of its direction of travel,
  // more for symbol 1, so that the two directions between a pair of states and the two symbols never overlap
  var SG = (function () {
    var C = 210, R = 148, NR = 19, n = M.n, pos = [], svg = "", NS = BB.STATES;
    for (var i = 0; i < n; i++) { var a = -Math.PI / 2 + 2 * Math.PI * i / n; pos.push([C + R * Math.cos(a), C + R * Math.sin(a), a]); }
    svg += '<defs><marker id="sgA" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse">' +
      '<path d="M0 0L10 5L0 10z" fill="context-stroke"/></marker></defs>';
    function f(x) { return x.toFixed(1); }
    for (var s = 0; s < n; s++) for (var y = 0; y < 2; y++) {
      var tr = M.table[s][y], p = pos[s], cls = "edge s" + y, d, lx, ly, lab;
      if (tr === null) {
        var ha = p[2] + (y ? 0.32 : -0.32), x1 = p[0] + NR * Math.cos(ha), y1 = p[1] + NR * Math.sin(ha);
        d = "M" + f(x1) + " " + f(y1) + "L" + f(p[0] + (NR + 20) * Math.cos(ha)) + " " + f(p[1] + (NR + 20) * Math.sin(ha));
        lx = p[0] + (NR + 34) * Math.cos(ha); ly = p[1] + (NR + 34) * Math.sin(ha) + 3; lab = y + ":halt"; cls += " halt";
      } else if (tr[2] === s) {
        var oa = p[2], ox = p[0] + (NR + 15) * Math.cos(oa + (y ? 0.5 : -0.5)), oy = p[1] + (NR + 15) * Math.sin(oa + (y ? 0.5 : -0.5));
        var b0 = oa + (y ? 0.5 : -0.5), sx = p[0] + NR * Math.cos(b0 - 0.45), sy = p[1] + NR * Math.sin(b0 - 0.45);
        var ex = p[0] + NR * Math.cos(b0 + 0.45), ey = p[1] + NR * Math.sin(b0 + 0.45);
        d = "M" + f(sx) + " " + f(sy) + "C" + f(sx + 30 * Math.cos(b0 - 0.5)) + " " + f(sy + 30 * Math.sin(b0 - 0.5)) + " " +
          f(ex + 30 * Math.cos(b0 + 0.5)) + " " + f(ey + 30 * Math.sin(b0 + 0.5)) + " " + f(ex) + " " + f(ey);
        lx = p[0] + (NR + 38) * Math.cos(b0); ly = p[1] + (NR + 38) * Math.sin(b0) + 3; lab = y + ":" + tr[0] + (tr[1] === 1 ? "R" : "L");
      } else {
        var q = pos[tr[2]], dx = q[0] - p[0], dy = q[1] - p[1], L = Math.sqrt(dx * dx + dy * dy), ux = dx / L, uy = dy / L;
        var k = y ? 44 : 16, mx = (p[0] + q[0]) / 2 + uy * k, my = (p[1] + q[1]) / 2 - ux * k;
        var a1 = Math.atan2(my - p[1], mx - p[0]), a2 = Math.atan2(my - q[1], mx - q[0]);
        d = "M" + f(p[0] + NR * Math.cos(a1)) + " " + f(p[1] + NR * Math.sin(a1)) + "Q" + f(mx) + " " + f(my) + " " +
          f(q[0] + (NR + 2) * Math.cos(a2)) + " " + f(q[1] + (NR + 2) * Math.sin(a2));
        // the label sits a third of the way along, where arrows out of one state have not yet crossed the others
        var t = 0.3, bx = (1 - t) * (1 - t) * p[0] + 2 * t * (1 - t) * mx + t * t * q[0], by = (1 - t) * (1 - t) * p[1] + 2 * t * (1 - t) * my + t * t * q[1];
        lx = bx + uy * 9; ly = by - ux * 9 + 3; lab = y + ":" + tr[0] + (tr[1] === 1 ? "R" : "L");
      }
      svg += '<g class="' + cls + '" id="sgE' + s + y + '" data-s="' + s + '"><path d="' + d + '"' + (tr === null ? "" : ' marker-end="url(#sgA)"') +
        '/><text x="' + f(lx) + '" y="' + f(ly) + '" text-anchor="middle">' + lab + "</text></g>";
    }
    for (i = 0; i < n; i++) svg += '<g class="node" id="sgN' + i + '" data-s="' + i + '"><circle cx="' + f(pos[i][0]) + '" cy="' + f(pos[i][1]) +
      '" r="' + NR + '"/><text x="' + f(pos[i][0]) + '" y="' + f(pos[i][1] + 5) + '" text-anchor="middle">' + NS[i] + "</text></g>";
    $("sg").innerHTML = svg;
    var use = "";
    for (s = 0; s < n; s++) for (y = 0; y < 2; y++) {
      tr = M.table[s][y];
      use += '<div id="useR' + s + y + '" data-s="' + s + '"' + (tr === null ? ' class="halt"' : "") + "><span>" + NS[s] + y + " " +
        (tr === null ? "halt" : "&rarr; " + tr[0] + (tr[1] === 1 ? "R" : "L") + NS[tr[2]]) + '</span><span><i></i></span><span class="t">0</span></div>';
    }
    $("use").innerHTML = use;
    function focus(s) {
      document.querySelectorAll("#sg .edge").forEach(function (e) { e.classList.toggle("dim", s !== null && e.dataset.s !== s); });
    }
    document.querySelectorAll("#sg .node, #use div").forEach(function (e) {
      e.onmouseenter = function () { focus(e.dataset.s); }; e.onmouseleave = function () { focus(null); };
    });
    var last = [];
    return function () {
      last.forEach(function (e) { e.classList.remove("on", "next"); }); last = [];
      var max = 1, tot = 0, never = 0, i;
      for (i = 0; i < cnt.length; i++) { if (cnt[i] > max) max = cnt[i]; tot += cnt[i]; }
      for (i = 0; i < cnt.length; i++) {
        var row = $("useR" + (i >> 1) + (i & 1)), sp = row.children;
        sp[1].firstChild.style.width = (cnt[i] ? Math.max(1, 100 * cnt[i] / max) : 0) + "%"; sp[2].textContent = fmt(cnt[i]);
        row.classList.toggle("never", !cnt[i]); if (!cnt[i] && M.table[i >> 1][i & 1] !== null) never++;
      }
      $("useCap").textContent = fmt(tot) + (tot === 1 ? " transition fired" : " transitions fired") + (never ? "; " + never + " of the machine's transitions not used yet" : "") + ".";
      if (r.halted) return;
      var y = r.get(r.head), ids = ["sgN" + r.state, "sgE" + r.state + y, "useR" + r.state + y, "tt" + r.state + y];
      ids.forEach(function (id, j) { var e = $(id); if (e) { e.classList.add(j ? "next" : "on"); last.push(e); } });
    };
  })();
  function draw() {
    SG();
    $("rStep").textContent = fmt(r.steps);
    $("rState").textContent = r.halted ? "halt" : BB.STATES[r.state];
    $("rWidth").textContent = fmt(r.hi - r.lo + 1);
    $("rOnes").textContent = fmt(r.ones());
    var box = $("cells"), w = box.clientWidth || 600, n = Math.max(9, Math.min(41, Math.floor(w / 24) | 1)), h = n >> 1;
    var html = "";
    for (var p = r.head - h; p <= r.head + h; p++) {
      var cls = "cell" + (r.get(p) ? " one" : "") + (p < r.lo || p > r.hi ? " out" : "") + (p === r.head ? " hd" : "");
      html += '<div class="' + cls + '"' + (p === r.head ? ' data-s="' + (r.halted ? "H" : BB.STATES[r.state]) + '"' : "") + "></div>";
    }
    box.innerHTML = html;
    var width = r.hi - r.lo + 1;
    $("config").textContent = width <= 4000 ? r.configStr() : "(" + fmt(width) + " cells: too wide to print here)";
  }
  function advance(n) {
    var target = r.steps + n;
    while (!r.halted && r.steps < target) { cnt[2 * r.state + r.cells[r.head + r.off]]++; if (!r.step()) break; }
  }
  function fresh() { r = new BB.Run(M); cnt.fill(0); }
  function jump(t) { if (t < r.steps) fresh(); advance(t - r.steps); draw(); }
  function loop() {
    if (!playing) return;
    advance(+$("speed").value); draw();
    if (r.halted) { stop(); return; }
    raf = requestAnimationFrame(loop);
  }
  function stop() { playing = false; cancelAnimationFrame(raf); $("play").textContent = "Play"; }
  $("step").onclick = function () { stop(); advance(1); draw(); };
  $("play").onclick = function () {
    if (playing) { stop(); return; }
    playing = true; $("play").textContent = "Pause"; loop();
  };
  $("reset").onclick = function () { stop(); fresh(); draw(); };
  $("jumpGo").onclick = function () {
    stop(); var t = parseInt($("jumpTo").value.replace(/[^0-9]/g, ""), 10);
    if (t >= 0 && t <= 1e9) jump(t);
  };
  document.querySelectorAll("[data-jump]").forEach(function (b) {
    b.onclick = function () { stop(); $("jumpTo").value = b.dataset.jump; jump(+b.dataset.jump); };
  });
  window.addEventListener("resize", draw);
  draw();
  // space-time diagram: one row per sample, the visited tape across
  function spacetime() {
    var mode = $("stMode").value, steps = Math.min(+$("stSteps").value, 1e9), rows = 600;
    var q = new BB.Run(M), snaps = [];
    function snap() { snaps.push([q.steps, q.lo, q.word(q.lo, q.hi), q.head, q.halted]); }
    snap();
    if (mode === "time") {
      var every = Math.max(1, Math.floor(steps / rows));
      while (q.steps < steps && !q.halted) { q.run(Math.min(steps, q.steps + every)); snap(); }
    } else {
      while (q.steps < steps && snaps.length < rows) {
        var lo = q.lo, hi = q.hi;
        if (!q.step()) { snap(); break; }
        if (q.lo < lo || q.hi > hi) snap();
      }
    }
    var lo = Math.min.apply(null, snaps.map(function (s) { return s[1]; }));
    var hi = Math.max.apply(null, snaps.map(function (s) { return s[1] + s[2].length - 1; }));
    var W = hi - lo + 1, cw = Math.max(1, Math.min(12, Math.floor(1000 / W))), ch = Math.max(1, Math.min(8, Math.floor(600 / snaps.length)));
    var cv = $("st"), dpr = window.devicePixelRatio || 1;
    cv.width = W * cw * dpr; cv.height = snaps.length * ch * dpr;
    cv.style.width = W * cw + "px"; cv.style.height = snaps.length * ch + "px";
    var g = cv.getContext("2d"); g.scale(dpr, dpr);
    g.fillStyle = css("--cell0"); g.fillRect(0, 0, W * cw, snaps.length * ch);
    g.fillStyle = css("--sunk");
    snaps.forEach(function (s, i) { g.fillRect((s[1] - lo) * cw, i * ch, s[2].length * cw, ch); });
    g.fillStyle = css("--ink");
    snaps.forEach(function (s, i) { s[2].forEach(function (c, j) { if (c) g.fillRect((s[1] - lo + j) * cw, i * ch, cw, ch); }); });
    g.fillStyle = css("--head");
    snaps.forEach(function (s, i) { g.fillRect((s[3] - lo) * cw, i * ch, cw, ch); });
    var last = snaps[snaps.length - 1];
    $("stCap").textContent = snaps.length + " rows, steps 0 to " + fmt(last[0]) + ", " + fmt(W) + " cells" +
      (last[4] ? "; the machine halted" : "") + ". Time runs down, the tape runs left to right; dark = 1, orange = the head.";
  }
  $("stGo").onclick = spacetime;
  spacetime();
  // records
  function showRecords() {
    var steps = Math.min(+$("recSteps").value, 1e9), res = BB.records(M, steps, 400), out = "";
    res.records.forEach(function (x) {
      out += '<div><span class="t">' + fmt(x[0]) + "</span><span>" + x[1] + '</span><span class="t">' + x[2] +
        "</span><span>" + x[3].replace(/&/g, "&amp;").replace(/</g, "&lt;") + "</span></div>";
    });
    $("recs").innerHTML = out || "<div>none</div>";
    $("recCap").textContent = res.records.length + " records in " + fmt(res.run.steps) + " steps" +
      (res.run.halted ? "; the machine halted" : "") + (res.records.length >= 400 ? " (the first 400 shown)" : "") + ".";
  }
  $("recGo").onclick = showRecords;
  showRecords();
  // ledger
  document.querySelectorAll(".lfilter button").forEach(function (b) {
    b.onclick = function () {
      document.querySelectorAll(".lfilter button").forEach(function (x) { x.setAttribute("aria-pressed", x === b ? "true" : "false"); });
      document.querySelectorAll(".litem").forEach(function (it) {
        it.hidden = b.dataset.f !== "all" && it.dataset.level !== b.dataset.f;
      });
    };
  });
})();
"""


def halt_analysis(m):
    """For each halting transition, the transitions that lead into its state and the local pattern that halts.

    Returns a list of (halting 'Hs', [(pred 'Qr', write, move 'L'|'R', pattern)]), the pattern being the cells around
    the head just before the step that leads into the halt: `Q>r s` when the step moves right onto a cell holding s.
    """
    out = []
    for h in range(m.n):
        for s in (0, 1):
            if m.table[h][s] is not None:
                continue
            preds = []
            for q in range(m.n):
                for r in (0, 1):
                    tr = m.table[q][r]
                    if tr is None or tr[2] != h:
                        continue
                    w, d, _ = tr
                    pat = f"{STATES[q]}>{r} {s}" if d == 1 else f"{s} {STATES[q]}>{r}"
                    preds.append((f"{STATES[q]}{r}", w, "R" if d == 1 else "L", pat))
            out.append((f"{STATES[h]}{s}", preds))
    return out


def _table_html(m):
    rows = []
    for s in range(m.n):
        cells = []
        for y in (0, 1):
            tr = m.table[s][y]
            if tr is None:
                cells.append(f'<td class="halt" id="tt{s}{y}">halt</td>')
            else:
                cells.append(f'<td id="tt{s}{y}">{tr[0]} {"R" if tr[1] == 1 else "L"} {STATES[tr[2]]}</td>')
        rows.append(f"        <tr><th>{STATES[s]}</th>{''.join(cells)}</tr>")
    return "\n".join(rows)


def _halt_html(m):
    parts = []
    for hs, preds in halt_analysis(m):
        state, sym = hs[0], hs[1]
        if not preds:
            parts.append(f"<p>{state} reading {sym} has no transition, but no transition enters {state}: "
                         "from the start state the machine can never halt there.</p>")
            continue
        ways = "; ".join(f"{p} (writes {w}, moves {d}): <code>{html.escape(pat)}</code>" for p, w, d, pat in preds)
        parts.append(f"<p>The machine stops when it is in {state} reading {sym}. {state} is entered only from {ways}. "
                     f"So a halt is the moment {'this pattern appears' if len(preds) == 1 else 'one of these patterns appears'}, "
                     f"with the head on the cell after <code>&gt;</code>.</p>")
    if not parts:
        parts.append("<p>The machine has no halting transition.</p>")
    return "\n    ".join(parts)


def _claim_html(c):
    cls, name = LEVEL[c["level"]]
    where = f'<div class="w">{c["where"]}</div>' if c.get("where") else ""
    return (f'    <div class="litem" data-level="{c["level"]}"><div><span class="ev {cls}">{name}</span>{where}</div>'
            f'<div><b>{c["title"]}</b><p>{c["text"]}</p></div></div>')


def build(spec, home="../index.html"):
    m = Machine.parse(spec["machine"])
    ex = spec.get("explainer", {})
    for c in spec.get("claims", []) + ex.get("facts", []):
        if c["level"] not in LEVEL:
            raise ValueError(f"unknown level {c['level']!r}")
    st = ex.get("spacetime", {})
    st_steps = int(st.get("steps", 2000))
    presets = ex.get("presets", [])
    sections = ex.get("sections", [])
    short = spec.get("crumb", m.text)
    toc = [("machine", "The machine"), ("run", "Watch it run"), ("glance", "The run at a glance")]
    toc += [(s["id"], s["heading"]) for s in sections] + [("ledger", "What is known"), ("check", "Check it")]
    title = ex.get("title", "Does this machine ever halt?")
    o = ["<!doctype html>", '<html lang="en">', "<head>", '<meta charset="utf-8">',
         '<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">',
         f"<title>Inside {html.escape(short)}</title>",
         f'<meta name="description" content="An interactive explainer of the {m.n}-state machine '
         f'{html.escape(m.text)}: the table, where it can halt, the machine running in the browser, a space-time '
         f'diagram, and what is known about it, each result marked by what it rests on.">',
         FONTS, f"<style>{CSS}</style>", "</head>", "<body>", '<div class="wrap">', '<header class="hero">',
         f'  <p class="crumb"><a href="{home}">Busy Beaver Explorer</a> / {html.escape(short)} / explained</p>',
         f'  <span class="eyebrow">A {m.n}-state Busy Beaver machine · {spec.get("asof", "")}</span>',
         f"  <h1>{title}</h1>", f'  <p class="machine-id">{html.escape(m.text)}</p>']
    if ex.get("lede"):
        o.append(f'  <div class="col"><p class="lede">{ex["lede"]}</p></div>')
    if ex.get("facts"):
        o.append('  <div class="facts">')
        for f in ex["facts"]:
            cls, name = LEVEL[f["level"]]
            o.append(f'    <div class="fact"><span class="ev {cls}">{name}</span><b>{f["value"]}</b>'
                     f'<span class="small">{f["text"]}</span></div>')
        o.append("  </div>")
    if spec.get("elsewhere"):
        o.append('  <div class="else" aria-label="Other proofs and outside reports">')
        for e in spec["elsewhere"]:
            o.append(f'    <div class="{html.escape(e["kind"])}"><strong>{e["title"]}</strong>{e["text"]}</div>')
        o.append("  </div>")
    o.append('  <div class="key" aria-label="Evidence levels used on this page">')
    for _, cls, name, gloss in LEVELS:
        o.append(f'    <div><span class="ev {cls}">{name}</span> {gloss}</div>')
    o.append("  </div>")
    o.append('  <nav class="toc" aria-label="Sections">' + "".join(f'<a href="#{i}">{html.escape(t)}</a>' for i, t in toc)
             + "</nav>")
    o.append("</header>")
    n_halt = len(m.halting_transitions())
    o += ['<section id="machine">', '  <span class="eyebrow">The machine</span>',
          f"  <h2>{m.n} states, two symbols, {n_halt} halting transition{'s' if n_halt != 1 else ''}</h2>",
          '  <div class="grid2">', '    <div class="col">',
          "    <p>Each entry says what to write, which way to move and which state to enter. The machine starts in A "
          "on a blank tape (all 0s).</p>", "    " + _halt_html(m), "    </div>",
          '    <div class="tw"><table class="tt" aria-label="Transition table">',
          "      <thead><tr><th>state</th><th>reads 0</th><th>reads 1</th></tr></thead>", "      <tbody>",
          _table_html(m), "      </tbody></table></div>", "  </div>",
          '  <div class="panel">', '    <div class="sg">',
          '      <div><svg id="sg" viewBox="0 0 420 420" role="img" aria-label="State diagram of the machine"></svg>'
          '<div class="cap">One circle per state. A solid arrow is taken on reading 0, a dashed one on reading 1; '
          "its label is <code>read:write move</code>. Red marks a halting transition. Hover a state or a row to "
          "single out its arrows.</div></div>",
          '      <div><div class="small"><b>Follows the simulator below.</b> The orange state is the current one and '
          "the thick arrow is the transition about to fire. The bars count how often each transition has fired "
          'since step 0, so the rare ones stand out.</div>',
          '        <div class="use" id="use" style="margin-top:10px"></div>',
          '        <div class="cap" id="useCap"></div></div>', "    </div>", "  </div>", "</section>"]
    o += ['<section id="run">', '  <span class="eyebrow">Watch it run</span>', "  <h2>The tape from blank, step by step</h2>",
          '  <div class="col"><p>This is the real machine, simulated in your browser. Step it, play it, or jump to a '
          "step count. Below the cells is the whole visited tape in the notation of the notes: <code>1^5</code> is "
          "five 1s, and <code>C&gt;0</code> is the head in state C on a 0.</p></div>",
          '  <div class="panel">', '    <div class="controls">',
          '      <button id="step" type="button">Step</button>',
          '      <button id="play" class="primary" type="button">Play</button>',
          '      <label class="small" for="speed">Speed</label>',
          '      <select id="speed"><option value="1">1 step/frame</option><option value="10" selected>10 steps/frame'
          '</option><option value="1000">1,000 steps/frame</option><option value="100000">100,000 steps/frame</option>'
          "</select>",
          '      <button id="reset" type="button">Reset</button>',
          '      <label class="small" for="jumpTo">Go to step</label>',
          '      <input type="text" id="jumpTo" inputmode="numeric" value="1000" spellcheck="false" autocomplete="off">',
          '      <button id="jumpGo" type="button">Go</button>', "    </div>"]
    if presets:
        o.append('    <div class="controls" style="margin-top:8px"><span class="small">Jump to:</span>'
                 + "".join(f'<button type="button" data-jump="{int(t)}">{int(t):,}</button>' for t in presets) + "</div>")
    o += ['    <div class="readout"><span>step <b id="rStep">0</b></span><span>state <span class="statechip" id="rState">A'
          '</span></span><span>cells visited <b id="rWidth">1</b></span><span>ones <b id="rOnes">0</b></span></div>',
          '    <div class="cellwrap"><div class="cells" id="cells" aria-label="Tape cells around the head"></div></div>',
          '    <div class="cap">Cells around the head (dark = 1, dashed = never visited).</div>',
          '    <div class="config" id="config" aria-live="polite"></div>', "  </div>", "</section>"]
    o += ['<section id="glance">', '  <span class="eyebrow">The run at a glance</span>',
          "  <h2>Space-time diagram and records</h2>",
          '  <div class="col"><p>The diagram stacks the tape at many moments. Sampling at each new cell shows the '
          "shape of the run as the visited region grows; sampling evenly in time shows where the head spends its "
          "time. The records list every step at which the head reaches a cell no earlier step reached, with the "
          "side, the width so far and the whole tape: the first place to look for a repeating macro structure.</p></div>",
          '  <div class="panel">', '    <div class="controls">',
          '      <label class="small" for="stMode">Rows</label>',
          '      <select id="stMode"><option value="rec" selected>at each new cell</option>'
          '<option value="time">evenly in time</option></select>',
          '      <label class="small" for="stSteps">up to step</label>',
          f'      <select id="stSteps">{_steps_options(st_steps)}</select>',
          '      <button id="stGo" class="primary" type="button">Draw</button>', "    </div>",
          '    <div class="stwrap"><canvas id="st" aria-label="Space-time diagram"></canvas></div>',
          '    <div class="cap" id="stCap"></div>', "  </div>",
          '  <div class="panel">', '    <div class="controls">', '      <label class="small" for="recSteps">Records up to step</label>',
          f'      <select id="recSteps">{_steps_options(max(st_steps, 10000))}</select>',
          '      <button id="recGo" class="primary" type="button">List</button>', "    </div>",
          '    <div class="cap" id="recCap"></div>', '    <div class="log" id="recs"></div>', "  </div>", "</section>"]
    for s in sections:
        body = s["html"] if isinstance(s["html"], str) else "\n".join(s["html"])
        o += [f'<section id="{html.escape(s["id"])}">', f'  <span class="eyebrow">{s.get("eyebrow", "")}</span>',
              f'  <h2>{s["heading"]}</h2>', body, "</section>"]
    o += ['<section id="ledger">', '  <span class="eyebrow">What is known</span>',
          "  <h2>Every result, by what it rests on</h2>",
          f'  <div class="col"><p>{spec.get("asof", "")} The same list as the <a href="proof-status.html">proof-status '
          "page</a>, built from the same file.</p></div>",
          '  <div class="lfilter" role="group" aria-label="Filter by evidence level">',
          '    <button type="button" data-f="all" aria-pressed="true">All</button>']
    for key, _, name, _ in LEVELS:
        o.append(f'    <button type="button" data-f="{key}" aria-pressed="false">{name}</button>')
    o.append("  </div>")
    o += [_claim_html(c) for c in spec.get("claims", [])]
    o.append("</section>")
    o += ['<section id="check">', '  <span class="eyebrow">Check it yourself</span>', "  <h2>Commands</h2>",
          "  <pre><code>" + html.escape("\n".join(spec.get("check", []))) + "</code></pre>", "</section>"]
    o += ['<footer class="foot">',
          f'  <p>Built by <code>tools/pages/build_explainer.py</code> from <code>{html.escape(spec.get("source", ""))}'
          "</code>; edit that file and rebuild rather than editing this page.</p>",
          '  <p>Source: <a href="https://github.com/fractal-geometry-explorer/busy-beaver-explorer">'
          "github.com/fractal-geometry-explorer/busy-beaver-explorer</a></p>", "</footer>", "</div>"]
    data = json.dumps({"machine": m.text}).replace("</", "<\\/")
    o += [f'<script type="application/json" id="spec">{data}</script>',
          f'<script id="engine">{ENGINE}</script>', f"<script>{UI}</script>", "</body>", "</html>"]
    return "\n".join(o) + "\n"


def _steps_options(default):
    vals = sorted({200, 1000, 2000, 10000, 100000, 1000000, 10000000, default})
    return "".join(f'<option value="{v}"{" selected" if v == default else ""}>{v:,}</option>' for v in vals)


def main(argv):
    if len(argv) != 2:
        print(__doc__, file=sys.stderr)
        return 1
    with open(argv[0]) as f:
        spec = json.load(f)
    spec.setdefault("source", argv[0])
    with open(argv[1], "w") as f:
        f.write(build(spec, spec.get("home", "../index.html")))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
