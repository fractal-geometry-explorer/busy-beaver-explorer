"""Writes the explainer section "region" into ../status.json: an interactive map of the region Z_k, n < 12k + 12,
drawn from the proved families of lean/zreg.json (the same case choice as `zmap.pick`).

usage: python3 zpage.py && python3 ../../build_pages.py 1RB---_1LC0LD_0RF0LD_0LE0RA_0LC1RA_1RC1RD
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ST = os.path.join(HERE, "..", "status.json")
Z = json.load(open(os.path.join(HERE, "..", "lean", "zreg.json")))["cases"]

fam = {c["name"]: [c["kind"], c["n"], c["k"], c.get("n2", ""), c.get("tail2", c.get("end", ""))] for c in Z}

JS = r"""
(function () {
  const F = __FAM__;
  const ev = (e, env) => e.split('+').reduce((s, t) => {
    const m = t.split('*');
    if (m.length === 2) return s + (+m[0]) * env[m[1]];
    return s + (/^\d+$/.test(t) ? +t : env[t]);
  }, 0);
  const C = name => +F[name][2].split('+').pop();
  function pick(k, n) {
    if (k === 0 && n >= 24) return [`zz${n % 2}`, {m: (n - 24) >> 1}];
    if (!(n < 12 * k + 12 || k === 0)) return null;
    if (n < 24) {
      const r = n, q = r % 8 === 7 ? 8 : 1, nm = q > 1 ? `zs${r}_${k % q}` : `zs${r}`;
      if (k >= C(nm)) return [nm, {e: (k - C(nm)) / q}];
      return [(r === 21 && k === 1) ? 'zh0' : `zt${r}_${k}`, {}];
    }
    const j = Math.floor((n - 24) / 24), r = (n - 24) % 24, s = k - 2 * j, q = r % 8 === 7 ? 8 : 1;
    const nm = q > 1 ? `zr${r}_${s % q}` : `zr${r}`;
    if (s >= C(nm)) return [nm, {j: j, e: (s - C(nm)) / q}];
    return [(r === 21 && s === 3) ? 'zh' : `zb${r}_${s}`, {j: j}];
  }
  function tailOf(t, env) {
    return t.split(' ').map(x => {
      const m = x.match(/^\(([01]+)\)\^(.+)$/);
      return m ? {w: m[1], c: ev(m[2], env)} : {w: x, c: 1};
    });
  }
  const show = parts => {
    const o = [];
    parts.forEach(p => {
      const lit = p.c === 1 && p.w.length === 1;
      if (lit && o.length && o[o.length - 1].lit) o[o.length - 1].s += p.w;
      else o.push({lit, s: lit ? p.w : `(${p.w})^${p.c}`});
    });
    return o.map(x => x.s).join(' ');
  };
  function classify(kind, t) {
    if (kind === 'halt') return 'halt';
    const s = t.replace(/\^[0-9a-z*+]+/g, '^#');
    if (['1', '0 0 0 1', '0 0 0 (10)^# 1', '0 0 0 (10)^# 0 0 0 1', '0 0 0 0 0 0 1'].includes(s)) return 'known';
    if (s.startsWith('1 1 (01)^#')) return 'yw';
    if (s === '0 0 0 (10)^# 0 0 0 (10)^# 1') return 'two';
    if (s.startsWith('0 0 0 (10)^#')) return 'xw';
    return 'small';
  }
  const LAB = {known: 'back to a mapped tail (1, X, Z)', xw: 'X-block, new end word', yw: 'Y-block, new end word',
               two: 'two blocks', small: 'short new word', halt: 'halts in this pass'};
  const VAR = {known: '--kernel', xw: '--accent', yw: '--computed', two: '--heur', small: '--muted', halt: '--open'};
  const KMAX = 24, CH = 9, NMAX = 12 * KMAX + 12, cv = document.getElementById('zr-map'), out = document.getElementById('zr-out');
  const kin = document.getElementById('zr-k'), nin = document.getElementById('zr-n');
  function result(k, n) {
    const p = pick(k, n);
    if (!p) return null;
    const f = F[p[0]], env = p[1];
    if (f[0] === 'halt') return {name: p[0], env, kind: 'halt', cls: 'halt'};
    const t = tailOf(f[4], env);
    return {name: p[0], env, kind: 'ev', n2: ev(f[3], env), tail: t, cls: classify('ev', f[4])};
  }
  function draw() {
    const css = getComputedStyle(document.documentElement), W = cv.clientWidth || 560, cw = W / NMAX, ch = CH;
    cv.width = Math.round(W * devicePixelRatio); cv.height = Math.round((KMAX + 1) * ch * devicePixelRatio);
    cv.style.height = ((KMAX + 1) * ch) + 'px';
    const g = cv.getContext('2d'); g.scale(devicePixelRatio, devicePixelRatio);
    g.fillStyle = css.getPropertyValue('--sunk') || '#eee'; g.fillRect(0, 0, W, (KMAX + 1) * ch);
    for (let k = 0; k <= KMAX; k++) for (let n = 0; n < Math.min(NMAX, 12 * k + 12); n++) {
      const r = result(k, n);
      g.fillStyle = css.getPropertyValue(VAR[r.cls]).trim() || '#888';
      g.fillRect(n * cw, (KMAX - k) * ch, Math.max(cw, 1), ch - 1);
      if (r.cls === 'halt') { g.fillRect(n * cw - 2, (KMAX - k) * ch - 1, Math.max(cw, 1) + 4, ch + 1); }
    }
    const sk = +kin.value, sn = +nin.value;
    if (sk <= KMAX && sn < NMAX) {
      g.strokeStyle = css.getPropertyValue('--ink').trim() || '#000'; g.lineWidth = 1.5;
      g.strokeRect(sn * cw - 2, (KMAX - sk) * ch - 2, Math.max(cw, 1) + 4, ch + 3);
    }
  }
  function describe() {
    const k = Math.max(0, Math.floor(+kin.value || 0)), n = Math.max(0, Math.floor(+nin.value || 0));
    const r = result(k, n);
    const start = `E&gt; 0^6 (10)^${n} 000 (10)^${k} 0001`;
    if (!r) { out.innerHTML = `<p><code>${start}</code>: n &ge; 12k + 12, outside the region; the map of Map.lean applies (a 3/2 pass).</p>`; return; }
    const f = F[r.name], vars = Object.entries(r.env).map(([a, b]) => `${a} = ${b}`).join(', ');
    let h = `<p><b>Z<sub>${k}</sub>, n = ${n}</b>: family <code>${r.name}</code> (n = ${f[1]}, k = ${f[2]}${vars ? '; ' + vars : ''}), lemma <code>zw_${r.name}</code> in <code>lean/ZMap.lean</code>.</p>`;
    if (r.kind === 'halt') h += `<p><code>${start}</code> &rarr; <b>halts</b> in this pass (state A reads 1): k is odd and n = 12k + 9.</p>`;
    else h += `<p><code>${start}</code><br>&rarr; <code>E&gt; 0^6 (10)^${r.n2} ${show(r.tail)}</code><br><span class="small">${LAB[r.cls]}</span></p>`;
    out.innerHTML = h;
  }
  cv.addEventListener('click', ev2 => {
    const b = cv.getBoundingClientRect(), W = b.width, cw = W / NMAX;
    const n = Math.floor((ev2.clientX - b.left) / cw), k = KMAX - Math.floor((ev2.clientY - b.top) / CH);
    if (k < 0 || k > KMAX) return;
    kin.value = k; nin.value = Math.min(n, 12 * k + 11); describe(); draw();
  });
  [kin, nin].forEach(x => x.addEventListener('input', () => { describe(); draw(); }));
  const lg = document.getElementById('zr-legend');
  lg.innerHTML = Object.keys(LAB).map(c => `<span style="display:inline-flex;align-items:center;gap:6px;margin-right:14px"><span style="width:12px;height:12px;background:var(${VAR[c]});display:inline-block;border-radius:2px"></span>${LAB[c]}</span>`).join('');
  window.addEventListener('resize', draw);
  describe(); draw();
})();
"""

HTML = [
    "<p>The map of the other sections leaves out one region: Z<sub>k</sub> with n &lt; 12k + 12. There the n-block "
    "runs out before the tail block (10)<sup>k</sup> does, so the pass never reaches its 3/2 part. The whole pass is "
    "the 9/8 phase of a Z tail: each group of nine rounds uses 24 of n and 2 of k. It ends with the rest of the tail "
    "block, about k &minus; n/12, still on the tape, followed by a new end word. For n &equiv; 7 (mod 8) the rest of the block is "
    "itself multiplied by 9/8 before the next E-event, a second level of the same mechanism.</p>",
    "<p><b>Proved in Lean's kernel</b> (<code>lean/ZRegion0&ndash;5.lean</code>, <code>lean/ZMap.lean</code>): 190 "
    "families cover every start of the region, and Z<sub>0</sub> for every n. <code>zregion</code>: the machine halts in "
    "the pass <b>exactly when k is odd and n = 12k + 9</b>. Every other start reaches a next E-event "
    "<code>E&gt; 0^6 (10)^n' T</code>, with n' = (9n + c)/8 and T given by the family.</p>",
    "<p>Each cell below is one start (n across, k up, k &le; 24; the halting starts are the red marks on the line n = 12k + 9), coloured by what the pass leaves behind. "
    "<b>Click a cell</b> or type k and n.</p>",
    "<div id=\"zr-legend\" class=\"small\" style=\"margin:8px 0\"></div>",
    "<canvas id=\"zr-map\" style=\"width:100%;max-width:720px;display:block;cursor:crosshair;border:1px solid var(--line)\"></canvas>",
    "<p style=\"margin-top:10px\">k <input id=\"zr-k\" type=\"number\" min=\"0\" value=\"11\" style=\"width:6em\"> "
    "n <input id=\"zr-n\" type=\"number\" min=\"0\" value=\"100\" style=\"width:8em\"></p>",
    "<div id=\"zr-out\"></div>",
    "<p>Most new tails are a block followed by a short end word (X- or Y-shaped), and the next passes treat the block "
    "as the counter k of the X and Y rules until the end word is reached. Followed by direct simulation, all 1,248 "
    "region starts with k &lt; 14 either return to the mapped tails within 11 passes (1,220), halt (15: the line n = 12k + 9, "
    "and a few, such as Z<sub>3</sub> at n = 23, two or more passes later), or are the start n = 2, which gives "
    "Z<sub>k+1</sub> at n = 2 again and never halts (13). So after the region the run is again a word on the right "
    "and a number on the left; a full halts-iff needs the X and Y rules for tails with any end word, which is the next step.</p>",
    "<script>" + JS.replace("__FAM__", json.dumps(fam, separators=(",", ":"))) + "</script>",
]

st = json.load(open(ST))
secs = st["explainer"]["sections"]
sec = {"id": "region", "eyebrow": "The region where a halt starts", "heading": "Inside Z<sub>k</sub> with n &lt; 12k + 12",
       "html": HTML}
idx = next((i for i, s in enumerate(secs) if s["id"] == "region"), None)
if idx is None:
    at = next((i for i, s in enumerate(secs) if s["id"] == "proof"), len(secs) - 1) + 1
    secs.insert(at, sec)
else:
    secs[idx] = sec
open(ST, "w").write(json.dumps(st, indent=1))
print("wrote the region section,", len(json.dumps(fam)), "bytes of families")
