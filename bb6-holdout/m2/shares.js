// step shares by the page's categories (same rules as m2sim.classify), online
const M = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = []; M.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65 }; } });
const N = +process.argv[2];
let cap = 1 << 24, t = new Uint8Array(cap), off = cap >> 1, pos = 0, st = 0, steps = 0;
const KN = k => "ABCDEF"[k >> 1] + (k & 1);
const PAT = { L: [1, 9, 2, 4], S: [0, 3], R: [8, 11] };
const cnt = { crawl: 0, run: 0, recode: 0, fill: 0, append: 0, fixed: 0 };
const buf = []; let cur = null, curN = 0, ev = [];
const win = []; // sliding window of 3 tokens: classify the middle one
function classify(prv, tk, nxt) {
  if (tk.c === 'L') return [['crawl', 4 * tk.n]];
  if (tk.c === 'R') return [['run', 2 * tk.n]];
  if (tk.c === 'S') {
    const n = tk.n, ps = prv ? (prv.c || prv.e) : '', ns = nxt ? (nxt.c || nxt.e) : '';
    if (n === 1 && (ns === 'A1' || ns.startsWith('A1 E0 F0 D0')) && (ps === 'L' || ps === '' || ps.endsWith('C0'))) return [['fill', 2]];
    if (n === 1 && ps === 'E1 B1 A0 B0 C1 D0') return [['append', 2]];
    if (n === 1 && ps === 'A1 E1 B0 C1 D0' && ns === 'L') return [['fixed', 2]];
    return [['recode', 2 * n]];
  }
  const w = tk.e, ps = prv ? (prv.c || prv.e) : '';
  const len = w.split(' ').length;
  if (w === 'A1' && ps === 'S') return [['fill', 1]];
  if (w.startsWith('A1 E0 F0 D0') && ps === 'S') return [['fill', 1], ['fixed', len - 1]];
  if (w === 'E1 B1 A0 B0 C1 D0' || w === 'E0 F0 D0') return [['append', len]];
  return [['fixed', len]];
}
function emit(tk) {
  win.push(tk); if (win.length > 3) win.shift();
  if (win.length === 3) for (const [k, n] of classify(win[0], win[1], win[2])) cnt[k] += n;
  else if (win.length === 1) for (const [k, n] of classify(null, win[0], null)) cnt[k] += 0; // first token handled below
}
let first = true;
while (steps < N) {
  const k = st * 2 + t[pos + off]; buf.push(k);
  const r = TR[k]; if (!r) { console.log('HALT'); break; }
  t[pos + off] = r.w; pos += r.d; st = r.n; steps++;
  while (buf.length >= 4) {
    let matched = null;
    for (const c of ['L', 'S', 'R']) { const p = PAT[c]; let ok = true; for (let j = 0; j < p.length; j++) if (buf[j] !== p[j]) { ok = false; break; } if (ok) { matched = c; break; } }
    if (matched) {
      if (ev.length) { emit({ e: ev.map(KN).join(' ') }); ev = []; }
      if (cur === matched) curN++; else { if (cur) emit({ c: cur, n: curN }); cur = matched; curN = 1; }
      buf.splice(0, PAT[matched].length);
    } else { if (cur) { emit({ c: cur, n: curN }); cur = null; curN = 0; } ev.push(buf.shift()); }
  }
}
const tot = Object.values(cnt).reduce((a, b) => a + b, 0);
console.log('classified', tot, 'of', steps);
for (const [k, v] of Object.entries(cnt)) console.log(k.padEnd(7), v, (100 * v / tot).toFixed(4) + '%');
