// collect token windows around rare events: prints pattern counts with run lengths abstracted
const M = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = []; M.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65 }; } });
const N = +process.argv[2];
let cap = 1 << 24, t = new Uint8Array(cap), off = cap >> 1, pos = 0, st = 0, steps = 0;
const KN = k => "ABCDEF"[k >> 1] + (k & 1);
const PAT = { L: [1, 9, 2, 4], S: [0, 3], R: [8, 11] };
const buf = []; let cur = null, curN = 0, ev = [], curStart = 0;
const toks = []; // recent tokens {s, step}
const pats = {}; const examples = {};
const abst = tk => tk.c ? tk.c + (tk.n <= 2 ? tk.n : (tk.n % 2 ? 'odd' : 'even')) : '[' + tk.e + ']';
function emit(tk) {
  toks.push(tk); if (toks.length > 9) toks.shift();
  // window centred at toks[3] if rare
  if (toks.length === 9) {
    const c = toks[3];
    if (c.e && c.e !== 'A1' && c.e !== 'E0 F0 D0' && c.e !== 'A1 E1 B0 C1 D0') {
      const key = toks.slice(1, 9).map(abst).join(' ');
      pats[key] = (pats[key] || 0) + 1; if (!examples[key]) examples[key] = c.step;
    }
  }
}
while (steps < N) {
  const k = st * 2 + t[pos + off]; buf.push(k);
  const r = TR[k]; if (!r) { console.log('HALT', steps); break; }
  t[pos + off] = r.w; pos += r.d; st = r.n; steps++;
  while (buf.length >= 4) {
    let matched = null;
    for (const c of ['L', 'S', 'R']) { const p = PAT[c]; let ok = true; for (let j = 0; j < p.length; j++) if (buf[j] !== p[j]) { ok = false; break; } if (ok) { matched = c; break; } }
    const s0 = steps - buf.length;
    if (matched) {
      if (ev.length) { emit({ e: ev.map(KN).join(' '), step: s0 - ev.length }); ev = []; }
      if (cur === matched) curN++; else { if (cur) emit({ c: cur, n: curN, step: curStart }); cur = matched; curN = 1; curStart = s0; }
      buf.splice(0, PAT[matched].length);
    } else {
      if (cur) { emit({ c: cur, n: curN, step: curStart }); cur = null; curN = 0; }
      ev.push(buf.shift());
    }
  }
}
for (const [k, v] of Object.entries(pats).sort((a, b) => b[1] - a[1])) console.log(String(v).padStart(7), String(examples[k]).padStart(9), k);
