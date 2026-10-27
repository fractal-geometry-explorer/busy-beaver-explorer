// Online classification: tokens = L/R/S cycle runs and event words; count event words with context
const M = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = []; M.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65 }; } });
const N = +process.argv[2];
let cap = 1 << 24, t = new Uint8Array(cap), off = cap >> 1, pos = 0, st = 0, steps = 0;
const KN = k => "ABCDEF"[k >> 1] + (k & 1);
// buffer of keys; greedy match cycles at buffer head
const buf = []; const toks = []; const ctx = {}; const counts = { L: 0, R: 0, S: 0, ev: 0 };
const PAT = { L: [1, 9, 2, 4], S: [0, 3], R: [8, 11] }; // key codes: A0=0 A1=1 B0=2 B1=3 C0=4 C1=5 D0=6 D1=7 E0=8 E1=9 F0=10 F1=11
let cur = null, curN = 0, ev = [];
function emit(tok) { // tok: {c:'L',n} or {e:'...'}
  toks.push(tok); if (toks.length > 3) toks.shift();
  if (toks.length === 3 && toks[1].e) { const k = (toks[0].c||'?') + ' [' + toks[1].e + '] ' + (toks[2].c||'?'); ctx[k] = (ctx[k]||0) + 1; }
}
let halted = false;
while (steps < N) {
  const k = st * 2 + t[pos + off]; buf.push(k);
  const r = TR[k]; if (!r) { halted = true; break; }
  t[pos + off] = r.w; pos += r.d; st = r.n; steps++;
  if (pos + off < 2 || pos + off > cap - 2) { console.log('tape overflow'); break; }
  // try to consume buffer
  while (buf.length >= 4) {
    let matched = null;
    for (const c of ['L', 'S', 'R']) { const p = PAT[c]; let ok = true; for (let j = 0; j < p.length; j++) if (buf[j] !== p[j]) { ok = false; break; } if (ok) { matched = c; break; } }
    if (matched) {
      if (ev.length) { emit({ e: ev.map(KN).join(' ') }); ev = []; }
      if (cur === matched) curN++; else { if (cur) emit({ c: cur, n: curN }); cur = matched; curN = 1; }
      counts[matched] += PAT[matched].length; buf.splice(0, PAT[matched].length);
    } else {
      if (cur) { emit({ c: cur, n: curN }); cur = null; curN = 0; }
      ev.push(buf.shift()); counts.ev++;
    }
  }
}
console.log(halted ? 'HALT at ' + steps : 'no halt in ' + steps);
const tot = counts.L + counts.R + counts.S + counts.ev;
console.log('share', Object.fromEntries(Object.entries(counts).map(([k, v]) => [k, (100 * v / tot).toFixed(3) + '%'])));
for (const [k, v] of Object.entries(ctx).sort((a, b) => b[1] - a[1])) console.log(String(v).padStart(9), k);
