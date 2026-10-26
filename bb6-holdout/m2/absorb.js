// classify every gap-step-like A0 B1 A1 that follows a carry's C0, by what the packet met, and the result
const M = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = []; M.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65 }; } });
const N = +process.argv[2];
let cap = 1 << 24, t = new Uint8Array(cap), off = cap >> 1, pos = 0, st = 0, steps = 0, lo = 0;
let prev = -1; const tab = {}; const pend = [];
const win = (a, b) => { let s = ''; for (let i = a; i <= b; i++) s += i < lo ? '_' : t[i + off]; return s; };
while (steps < N) {
  const k = st * 2 + t[pos + off];
  if (k === 0 && prev === 4) { // A0 after C0
    const before = win(pos - 3, pos + 2); // pos+1 holds C0's new 1
    let cat = t[pos - 1 + off] === 1 ? 'wall' : (pos - 2 < lo || (t[pos-2+off] === 0 && t[pos-3+off] === 0) ? 'left end' : 'gap');
    pend.push({ at: steps + 3, p: pos, cat, before });
  }
  const r = TR[k]; if (!r) { console.log('HALT'); break; }
  t[pos + off] = r.w; pos += r.d; st = r.n; steps++; if (pos < lo) lo = pos;
  prev = k;
  while (pend.length && pend[0].at === steps) {
    const q = pend.shift(); const after = win(q.p - 3, q.p + 3);
    const key = q.cat + ': ' + q.before + ' -> ' + after;
    tab[key] = (tab[key] || 0) + 1;
  }
}
for (const [k, v] of Object.entries(tab).sort((a, b) => b[1] - a[1])) console.log(String(v).padStart(8), k);
