const M = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = []; M.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65 }; } });
let cap = 1 << 22, t = new Uint8Array(cap), off = cap >> 1, pos = 0, st = 0, steps = 0, lo = 0, hi = 0;
const S="ABCDEF", N = +process.argv[2], from = +(process.argv[3]||0);
const rle = () => { let s=''; for (let i=lo;i<=hi;i++) s += (i===pos? '|' : '') + (t[i+off] ? '1' : '0'); return s.replace(/(10){2,}/g, m => ` (10)^${m.length/2} `).replace(/(01){2,}/g, m => ` (01)^${m.length/2} `); };
let side = 0; // which end we last logged
while (steps <= N) {
  const r = TR[st*2 + t[pos+off]]; if (!r) { console.log('HALT', steps); break; }
  t[pos+off] = r.w; pos += r.d; st = r.n; steps++;
  if (pos < lo) lo = pos; if (pos > hi) hi = pos;
  if (pos <= lo + 1 && side !== -1) { side = -1; if (steps >= from) console.log(String(steps).padStart(9), 'L', S[st], rle()); }
  if (pos >= hi - 1 && side !== 1) { side = 1; if (steps >= from) console.log(String(steps).padStart(9), 'R', S[st], rle()); }
}
