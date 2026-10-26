const M = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = []; M.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65 }; } });
let cap = 1 << 22, t = new Uint8Array(cap), off = cap >> 1, pos = 0, st = 0, steps = 0, lo = 0, hi = 0;
const N = +process.argv[2]; let nextW = 16;
const rle = () => { let s=''; for (let i=lo;i<=hi;i++) s += t[i+off] ? '1' : '0'; return s.replace(/(10){3,}/g, m => `(10)^${m.length/2} `); };
while (steps <= N) {
  const r = TR[st*2 + t[pos+off]]; if (!r) { console.log('HALT', steps); break; }
  t[pos+off] = r.w; pos += r.d; st = r.n; steps++;
  if (pos < lo) lo = pos; if (pos > hi) hi = pos;
  if (hi - lo + 1 >= nextW) { console.log('width', hi-lo+1, 'steps', steps, 'ratio steps/w^3', (steps/((hi-lo+1)**3)).toFixed(3), 'steps/w^2', (steps/((hi-lo+1)**2)).toFixed(2)); nextW *= 2; }
}
console.log(rle().slice(0, 600));
