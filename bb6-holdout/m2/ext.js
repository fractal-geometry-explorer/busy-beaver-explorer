const M = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = []; M.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65 }; } });
let cap = 1 << 16, t = new Uint8Array(cap), off = cap >> 1, pos = 0, st = 0, steps = 0, lo = 0, hi = 0;
const S = "ABCDEF", N = +process.argv[2];
const tape = () => { let r=''; for (let i=lo;i<=hi;i++){ const c=t[i+off]; r += i===pos ? (c?'[1]':'[0]') : (c?'1':'.'); } return r; };
let lastlo = 0, lasthi = 0;
while (steps <= N) {
  const r = TR[st*2 + t[pos+off]]; if (!r) { console.log('HALT', steps); break; }
  t[pos+off] = r.w; pos += r.d; st = r.n; steps++;
  if (pos < lo) { lo = pos; console.log(String(steps).padStart(8), 'L', S[st], tape()); }
  if (pos > hi) { hi = pos; console.log(String(steps).padStart(8), 'R', S[st], tape()); }
}
