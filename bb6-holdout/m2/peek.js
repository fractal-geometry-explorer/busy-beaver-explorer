const M = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = [];
M.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65, txt: x }; } });
let cap = 1 << 16, t = new Uint8Array(cap), off = cap >> 1, pos = 0, st = 0, steps = 0, lo = 0, hi = 0;
const S = "ABCDEF";
const N = +process.argv[2], every = +process.argv[3] || 1, start = +process.argv[4] || 0, wl = +process.argv[5] || -40, wh = +process.argv[6] || 40;
const show = () => { let r = ''; for (let i = wl; i <= wh; i++) { const c = t[i+off]; r += i === pos ? (c ? '¹' : '⁰') : (c ? '1' : '.'); } return r; };
while (steps <= N) {
  if (steps >= start && (steps - start) % every === 0) console.log(String(steps).padStart(7), S[st] + t[pos+off], show());
  const r = TR[st*2 + t[pos+off]]; if (!r) { console.log('HALT', steps); break; }
  t[pos+off] = r.w; pos += r.d; st = r.n; steps++;
}
