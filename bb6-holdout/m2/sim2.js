const M = process.argv[2] || "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = [];
M.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---" || x[2] === "Z") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65 }; } });
const N = +process.argv[3] || 1e8;
let cap = 1 << 20, t = new Uint8Array(cap), off = cap >> 1, pos = 0, st = 0, steps = 0, lo = 0, hi = 0;
while (steps < N) {
  const r = TR[st*2 + t[pos+off]];
  if (!r) { console.log("HALT at step", steps, "state", "ABCDEF"[st], "reading", t[pos+off]); break; }
  t[pos+off] = r.w; pos += r.d; st = r.n; steps++;
  if (pos < lo) lo = pos; if (pos > hi) hi = pos;
  if (pos + off < 10 || pos + off > cap - 10) { const nc = cap*2, nt = new Uint8Array(nc); nt.set(t, cap >> 1); off += cap >> 1; t = nt; cap = nc; }
}
let ones = 0; for (let i = lo; i <= hi; i++) ones += t[i+off];
console.log("steps", steps, "span", lo, hi, "width", hi-lo+1, "ones", ones);
