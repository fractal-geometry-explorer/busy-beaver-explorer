// Find every time the tape is exactly 1 0 (10)^n 1 1 with the head in state C on the second cell.
const M = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = []; M.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65 }; } });
let cap = 1 << 22, t = new Uint8Array(cap), off = cap >> 1, pos = 0, st = 0, steps = 0, lo = 0, hi = 0;
const N = +process.argv[2];
let side = 0, sweeps = 0, lastClean = 0, lastSweeps = 0;
const out = [];
while (steps <= N) {
  const r = TR[st*2 + t[pos+off]]; if (!r) { console.log('HALT', steps); break; }
  t[pos+off] = r.w; pos += r.d; st = r.n; steps++;
  if (pos < lo) lo = pos; if (pos > hi) hi = pos;
  if (pos <= lo + 1 && side !== -1) { side = -1; sweeps++;
    if (st === 2 && pos === lo + 1) {
      // check exact pattern 1 0 (10)^n 1 1
      const L = hi - lo + 1;
      let ok = t[lo+off] === 1 && t[lo+1+off] === 0 && t[hi+off] === 1 && t[hi-1+off] === 1 && (L - 4) % 2 === 0;
      for (let i = lo + 2; ok && i <= hi - 2; i += 2) if (t[i+off] !== 1 || t[i+1+off] !== 0) ok = false;
      if (ok) { const n = (L - 4) / 2; out.push([steps, n, sweeps - lastSweeps]); lastSweeps = sweeps; }
    }
  }
  if (pos >= hi - 1 && side !== 1) side = 1;
}
console.log(out.map(([s, n, k]) => `${n}:${k}`).join(' '));
console.log('count', out.length);
require('fs').writeFileSync('clean.json', JSON.stringify(out));
