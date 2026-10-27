// Start from the clean tape 1 0 (10)^n 1 1 with the head in state C on the second cell; run to the next clean tape.
const M_ = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = []; M_.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65 }; } });
function realf(n, maxSteps) {
  const cap = 1 << 22; const t = new Uint8Array(cap); const off = cap >> 1;
  const L = 2 * n + 4; for (let i = 0; i < L; i++) t[off + i] = (i < 2 * n + 2) ? (i % 2 === 0 ? 1 : 0) : 1;
  let pos = 1, st = 2, steps = 0, lo = 0, hi = L - 1, side = -1;
  while (steps < maxSteps) {
    const r = TR[st * 2 + t[pos + off]]; if (!r) return { halt: true, steps };
    t[pos + off] = r.w; pos += r.d; st = r.n; steps++;
    if (pos < lo) lo = pos; if (pos > hi) hi = pos;
    if (pos <= lo + 1 && side !== -1) { side = -1;
      if (st === 2 && pos === lo + 1 && steps > 10) {
        const W = hi - lo + 1;
        let ok = t[lo + off] === 1 && t[lo + 1 + off] === 0 && t[hi + off] === 1 && t[hi - 1 + off] === 1 && (W - 4) % 2 === 0;
        for (let i = lo + 2; ok && i <= hi - 2; i += 2) if (t[i + off] !== 1 || t[i + 1 + off] !== 0) ok = false;
        if (ok) return { next: (W - 4) / 2, steps };
      }
    }
    if (pos >= hi - 1 && side !== 1) side = 1;
  }
  return { timeout: true, steps };
}
const ns = process.argv.slice(2).map(Number);
for (const n of ns) console.log(n, JSON.stringify(realf(n, 4e9)));
