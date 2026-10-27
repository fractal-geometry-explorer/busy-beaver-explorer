// round-start mark lists for one cycle starting from clean n
const M_ = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = []; M_.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65 }; } });
const n = +process.argv[2];
const cap = 1 << 22; const t = new Uint8Array(cap); const off = cap >> 1;
const L = 2 * n + 4; for (let i = 0; i < L; i++) t[off + i] = (i < 2 * n + 2) ? (i % 2 === 0 ? 1 : 0) : 1;
let pos = 1, st = 2, steps = 0, lo = 0, hi = L - 1, pending = false, rounds = 0;
function marks() {
  let a = lo; while (!t[a + off]) a++; let b = hi; while (!t[b + off]) b--;
  const res = []; let i = a;
  while (i <= b) { let j = i; while (j + 1 <= b && t[j + 1 + off] === t[i + off]) j++;
    const Ln = j - i + 1;
    if (Ln >= 2) res.push((t[i + off] ? (Ln === 2 ? 'M' : Ln === 3 ? 'B' : 'X' + Ln) : (Ln === 2 ? 'W' : Ln === 3 ? 'G' : 'Z' + Ln)) + (i - a));
    i = j + 1; }
  return 'w' + (b - a + 1) + ' ' + res.join(' ');
}
while (steps < 4e9) {
  const r = TR[st * 2 + t[pos + off]]; if (!r) { console.log('HALT', steps); break; }
  t[pos + off] = r.w; pos += r.d; st = r.n; steps++;
  if (pos > hi) hi = pos;
  if (pos < lo) { lo = pos; pending = true; }
  if (pending && st === 4 && t[pos + off] === 0 && pos >= lo + 3) {
    pending = false; const s = marks(); console.log(steps + ' ' + s); rounds++;
    if (/^w\d+ G1 M\d+$/.test(s) && rounds > 1) { const w = +s.split(' ')[0].slice(1); const [_, p] = s.split(' M'); if (+p === w - 2) break; }
  }
}
