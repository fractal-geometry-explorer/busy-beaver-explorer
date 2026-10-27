// At the start of each round (a new gap just born at the left end), print content width and marks
// relative to the leftmost 1. Marks: G=gap 000 (pos of first 0), M=marker 11, W=wall 00, B=block 111, also raw runs.
const M_ = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = []; M_.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65 }; } });
const N = +process.argv[2];
let cap = 1 << 24, t = new Uint8Array(cap), off = cap >> 1, pos = 0, st = 0, steps = 0, lo = 0, hi = 0;
let pending = false; const out = [];
function marks() {
  let a = lo; while (!t[a + off]) a++; let b = hi; while (!t[b + off]) b--;
  // runs of equal symbols of length >= 2
  const res = []; let i = a;
  while (i <= b) { let j = i; while (j + 1 <= b && t[j + 1 + off] === t[i + off]) j++;
    const L = j - i + 1;
    if (L >= 2) res.push((t[i + off] ? (L === 2 ? 'M' : L === 3 ? 'B' : 'X' + L) : (L === 2 ? 'W' : L === 3 ? 'G' : 'Z' + L)) + (i - a));
    i = j + 1; }
  return { w: b - a + 1, m: res.join(' ') };
}
while (steps < N) {
  const r = TR[st*2 + t[pos+off]]; if (!r) { console.log('HALT', steps); break; }
  t[pos+off] = r.w; pos += r.d; st = r.n; steps++;
  if (pos > hi) hi = pos;
  if (pos < lo) { lo = pos; pending = true; }
  if (pending && st === 4 && t[pos+off] === 0 && pos >= lo + 3) { pending = false; const k = marks(); out.push(steps + ' w' + k.w + ' ' + k.m); }
}
require('fs').writeFileSync(process.argv[3], out.join('\n') + '\n');
console.log(out.length);
