// fast: at each restart (left edge grows), record defect list; flag adjacent defects other than the leading gap
const M = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = []; M.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65 }; } });
const N = +process.argv[2];
let cap = 1 << 22, t = new Uint8Array(cap), off = cap >> 1, pos = 0, st = 0, steps = 0, lo = 0, hi = 0;
let restarts = 0, flagged = 0; const firstFlags = []; const out = [];
let pending = -1;
while (steps < N) {
  const r = TR[st*2 + t[pos+off]]; if (!r) { console.log('HALT', steps); break; }
  t[pos+off] = r.w; pos += r.d; st = r.n; steps++;
  if (pos > hi) hi = pos;
  if (pos < lo) { lo = pos; pending = steps + 6; }
  if (steps === pending) {
    restarts++;
    // defects (skip blank-right)
    const d = []; let a = lo; while (t[a+off] === 0 && a < hi) a++; // leftmost 1
    for (let i = a; i < hi; i++) { const x = t[i+off], y = t[i+1+off]; if (x === y && !(x === 0 && i + 1 >= hi)) d.push([x, i - a]); }
    let adj = false; for (let k = 1; k < d.length; k++) if (d[k][1] === d[k-1][1] + 1 && d[k][1] > 4) adj = true;
    if (adj) { flagged++; if (firstFlags.length < 12) firstFlags.push(steps + ' ' + d.map(([x, i]) => (x ? 'X' : 'o') + i).join(' ')); }
    if (process.argv[3] && restarts % +process.argv[3] === 0) out.push(steps + ' ' + d.map(([x, i]) => (x ? 'X' : 'o') + i).join(' '));
  }
}
console.log('restarts', restarts, 'flagged', flagged);
console.log(firstFlags.join('\n'));
if (out.length) console.log(out.slice(-20).join('\n'));
