// Dumps everything the setup map needs: per-step head position + routine label, tape 1-runs per cell, final layout segments.
const { Sim, SNAME } = require(process.argv[2] + '/engine.js');
const N = 821;
const s = new Sim('real');
const pos = [], key = [], tapes = [];
let lo = 0, hi = 0;
while (s.steps < N) {
  pos.push(s.pos); key.push(SNAME[s.st] + s.t[s.pos + s.off]);
  const row = {}; for (let i = s.lo; i <= s.hi; i++) if (s.t[i + s.off]) row[i] = 1;
  tapes.push(row);
  s.step();
}
pos.push(s.pos);
const row = {}; for (let i = s.lo; i <= s.hi; i++) if (s.t[i + s.off]) row[i] = 1; tapes.push(row);
for (const p of pos) { lo = Math.min(lo, p); hi = Math.max(hi, p); }
for (const r of tapes) for (const c of Object.keys(r)) { lo = Math.min(lo, +c); hi = Math.max(hi, +c); }
// labels (same classifier as the step-share figures)
const lab = key.map(() => 'fixed');
for (let i = 0; i < key.length; i++) {
  const t = key[i], p = i ? key[i - 1] : '', n = key[i + 1] || '';
  if (t === 'A1') lab[i] = 'run';
  else if (t === 'C1' || t === 'F1') lab[i] = 'recode';
  else if (t === 'E1') lab[i] = p === 'F1' ? 'recode' : (p === 'D1' ? 'crawl' : 'fixed');
  else if (t === 'D1') lab[i] = n === 'E1' ? 'crawl' : 'fixed';
  else if (t === 'C0') lab[i] = (p === 'E1' && lab[i - 1] === 'crawl') ? 'crawl' : 'fixed';
}
// vertical runs of 1s per cell over time (row i = tape before step i; row N = after the last step)
const runs = [];
for (let c = lo; c <= hi; c++) {
  let start = -1;
  for (let i = 0; i <= N; i++) {
    const on = !!tapes[i][c];
    if (on && start < 0) start = i;
    if ((!on || i === N) && start >= 0) { runs.push([c, start, on && i === N ? i : i - 1]); start = -1; }
  }
}
const cp = s.cp;
require('fs').writeFileSync(process.argv[2] + '/warmmap.json', JSON.stringify({ N, pos, key, lab, lo, hi, runs, segs: cp ? cp.segs : null }));
console.log('cells', lo, hi, 'runs', runs.length, 'segs', JSON.stringify(cp && cp.segs), 'step', s.steps);
