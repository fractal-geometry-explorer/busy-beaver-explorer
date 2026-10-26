// print the window [lo..hi] (relative to m.lo) for every step in [a,b], or only listed steps
const { T, S, TR } = require('./tm2.js');
const [a, b, lo, hi] = process.argv.slice(2).map(Number);
const m = new T('', 0, 0);
while (m.steps < a) m.step();
while (m.steps <= b) {
  let r = ''; for (let i = lo; i <= hi; i++) { const v = m.t[i + m.lo + m.off]; r += (i === m.pos - m.lo) ? (v ? '¹' : '⁰') : (v ? '1' : '·'); }
  const tr = TR[m.st*2 + m.t[m.pos+m.off]];
  console.log(String(m.steps).padStart(7), m.key(), tr ? tr.txt : '---', String(m.pos - m.lo).padStart(4), r);
  if (!m.step()) { console.log('HALT'); break; }
}
