const { T, S, TR } = require('./tm2.js');
const [a, b, L, R] = process.argv.slice(2).map(Number);
const m = new T("", 0, 0);
while (m.steps < a) m.step();
const c = m.pos, lo = c - L, hi = c + R;
while (m.steps <= b) {
  let r = ''; for (let i = lo; i <= hi; i++) { const v = m.t[i+m.off]; r += i === m.pos ? (v ? '¹' : '⁰') : (v ? '1' : '.'); }
  const k = m.key(); const tr = TR[m.st*2 + m.t[m.pos+m.off]];
  console.log(String(m.steps).padStart(7), k, tr ? tr.txt : '---', r);
  if (!m.step()) { console.log('HALT'); break; }
}
