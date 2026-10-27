// print defects (adjacent equal cells) at each direction reversal
const { T, S } = require('./tm2.js');
const [a, b] = process.argv.slice(2).map(Number);
const m = new T("", 0, 0);
const defs = () => { const out = []; for (let i = m.lo; i < m.hi + 1; i++) { const x = m.t[i+m.off], y = m.t[i+1+m.off]; if (x === y && !(x===0 && i+1>m.hi)) out.push((x ? 'X' : 'o') + (i - m.lo)); } return out.join(' '); };
let ring = [], lastDir = 0;
while (m.steps < b) {
  ring.push(m.pos); if (ring.length > 5) ring.shift();
  if (ring.length === 5) { const d = Math.sign(ring[4] - ring[0]);
    if (d && d !== lastDir) { if (m.steps >= a) console.log(String(m.steps).padStart(7), d < 0 ? '<' : '>', 'head@' + (m.pos - m.lo), 'w' + (m.hi - m.lo + 1), defs()); lastDir = d; } }
  if (!m.step()) { console.log('HALT'); break; }
}
