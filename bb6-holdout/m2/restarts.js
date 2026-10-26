// at each moment a new gap is born at the left edge (head enters E0 at lo+3 after restart), list defects
const { T, S } = require('./tm2.js');
const N = +process.argv[2];
const m = new T('', 0, 0);
const defs = () => { const out = []; for (let i = m.lo; i <= m.hi; i++) { const x = m.t[i+m.off], y = m.t[i+1+m.off]; if (x === y && !(x===0 && i+1>m.hi)) out.push((x ? 'X' : 'o') + (i - m.lo)); } return out; };
let prevLo = 0;
while (m.steps < N) {
  if (!m.step()) { console.log('HALT', m.steps); break; }
  if (m.lo < prevLo) { prevLo = m.lo; // left edge grew: a restart in progress; report a few steps later
    for (let k = 0; k < 6; k++) m.step();
    const d = defs();
    console.log(String(m.steps).padStart(9), 'w' + (m.hi - m.lo + 1), d.join(' '));
  }
}
