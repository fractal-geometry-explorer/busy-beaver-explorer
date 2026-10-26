const { T, S } = require('./tm2.js');
// Leftward sweep through defect D: tape = (10)^a D (10)^b 11, head A on the left 1 of the final "11"
function left(D, a = 6, b = 6) {
  const cells = "10".repeat(a) + D + "10".repeat(b) + "11";
  const m = new T(cells, cells.length - 2, 0);
  const seen = [];
  while (m.steps < 5000) { const k = m.key(); if (!m.step()) break; seen.push(k); if (m.pos < 0) break; }
  return { D, out: m.rle(), steps: m.steps, state: S[m.st], halted: m.halted };
}
for (const D of ["", "0", "1", "00", "11", "1000", "11000", "100", "0110"]) { const r = left(D); console.log('LEFT  D=' + (D || '∅').padEnd(6), r.halted ? 'HALT' : '', 'steps', r.steps, r.state, r.out); }
// Rightward sweep: tape = 1 0 (10)^a D (10)^b ..., head E on the first 0 (pos 1)
function right(D, a = 6, b = 6) {
  const cells = "10" + "10".repeat(a) + D + "10".repeat(b);
  const m = new T(cells, 1, 4);
  while (m.steps < 5000) { if (!m.step()) break; if (m.pos > cells.length) break; }
  return { out: m.rle(), steps: m.steps, state: S[m.st], halted: m.halted };
}
for (const D of ["", "0", "1", "00", "11", "1000", "11000", "100"]) { const r = right(D); console.log('RIGHT D=' + (D || '∅').padEnd(6), r.halted ? 'HALT' : '', 'steps', r.steps, r.state, r.out); }
