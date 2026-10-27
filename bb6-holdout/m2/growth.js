const { T } = require('./tm2.js');
const [a, b] = process.argv.slice(2).map(Number);
const m = new T('', 0, 0);
let L1 = 0, R1 = 0; // leftmost/rightmost ever-written 1 positions tracked incrementally
const ext = () => { let x = m.lo; while (x <= m.hi && !m.t[x + m.off]) x++; let y = m.hi; while (y >= m.lo && !m.t[y + m.off]) y--; return [x, y]; };
while (m.steps < a) m.step();
let [pl, pr] = ext();
console.log('start', m.steps, pl, pr, pr - pl + 1);
while (m.steps < b) {
  m.step();
  if (m.pos <= pl + 2 || m.pos >= pr - 2) {
    const [l, r] = ext();
    if (l !== pl || r !== pr) { if (Math.abs(l - pl) + Math.abs(r - pr) > 0) console.log(m.steps, 'L', pl, '->', l, ' R', pr, '->', r, ' width', r - l + 1); pl = l; pr = r; }
  }
}
