const { T } = require('./tm2.js');
const m = new T('', 0, 0);
const N = +process.argv[2], W = +process.argv[3];
let found = 0;
while (m.steps < N && found < 25) {
  m.step();
  if (m.key() !== 'A1') continue;
  // carrying: head on [1]11 with 0 left
  const g = i => m.t[i + m.off];
  if (!(g(m.pos+1) === 1 && g(m.pos+2) === 1 && g(m.pos-1) === 0 && g(m.pos+3) === 0)) continue;
  let a = m.lo; while (g(a) === 0) a++; let b = m.hi; while (g(b) === 0) b--;
  if (b - a + 1 > W) continue;
  let s = ''; for (let i = a; i <= b; i++) s += g(i);
  // mark packet cells as p
  const rel = m.pos - a;
  const s2 = s.slice(0, rel) + 'ppp' + s.slice(rel + 3);
  const hasGap = /000/.test(s2.slice(0, rel)), right = s2.slice(rel + 3);
  const hasMarker = /11/.test(right), hasWall = /(^|1)00(1|$)/.test(right);
  const leftMarker = /11/.test(s2.slice(0, rel));
  if (hasGap && hasMarker && hasWall) { found++; console.log(m.steps, b - a + 1, rel, s2, leftMarker ? 'LM' : ''); }
}
