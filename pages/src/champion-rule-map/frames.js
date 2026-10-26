const { Sim, TR, SNAME } = require(process.argv[2] + '/engine.js');
// spec: [key, startStep, endStep, leftCells, rightCells]
function frames(key, a, b, L, R, every=1) {
  const s = new Sim(key);
  while (s.steps < a && s.step());
  const p0 = s.pos, lo = p0 - L, hi = p0 + R, out = [];
  // region labels from current segs
  const reg = i => { for (const [x,y,n] of s.segs) if (i>=x&&i<=y) return n; return i > s.segs[s.segs.length-1][1] ? 'blank' : 'blank'; };
  const regs = []; for (let i=lo;i<=hi;i++) regs.push(reg(i));
  while (s.steps <= b) {
    let cells=''; for (let i=lo;i<=hi;i++) cells += s.t[i+s.off];
    const rd = s.t[s.pos+s.off], r = s.halted ? null : TR[s.st*2+rd];
    out.push({ step: s.steps, state: s.halted ? 'H' : SNAME[s.st], head: s.pos-lo, cells, rule: r ? SNAME[s.st]+rd+' '+r.txt : 'halt' });
    if (s.steps === b || !s.step()) break;
  }
  return { key, lo, regs, out };
}
const specs = JSON.parse(process.argv[3]);
const res = specs.map(sp => frames(...sp));
for (const r of res) { console.log('##', r.key, 'regs:', r.regs.map(x=>x[0]).join('')); for (const f of r.out) console.log(String(f.step).padStart(6), f.state, f.cells.slice(0,f.head)+'['+f.cells[f.head]+']'+f.cells.slice(f.head+1), f.rule); }
require('fs').writeFileSync(process.argv[2]+'/frames_out.json', JSON.stringify(res));
