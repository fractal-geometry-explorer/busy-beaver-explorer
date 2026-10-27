// one pass of the plain loop, round by round, from a phase-0 pass start: print marks and end meetings
const E_ = require('./engine.js');
const a = 1000001n, b = 5000000n, c = 9999999n, E = 10000000n + 2048n * 3n; // R = E - c - 1
let st = { W: E, marks: [{ t: 'G', p: 1n }, { t: 'W', p: a }, { t: 'W', p: b }, { t: 'W', p: c }], lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity };
console.log('R =', String(E - c - 1n), 'L1 =', String(147n * b + 280n * E - 392n * c - 578n), 'check', E_.checkTape(E, st.marks));
for (let r = 0; r < 9; r++) {
  const nx = E_.doRound(st, {});
  if (nx.stop) { console.log('stop', nx.stop.k, nx.stop.text); break; }
  console.log('round', r + 1, nx.marks.map(q => q.t + String(q.p)).join(' '), 'W=' + nx.W, 'meets:', nx.meets.map(q => q.kind + ' d=' + q.d).join(', '));
  st = nx;
}
