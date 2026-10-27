const E_ = require('./engine.js');
const W = 4446761185833621884n;
let st = { W, marks: [{ t: 'G', p: 1n }, { t: 'B', p: 3317621145360338950n }, { t: 'W', p: 4418278703956725807n }], lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity };
for (let r = 0; r < 60; r++) {
  const sh = st.marks.map(m => m.t).join('');
  const Wn = Number(st.W);
  const pos = st.marks.slice(1).map(m => (Number(st.W - m.p) / Wn).toExponential(3)).join(' ');
  const nx = E_.doRound(st, {});
  const mt = nx.meets.map(m => m.kind[0] + m.h.toFixed(2) + '/c' + m.chain).join(',');
  console.log(String(r).padStart(2), sh.padEnd(10), 'dist to end/W:', pos.padEnd(60), 'meets', mt);
  if (nx.stop) { console.log('stop', nx.stop.k); break; }
  st = nx;
}
