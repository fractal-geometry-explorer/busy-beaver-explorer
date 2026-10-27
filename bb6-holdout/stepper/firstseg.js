// clean tape n -> GM state of width N = 2n + 6 -> after one round the first GMM state: read off m as a function of N
const E_ = require('./engine.js');
for (const n of [1000n, 1002n, 1004n, 2000n, 2002n, 1001n, 1003n]) {
  const N = 2n * n + 6n;
  let st = { W: N, marks: [{ t: 'G', p: 1n }, { t: 'M', p: N - 2n }], lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity };
  const sh = [];
  for (let r = 0; r < 3; r++) { const nx = E_.doRound(st, {}); if (nx.stop) { sh.push('stop:' + nx.stop.k); break; } sh.push(nx.marks.map(q => q.t + q.p).join(' ') + ' W=' + nx.W); st = nx; }
  console.log('n', String(n), 'N', String(N), '|', sh.join(' | '));
}
