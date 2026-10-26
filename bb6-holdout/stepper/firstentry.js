// for even n in a range: does the FIRST segment (from the first GMM state) reach a phase-0 plain entry? print (m, E) when it does
const E_ = require('./engine.js');
const lo = BigInt(process.argv[2]), hi = BigInt(process.argv[3]);
let found = 0;
for (let n = lo; n < hi && found < 12; n += 2n) {
  const N = 2n * n + 6n;
  let st = { W: N, marks: [{ t: 'G', p: 1n }, { t: 'M', p: N - 2n }], lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity };
  let nx = E_.doRound(st, {}); st = nx;           // round 1 -> first GMM state
  const m0 = st.marks[1].p, E0 = st.W;
  const hist = [];
  for (let r = 0; r < 400; r++) {
    nx = E_.doRound(st, {}); if (nx.stop) break;
    const sh = nx.marks.map(q => q.t).join(''); hist.push(sh); const L = hist.length; const ms = nx.marks;
    if (L >= 3 && hist[L - 3] === 'GWWW' && hist[L - 2] === 'GBW' && hist[L - 1] === 'GMB') { console.log('n', String(n), 'first GMM state m', String(m0), 'E', String(E0), '2m-E', String(2n * m0 - E0), 'route', hist.slice(0, L - 2).join(' ')); found++; break; }
    if (ms.length === 3 && ms[1].t === 'M' && ms[2].t === 'M' && ms[2].p === nx.W - 2n) break;   // segment ends
    if (ms.length === 2 && ms[1].t === 'M' && ms[1].p === nx.W - 2n) break;
    st = nx;
  }
}
console.log('found', found);
