// GMM state (gap at 1, marker m, end marker at E-2, width E) on the stepper engine: shapes until the first phase-0
// plain pass start, then s, lambda and sigma there.
const E_ = require('./engine.js');
const [x0m, x0E, B00, B10, B11, t, k] = process.argv.slice(2).map(Number);
// choose y0, y1 so that E ~ 2^k and m/E ~ t
const Et = 2n ** BigInt(k); const mt = BigInt(Math.floor(t * 1e9)) * Et / 1000000000n;
const b00 = BigInt(B00), b10 = BigInt(B10), b11 = BigInt(B11);
const y0 = (mt - BigInt(x0m)) / b00; const m = BigInt(x0m) + b00 * y0;
const y1 = (Et - BigInt(x0E) - b10 * y0) / b11; const E = BigInt(x0E) + b10 * y0 + b11 * y1;
let st = { W: E, marks: [{ t: 'G', p: 1n }, { t: 'M', p: m }, { t: 'M', p: E - 2n }], lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity };
console.log('m', String(m), 'E', String(E), 'm/E', Number(m) / Number(E), 'tape check', JSON.stringify(E_.checkTape(E, st.marks)));
const hist = [], states = [];
for (let r = 0; r < 300; r++) {
  const nx = E_.doRound(st, {});
  if (nx.stop) { console.log('stop', nx.stop.k, nx.stop.text); break; }
  const sh = nx.marks.map(q => q.t).join(''); hist.push(sh); states.push(nx);
  const L = hist.length;
  if (L >= 3 && hist[L - 3] === 'GWWW' && hist[L - 2] === 'GBW' && hist[L - 1] === 'GMB') {
    const s0 = states[L - 3]; const ms = s0.marks;
    const R1 = s0.W - ms[3].p - 1n, L1 = 147n * ms[2].p + 280n * s0.W - 392n * ms[3].p - 578n;
    const s = E_.lg2(s0.W) - E_.lg2(R1), lam = E_.lg2(L1 < 0n ? -L1 : L1) - E_.lg2(s0.W);
    console.log('first phase-0 entry after', L - 2, 'rounds: s', s.toFixed(3), 'lambda', lam.toFixed(3), 'sigma', (3 * s + 2 * lam).toFixed(3));
    console.log(hist.slice(0, L - 2).join(' '));
    break;
  }
  st = nx;
}
