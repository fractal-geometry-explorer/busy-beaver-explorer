// Run a G W W W W state on the stepper engine; at the first plain phase-0 pass start report s, lambda, sigma.
const E_ = require('./engine.js');
const v = process.argv.slice(2).map(BigInt); const [a, b, c, d, E] = v;
let st = { W: E, marks: [{ t: 'G', p: 1n }, { t: 'W', p: a }, { t: 'W', p: b }, { t: 'W', p: c }, { t: 'W', p: d }], lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity };
console.log('tape check:', JSON.stringify(E_.checkTape(E, st.marks)));
const hist = [], states = []; let maxc = 0;
for (let r = 0; r < 80; r++) {
  const nx = E_.doRound(st, {});
  if (nx.stop) { console.log('stop', nx.stop.k, nx.stop.text); break; }
  const sh = nx.marks.map(m => m.t).join(''); hist.push(sh); states.push(nx);
  for (const m of nx.meets) { if (m.chain === 1 && r > 0) { console.log('chain broke at round', r + 1); } maxc = Math.max(maxc, m.chain); }
  const L = hist.length;
  if (L >= 3 && hist[L - 3] === 'GWWW' && hist[L - 2] === 'GBW' && hist[L - 1] === 'GMB') {
    const s0 = states[L - 3]; const ms = s0.marks;
    const R1 = s0.W - ms[3].p - 1n, L1 = 147n * ms[2].p + 280n * s0.W - 392n * ms[3].p - 578n;
    const s = E_.lg2(s0.W) - E_.lg2(R1), lam = E_.lg2(L1 < 0n ? -L1 : L1) - E_.lg2(s0.W);
    console.log('plain entry after', L - 2, 'rounds; R1 =', String(R1), 's', s.toFixed(3), 'lambda', lam.toFixed(3), 'sigma', (3 * s + 2 * lam).toFixed(3), 'chain', maxc);
    console.log(hist.slice(0, L - 2).join(' '));
    break;
  }
  st = nx;
}
