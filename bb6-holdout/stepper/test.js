const E = require('./engine.js');
const init = (W, marks) => ({ W, marks, lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity });
const kindOf = st => { const ms = st.marks, W = st.W;
  if (ms.length === 2 && ms[1].t === 'M' && ms[1].p === W - 2n) return 'clean';
  return null; };
let agree = 0, missed = [], flagged = {}, rounds = 0;
function runCase(W, marks, maxR, label) {
  let st = init(W, marks);
  for (let r = 0; r < maxR; r++) {
    const nx = E.doRound(st, {});
    const tm = E.realRound(st.W, st.marks, 5e7);
    rounds++;
    if (nx.stop) { const k = nx.stop.k + (tm.halted ? '/halts' : tm.timeout ? '/timeout' : E.sameMarks(tm.marks, nx.marks) && tm.W === nx.W ? '/same' : '/differs'); flagged[k] = (flagged[k] || 0) + 1; return; }
    if (tm.timeout) return;
    if (tm.halted || tm.W !== nx.W || !E.sameMarks(tm.marks, nx.marks)) { missed.push({ label, r, W: st.W, marks: st.marks.map(m => m.t + m.p).join(' '), tm: tm.halted ? 'HALT' : tm.marks.map(m => m.t + m.p).join(' ') + ' w' + tm.W, model: nx.marks.map(m => m.t + m.p).join(' ') + ' w' + nx.W }); return; }
    agree++;
    st = nx;
    if (kindOf(st) === 'clean' && label.startsWith('clean')) return;
  }
}
for (let n = 2n; n <= 400n; n++) { const W = 2n * n + 6n; runCase(W, [{ t: 'G', p: 1n }, { t: 'M', p: W - 2n }], 2000, 'clean' + n); }
console.log('clean tapes 2..600: rounds', rounds, 'agree', agree, 'missed', missed.length, 'flagged', JSON.stringify(flagged));
// random small round starts
let seed = 12345; const rnd = k => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed % k; };
let tries = 0, valid = 0; agree = 0; rounds = 0; flagged = {}; const missed0 = missed.length;
while (valid < 5000) {
  tries++;
  const W = BigInt(20 + rnd(380)); const k = 1 + rnd(4); const marks = [{ t: 'G', p: 1n }];
  const ps = new Set(); for (let i = 0; i < k; i++) ps.add(5 + rnd(Number(W) - 8));
  const types = 'MWB';
  for (const p of [...ps].sort((a, b) => a - b)) marks.push({ t: types[rnd(3)], p: BigInt(p) });
  if (rnd(2)) marks.push({ t: 'M', p: W - 2n });
  marks.sort(E.byPos);
  if (E.checkTape(W, marks).length) continue;
  valid++;
  runCase(W, marks, 25, "rand"); if (valid % 2000 === 0) console.log(valid, rounds, agree, missed.length, JSON.stringify(flagged));
}
console.log('random: tries', tries, 'valid', valid, 'rounds', rounds, 'agree', agree, 'missed', missed.length - missed0, 'flagged', JSON.stringify(flagged));
for (const m of missed.slice(missed0, missed0 + 12)) console.log(JSON.stringify(m));
