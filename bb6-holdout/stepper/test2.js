const E = require('./engine.js');
const init = (W, marks) => ({ W, marks, lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity });
let agree = 0, missed = [], flagged = {}, rounds = 0, examples = {};
function runCase(W, marks, maxR) {
  let st = init(W, marks);
  for (let r = 0; r < maxR; r++) {
    const nx = E.doRound(st, {});
    const tm = E.realRound(st.W, st.marks, 2e7);
    rounds++;
    const tmSame = !tm.halted && !tm.timeout && tm.W === nx.W && E.sameMarks(tm.marks, nx.marks);
    if (nx.stop) { const k = nx.stop.k + (tm.halted ? '/halts' : tm.timeout ? '/timeout' : tmSame ? '/same' : '/differs'); flagged[k] = (flagged[k] || 0) + 1;
      if (!examples[k]) examples[k] = { start: marks.map(m => m.t + m.p).join(' ') + ' w' + W, round: r, at: st.marks.map(m => m.t + m.p).join(' ') + ' w' + st.W, why: nx.stop.text }; return; }
    if (tm.timeout) return;
    if (!tmSame) { missed.push({ r, W: String(st.W), marks: st.marks.map(m => m.t + m.p).join(' '), tm: tm.halted ? 'HALT after ' + tm.steps : tm.marks.map(m => m.t + m.p).join(' ') + ' w' + tm.W, model: nx.marks.map(m => m.t + m.p).join(' ') + ' w' + nx.W }); return; }
    agree++; st = nx;
  }
}
let seed = (+process.argv[2] || 777) >>> 0; const rnd = k => { seed = (seed + 0x6D2B79F5) >>> 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return (((t ^ (t >>> 14)) >>> 0) % k); };
let valid = 0, tries = 0; const NV = +process.argv[3] || 20000;
while (valid < NV) {
  tries++;
  const marks = [{ t: 'G', p: 1n }]; let p = 4 + rnd(6); const k = 1 + rnd(5);
  for (let i = 0; i < k; i++) { const t = 'MWB'[rnd(3)]; marks.push({ t, p: BigInt(p) }); p += Number(E.LEN[t]) + rnd(7); }
  let W = BigInt(p + rnd(8));
  if (rnd(2)) { marks.push({ t: 'M', p: W }); W += 2n; }
  if (E.checkTape(W, marks).length) continue;
  valid++; runCase(W, marks, 30);
}
console.log('close-mark tapes: tries', tries, 'valid', valid, 'rounds', rounds, 'agree', agree, 'missed', missed.length);
console.log(JSON.stringify(flagged));
for (const [k, v] of Object.entries(examples)) console.log(k, JSON.stringify(v));
for (const m of missed.slice(0, 15)) console.log('MISSED', JSON.stringify(m));
