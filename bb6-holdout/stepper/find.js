const E = require('./engine.js');
const init = (W, marks) => ({ W, marks, lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity });
let seed = 99 >>> 0; const rnd = k => { seed = (seed + 0x6D2B79F5) >>> 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return (((t ^ (t >>> 14)) >>> 0) % k); };
const seen = {};
for (let c = 0; c < 400000 && Object.keys(seen).length < 12; c++) {
  const marks = [{ t: 'G', p: 1n }]; let p = 4 + rnd(10); const k = 1 + rnd(5);
  for (let i = 0; i < k; i++) { const t = 'MWB'[rnd(3)]; marks.push({ t, p: BigInt(p) }); p += Number(E.LEN[t]) + rnd(9); }
  let W = BigInt(p + rnd(8)); marks.push({ t: 'M', p: W }); W += 2n;
  if (E.checkTape(W, marks).length) continue;
  let st = init(W, marks);
  for (let r = 0; r < 30; r++) { const nx = E.doRound(st, {}); if (nx.stop) { const key = nx.stop.k + ':' + nx.stop.text.replace(/[0-9,.×⁰-⁹]+/g, '#').slice(0, 70);
      if (!seen[key]) { const tm = E.realRound(st.W, st.marks, 1e7); seen[key] = { start: marks.map(m => m.t + m.p).join(' ') + ' width ' + W, round: r, tm: tm.halted ? 'halts after ' + tm.steps : tm.timeout ? 'timeout' : 'continues' }; } break; } st = nx; }
}
for (const [k, v] of Object.entries(seen)) console.log(k, '|', JSON.stringify(v));
