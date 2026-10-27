/* Driver for the stepper page's engine (../stepper/engine.js), same line formats as Oracle.lean.
   usage: node stepper.js NR [machine] < starts       with "machine": the bare transition table (realRound) instead
   of the mark rules, for tapes up to a few hundred cells; any configuration the engine stops at is U. */
'use strict';
const E = require('../stepper/engine.js');
const NR = Number(process.argv[2] || 8), bare = process.argv[3] === 'machine';
const out = [];
for (const line of require('fs').readFileSync(0, 'utf8').split('\n')) {
  const w = line.trim().split(/\s+/); if (!w[0]) continue;
  let W = BigInt(w[0]); let marks = [{ t: 'G', p: 1n }];
  for (let i = 1; i < w.length; i += 2) marks.push({ t: w[i], p: BigInt(w[i + 1]) });
  let st = { W, marks, lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity }, end = 'E';
  for (let r = 0; r < NR; r++) {
    if (bare) {
      if (W > 4000n) { end = 'U'; break; }
      const res = E.realRound(W, marks, 5e7);
      if (res.halted) { end = 'H'; break; }
      if (res.timeout || res.marks.some(m => !'GMWB'.includes(m.t))) { end = 'U'; break; }
      W = res.W; marks = res.marks;
    } else {
      const res = E.doRound(st, {});
      if (res.stop) { end = res.stop.k === 'halt' ? 'H' : 'U'; break; }
      st = res; W = res.W; marks = res.marks;
    }
    if (!marks.length || marks[0].t !== 'G' || marks[0].p !== 1n) { end = 'U'; break; }
    out.push(['R', W, ...marks.slice(1).flatMap(m => [m.t, m.p])].join(' '));
  }
  out.push(end, '.');
}
process.stdout.write(out.join('\n') + '\n');
