// Random pass-start states at a fixed R on the stepper's engine: how often the run closes, and the left countdown
// L = 147b - 112E + 392R - 186 at the closing states.
const E_ = require('./engine.js');
let seed = 11 >>> 0; const rnd = () => { seed = (seed + 0x6D2B79F5) >>> 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
const big = k => { let x = 0n; for (let i = 0; i < k; i += 30) x = (x << 30n) | BigInt(Math.floor(rnd() * 2 ** 30)); return x & ((1n << BigInt(k)) - 1n); };
const R = BigInt(process.argv[2]); const TR = +process.argv[3]; const MOD = BigInt(process.argv[4] || 896);
let close = 0, ph0 = 0; const Lres = {}; const outc = {};
for (let t = 0; t < TR; t++) {
  let E = (1n << 40n) + big(40); if (E % 2n) E += 1n;
  const c = E - R - 1n;
  let b = (E * 3n) / 4n + big(34); if (b % 2n) b += 1n;
  let a = big(36) + 11n; if (a % 2n === 0n) a += 1n;
  const marks = [{ t: 'G', p: 1n }, { t: 'W', p: a }, { t: 'W', p: b }, { t: 'W', p: c }];
  if (E_.checkTape(E, marks).length) { outc.invalid = (outc.invalid || 0) + 1; continue; }
  let st = { W: E, marks, lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity };
  const shapes = []; let out = 'limit';
  for (let r = 0; r < 60; r++) {
    const nx = E_.doRound(st, {});
    let brk = false;
    for (const m of nx.meets) if (m.chain === 1 && st.lastD !== null && m.d > 1000n) brk = true;
    if (nx.stop) { out = nx.stop.k; break; }
    if (brk) { out = 'break'; break; }
    const sh = nx.marks.map(m => m.t).join(''); shapes.push(sh);
    if (shapes.length === 1 && sh !== 'GBW' || shapes.length === 2 && sh !== 'GMB') { out = 'notphase0'; break; }
    const L = shapes.length;
    if (L >= 3 && shapes[L - 3] === 'GWWW' && shapes[L - 2] === 'GBW' && shapes[L - 1] === 'GMB') { out = 'pass'; break; }
    st = nx;
  }
  outc[out] = (outc[out] || 0) + 1;
  if (out === 'close') { const Lv = 147n * b - 112n * E + 392n * R - 186n; const k = ((Lv % MOD) + MOD) % MOD; Lres[k] = (Lres[k] || 0) + 1; }
}
console.log('R', String(R), 'trials', TR, JSON.stringify(outc), 'L mod', String(MOD), 'at closes:', JSON.stringify(Lres));
