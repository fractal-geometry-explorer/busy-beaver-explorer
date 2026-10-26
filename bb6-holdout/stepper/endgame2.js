// From a loop pass start G1 W a W b W c (end E, R = E - c - 1), how large can R be and the run still reach the end
// (d <= 2 at a meeting with the end marker) without starting another pass?
const E_ = require('./engine.js');
let seed = 5 >>> 0; const rnd = () => { seed = (seed + 0x6D2B79F5) >>> 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
const big = k => { let x = 0n; for (let i = 0; i < k; i += 30) x = (x << 30n) | BigInt(Math.floor(rnd() * 2 ** 30)); return x; };
const Rs = []; for (let R = 8; R <= 1024; R += 8) Rs.push(R);
const TR = +process.argv[2] || 3000;
const res = [];
for (const R of Rs) {
  let close = 0, pass = 0, other = 0, maxMeet = 0;
  for (let t = 0; t < TR; t++) {
    let E = (1n << 40n) + big(40); if (E % 2n) E += 1n;
    const c = E - BigInt(R) - 1n;
    let b = E / 2n + big(36); if (b % 2n) b += 1n; if (b >= c - 10n) b = c - 12n;
    let a = big(36) + 11n; if (a % 2n === 0n) a += 1n; if (a >= b - 10n) a = b - 11n;
    const marks = [{ t: 'G', p: 1n }, { t: 'W', p: a }, { t: 'W', p: b }, { t: 'W', p: c }];
    if (E_.checkTape(E, marks).length) { other++; continue; }
    let st = { W: E, marks, lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity };
    const shapes = []; let outcome = 'ends', meets = 0;
    for (let r = 0; r < 40; r++) {
      const nx = E_.doRound(st, {});
      meets += nx.meets.length;
      if (nx.stop) { outcome = nx.stop.k === 'close' ? 'close' : 'stop:' + nx.stop.k; break; }
      const sh = nx.marks.map(m => m.t).join(''); shapes.push(sh);
      const L = shapes.length;
      if (L >= 3 && shapes[L - 3] === 'GWWW' && shapes[L - 2] === 'GBW' && shapes[L - 1] === 'GMB') { outcome = 'pass'; break; }
      st = nx;
      if (nx.marks.length === 3 && nx.marks[2].t === 'M' && nx.marks[1].t === 'M' && nx.marks[2].p === nx.W - 2n) break; // two-marker state: segment over
    }
    if (outcome === 'close') { close++; if (meets > maxMeet) maxMeet = meets; } else if (outcome === 'pass') pass++; else other++;
  }
  res.push([R, close, pass, other, maxMeet]);
}
for (const r of res) if (r[1]) console.log('R ' + r[0] + ': reaches the end ' + r[1] + ', starts another pass ' + r[2] + ', other ' + r[3] + ', most meetings before the end ' + r[4]);
const mx = res.filter(r => r[1] > 0).map(r => r[0]); console.log('largest R that reaches the end:', Math.max(...mx));
