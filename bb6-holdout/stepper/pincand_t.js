// Exact candidates for a route whose plain entry has a high sigma ceiling (October 23).
// A GMM route is a coset m = x0m + B00*y0, E = x0E + B10*y0 + B11*y1. At its first phase-0 plain entry R1 and L1 are
// affine in (y0, y1); read them off three integer points on the stepper engine. A halt through that entry needs, for
// some p, R1 = 16^p * r with r in the close set and L1 / 64^p in r's class (endsym.py / endL.py). For every width octave
// 2^k with kmin <= k <= kmax this lists the (m, E) in the coset that meet both, and runs each on the engine.
// usage: node pincand.js x0m x0E B00 B10 B11 kmin kmax
const E_ = require('./engine.js');
const a = process.argv.slice(2);
const [x0m, x0E, B00, B10, B11] = a.slice(0, 5).map(BigInt); const kmin = +a[5], kmax = +a[6];
const CLOSE = process.env.TESTCLOSE ? JSON.parse(process.env.TESTCLOSE).map(r => r.map(BigInt)) : [[2n, 10n, 14n], [4n, 10n, 14n], [8n, 24n, 56n], [16n, 192n, 224n], [24n, 416n, 448n], [32n, 192n, 448n], [48n, 640n, 896n], [64n, 640n, 896n], [176n, 640n, 896n]];
const mod = (x, m) => ((x % m) + m) % m;
function entry(m, E, maxr) {
  let st = { W: E, marks: [{ t: 'G', p: 1n }, { t: 'M', p: m }, { t: 'M', p: E - 2n }], lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity };
  const hist = [], states = [];
  for (let r = 0; r < (maxr || 400); r++) {
    const nx = E_.doRound(st, {});
    if (nx.stop) return { stop: nx.stop.k, hist };
    const sh = nx.marks.map(q => q.t).join(''); hist.push(sh); states.push(nx);
    const L = hist.length;
    if (L >= 3 && hist[L - 3] === 'GWWW' && hist[L - 2] === 'GBW' && hist[L - 1] === 'GMB') {
      const s0 = states[L - 3], ms = s0.marks;
      return { R1: s0.W - ms[3].p - 1n, L1: 147n * ms[2].p + 280n * s0.W - 392n * ms[3].p - 578n, W: s0.W, hist: hist.slice(0, L - 2).join(' '), rounds: L - 2 };
    }
    st = nx;
  }
  return { stop: 'no entry', hist };
}
// run a GMM state through its whole segment: does any end meeting come within 2 cells (close) or a packet hit a block?
function follow(m, E) {
  let st = { W: E, marks: [{ t: 'G', p: 1n }, { t: 'M', p: m }, { t: 'M', p: E - 2n }], lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity };
  for (let r = 0; r < 4000; r++) {
    const nx = E_.doRound(st, {});
    if (nx.stop) return { end: nx.stop.k, best: nx.best };
    const ms = nx.marks; if (ms.length === 3 && ms[1].t === 'M' && ms[2].t === 'M' && ms[2].p === nx.W - 2n && r > 0) return { end: 'segment ends (GMM)', best: nx.best };
    if (ms.length === 2 && ms[1].t === 'M' && ms[1].p === nx.W - 2n) return { end: 'clean tape', best: nx.best };
    st = nx;
  }
  return { end: 'round limit', best: st.best };
}
// three points far out (y chosen for E near 2^200 and m/E near 1/2) give the affine forms in (y0, y1)
const big = 2n ** 200n;
const y0b = (big / 2n - x0m) / B00, y1b = (big - x0E - B10 * y0b) / B11;
const pt = (y0, y1) => [x0m + B00 * y0, x0E + B10 * y0 + B11 * y1];
const e0 = entry(...pt(y0b, y1b)), e1 = entry(...pt(y0b + 1n, y1b)), e2 = entry(...pt(y0b, y1b + 1n));
if (!e0.R1 || !e1.R1 || !e2.R1 || e0.hist !== e1.hist || e0.hist !== e2.hist) { console.log('route not followed at the probe points'); process.exit(1); }
const R = [e0.R1 - (e1.R1 - e0.R1) * y0b - (e2.R1 - e0.R1) * y1b, e1.R1 - e0.R1, e2.R1 - e0.R1];
const Lf = [e0.L1 - (e1.L1 - e0.L1) * y0b - (e2.L1 - e0.L1) * y1b, e1.L1 - e0.L1, e2.L1 - e0.L1];
console.log('route (' + e0.rounds + ' rounds to the entry): ' + e0.hist);
console.log('R1 = ' + R[0] + ' + ' + R[1] + '*y0 + ' + R[2] + '*y1;  L1 = ' + Lf[0] + ' + ' + Lf[1] + '*y0 + ' + Lf[2] + '*y1');
function egcd(x, y) { let [r0, r1, s0, s1, t0, t1] = [x, y, 1n, 0n, 0n, 1n]; while (r1 !== 0n) { const q = r0 / r1; [r0, r1] = [r1, r0 - q * r1]; [s0, s1] = [s1, s0 - q * s1]; [t0, t1] = [t1, t0 - q * t1]; } if (r0 < 0n) { r0 = -r0; s0 = -s0; t0 = -t0; } return [r0, s0, t0]; }
let total = 0, ran = 0, halts = 0, rhits = 0;
for (let k = kmin; k <= kmax; k++) {
  const Elo = 2n ** BigInt(k), Ehi = 2n ** BigInt(k + 1);
  let nk = 0;
  for (let p = 0n; p < 80n; p++) {
    for (const [r, cls, M] of CLOSE) {
      const target = 16n ** p * r;
      // R1 = target: R[1] y0 + R[2] y1 = target - R[0]
      const [g, s, t] = egcd(R[1], R[2]); const rhs = target - R[0];
      if (g === 0n || rhs % g !== 0n) continue;
      const Y0 = s * (rhs / g), Y1 = t * (rhs / g), d0 = R[2] / g, d1 = -R[1] / g;   // (y0, y1) = (Y0, Y1) + u (d0, d1)
      // E = x0E + B10 y0 + B11 y1 is affine in u: range of u for E in [Elo, Ehi)
      const Ec = x0E + B10 * Y0 + B11 * Y1, Ed = B10 * d0 + B11 * d1;
      if (Ed === 0n) continue;
      let ulo = (Elo - Ec) / Ed, uhi = (Ehi - Ec) / Ed; if (ulo > uhi) [ulo, uhi] = [uhi, ulo]; ulo -= 2n; uhi += 2n;
      // L1(u) = Lc + Ld u must be 64^p * (cls mod M): L1 = 64^p * cls (mod 64^p * M)
      for (let uu = ulo; uu <= uhi; uu++) { const [mm2, EE2] = pt(Y0 + uu * d0, Y1 + uu * d1); if (EE2 >= Elo && EE2 < Ehi && mm2 > 0n && mm2 < EE2 - 2n) rhits++; if (uhi - ulo > 100000n) break; }
      const Lc = Lf[0] + Lf[1] * Y0 + Lf[2] * Y1, Ld = Lf[1] * d0 + Lf[2] * d1;
      const Mod = 64n ** p * M, want = mod(64n ** p * cls - Lc, Mod);
      const [h, sh] = egcd(mod(Ld, Mod), Mod);
      if (want % h !== 0n) continue;
      const step = Mod / h, u0 = mod((want / h) * sh, step);
      let u = ulo + mod(u0 - ulo, step);
      for (; u <= uhi; u += step) {
        const y0 = Y0 + u * d0, y1 = Y1 + u * d1; const [m, E] = pt(y0, y1);
        if (E < Elo || E >= Ehi || m <= 0n || m >= E - 2n) continue;
        nk++; total++;
        if (ran < 200) { ran++; const res = follow(m, E); if (res.end === 'close' || res.end === 'halt') halts++;
          console.log('  candidate k=' + k + ' p=' + p + ' r=' + r + ': m=' + m + ' E=' + E + ' -> ' + res.end + ', closest ' + res.best.toFixed(2) + ' halvings'); }
      }
    }
  }
  console.log('width 2^' + k + ': ' + nk + ' candidates');
}
console.log('points with R1 = 16^p r (any L1): ' + rhits); console.log('total candidates ' + total + ', run ' + ran + ', reaching the end ' + halts);
