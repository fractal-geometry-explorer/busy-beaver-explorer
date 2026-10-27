// unit test of pincand's lattice solving: random affine forms, compare with brute force
const mod = (x, m) => ((x % m) + m) % m;
function egcd(x, y) { let [r0, r1, s0, s1, t0, t1] = [x, y, 1n, 0n, 0n, 1n]; while (r1 !== 0n) { const q = r0 / r1; [r0, r1] = [r1, r0 - q * r1]; [s0, s1] = [s1, s0 - q * s1]; [t0, t1] = [t1, t0 - q * t1]; } if (r0 < 0n) { r0 = -r0; s0 = -s0; t0 = -t0; } return [r0, s0, t0]; }
let seed = 3; const rnd = n => { seed = (seed * 1103515245 + 12345) % 2147483648; return BigInt(seed % n); };
let bad = 0;
for (let trial = 0; trial < 300; trial++) {
  const x0m = rnd(8), x0E = rnd(16) + 20n, B00 = 2n + rnd(6), B10 = rnd(9), B11 = 2n + rnd(10);
  const R = [rnd(50), 1n + rnd(9), 1n + rnd(9)], L = [rnd(400) - 200n, rnd(300) - 150n, rnd(300) - 150n];
  const CL = [[2n + 2n * rnd(20), rnd(7), 7n + 7n * rnd(4)], [4n + 2n * rnd(20), rnd(14), 14n]];
  const pt = (y0, y1) => [x0m + B00 * y0, x0E + B10 * y0 + B11 * y1];
  const Elo = 64n, Ehi = 4096n; const P = 2n;
  // brute
  const seen = new Set();
  for (let y0 = -400n; y0 <= 400n; y0++) for (let y1 = -800n; y1 <= 800n; y1++) {
    const [m, E] = pt(y0, y1); if (E < Elo || E >= Ehi || m <= 0n || m >= E - 2n) continue;
    const R1 = R[0] + R[1] * y0 + R[2] * y1, L1 = L[0] + L[1] * y0 + L[2] * y1;
    for (const [r, cls, M] of CL) for (let p = 0n; p < P; p++) if (R1 === 16n ** p * r && mod(L1, 64n ** p * M) === mod(64n ** p * cls, 64n ** p * M)) seen.add(m + ',' + E + ',' + p + ',' + r);
  }
  // solver (same steps as pincand.js)
  const got = new Set();
  for (let p = 0n; p < P; p++) for (const [r, cls, M] of CL) {
    const target = 16n ** p * r; const [g, s, t] = egcd(R[1], R[2]); const rhs = target - R[0];
    if (g === 0n || rhs % g !== 0n) continue;
    const Y0 = s * (rhs / g), Y1 = t * (rhs / g), d0 = R[2] / g, d1 = -R[1] / g;
    const Ec = x0E + B10 * Y0 + B11 * Y1, Ed = B10 * d0 + B11 * d1;
    let ulo, uhi;
      if (Ed !== 0n) { ulo = (Elo - Ec) / Ed; uhi = (Ehi - Ec) / Ed; }
      else {   // E is constant on this line: bound u by 0 < m < E instead
        if (Ec < Elo || Ec >= Ehi) continue;
        const Mc = x0m + B00 * Y0, Md = B00 * d0; if (Md === 0n) continue;
        ulo = (0n - Mc) / Md; uhi = (Ec - Mc) / Md; }
      if (ulo > uhi) [ulo, uhi] = [uhi, ulo]; ulo -= 2n; uhi += 2n;
    const Lc = L[0] + L[1] * Y0 + L[2] * Y1, Ld = L[1] * d0 + L[2] * d1;
    const Mod = 64n ** p * M, want = mod(64n ** p * cls - Lc, Mod);
    const [h, sh] = egcd(mod(Ld, Mod), Mod); if (want % h !== 0n) continue;
    const step = Mod / h, u0 = mod((want / h) * sh, step);
    for (let u = ulo + mod(u0 - ulo, step); u <= uhi; u += step) {
      const [m, E] = pt(Y0 + u * d0, Y1 + u * d1); if (E < Elo || E >= Ehi || m <= 0n || m >= E - 2n) continue;
      const y0 = Y0 + u * d0, y1 = Y1 + u * d1; const R1 = R[0] + R[1] * y0 + R[2] * y1, L1 = L[0] + L[1] * y0 + L[2] * y1;
      if (R1 !== target || mod(L1, Mod) !== mod(64n ** p * cls, Mod)) { console.log('UNSOUND point'); }
      got.add(m + ',' + E + ',' + p + ',' + r);
    }
  }
  const missing = [...seen].filter(x => !got.has(x));
  if (missing.length) { bad++; if (bad < 4) console.log('missing', trial, missing, 'R', R.map(String), 'L', L.map(String), 'B', [x0m, x0E, B00, B10, B11].map(String), 'CL', JSON.stringify(CL.map(c => c.map(String)))); }
  else if (trial < 5) console.log('trial', trial, 'agree on', seen.size, 'points');
}
console.log('mismatches:', bad, 'of 300');
