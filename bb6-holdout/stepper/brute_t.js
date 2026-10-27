// brute-force check of the pinning conditions on the main-route coset (forms read off by pincand.js)
const CLOSE = process.env.TESTCLOSE ? JSON.parse(process.env.TESTCLOSE).map(r => r.map(BigInt)) : [[2n, 10n, 14n], [4n, 10n, 14n], [8n, 24n, 56n], [16n, 192n, 224n], [24n, 416n, 448n], [32n, 192n, 448n], [48n, 640n, 896n], [64n, 640n, 896n], [176n, 640n, 896n]];
const mod = (x, m) => ((x % m) + m) % m;
let n = 0, nR = 0, nRv = 0;
for (let y1 = -4200n; y1 <= 512n; y1++) for (let y0 = 0n; y0 < 16384n; y0++) {
  const m = 64n + 128n * y0, E = 777n + 1088n * y0 + 4096n * y1;
  if (E < 4096n || E >= 1n << 21n || m >= E - 2n) continue;
  const R1 = 192n + 256n * y0 + 968n * y1, L1 = 23824n + 32004n * y0 + 121212n * y1;
  for (const [r, cls, M] of CLOSE) for (let p = 0n; p < 8n; p++) {
    if (R1 !== 16n ** p * r) continue;
    nR++;
    if (mod(L1, 64n ** p) === 0n) nRv++;
    if (mod(L1, 64n ** p * M) === mod(64n ** p * cls, 64n ** p * M)) { n++; }
  }
}
console.log('points with R1 = 16^p r:', nR, '; and 64^p | L1:', nRv, '; full condition:', n);
