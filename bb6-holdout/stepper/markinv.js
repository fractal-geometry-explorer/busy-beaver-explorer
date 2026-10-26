// Search for conserved quantities of the MARK model: functions of a round-start state
//   F = sum over marks of w(type, feature) + v1*W + v2*W^2 + const   (mod k, or over the rationals)
// with features: count, position x, x^2, x*(rank from the left), and whether the mark is the last one.
// Random valid round-start tapes are run for one round on the engine; F(before) = F(after) gives linear equations in
// the weights; the kernel modulo each k is printed after removing the trivial constant.
const E_ = require('./engine.js');
let seed = 17 >>> 0; const rnd = () => { seed = (seed + 0x6D2B79F5) >>> 0; let t = seed; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
const TYPES = ['G', 'M', 'W', 'B'];
const FEATS = ['count', 'x', 'x2', 'xrank', 'last'];
const names = []; const index = {};
for (const t of TYPES) for (const f of FEATS) { index[t + ':' + f] = names.length; names.push(t + ':' + f); }
for (const a of TYPES) for (const b of TYPES) { index['gap:' + a + b] = names.length; names.push('gap:' + a + b); index['gap2:' + a + b] = names.length; names.push('gap2:' + a + b); }
index['tailgap'] = names.length; names.push('tailgap');
index['W1'] = names.length; names.push('W1'); index['W2'] = names.length; names.push('W2'); index['const'] = names.length; names.push('const');
const NU = names.length;
function feats(W, marks) {
  const v = new Array(NU).fill(0n); const ms = marks.slice().sort(E_.byPos);
  ms.forEach((m, i) => {
    const b = index[m.t + ':'];
    v[index[m.t + ':count']] += 1n; v[index[m.t + ':x']] += m.p; v[index[m.t + ':x2']] += m.p * m.p; v[index[m.t + ':xrank']] += m.p * BigInt(i);
    if (i === ms.length - 1) v[index[m.t + ':last']] += 1n;
  });
  for (let i = 0; i + 1 < ms.length; i++) { const d = ms[i + 1].p - ms[i].p - E_.LEN[ms[i].t]; const key = ms[i].t + ms[i + 1].t; v[index['gap:' + key]] += d; v[index['gap2:' + key]] += d * d; }
  v[index['tailgap']] = W - ms[ms.length - 1].p - E_.LEN[ms[ms.length - 1].t];
  v[index['W1']] = W; v[index['W2']] = W * W; v[index['const']] = 1n; return v;
}
// random valid round-start state: gap at 1, then a random sequence of marks with random stripe lengths of the right parity
function randomState() {
  const marks = [{ t: 'G', p: 1n }]; let pos = 4n; const n = 1 + Math.floor(rnd() * 5);
  let prevVal = 0;   // the gap's cells are 0
  for (let i = 0; i < n; i++) {
    const t = TYPES[Math.floor(rnd() * 4)]; const val = E_.VAL[t];
    let L = 1n + 2n * BigInt(5 + Math.floor(rnd() * 400));        // odd length when the values are equal
    if (val !== prevVal) L += 1n;                                  // even length when they differ
    const p = pos + L; marks.push({ t, p }); pos = p + E_.LEN[t]; prevVal = val;
  }
  // the end marker: a marker at W - 2 so that the tape ends on a 1
  let L = 1n + 2n * BigInt(5 + Math.floor(rnd() * 400)); if (prevVal !== 1) L += 1n;
  const pe = pos + L; marks.push({ t: 'M', p: pe }); const W = pe + 2n;
  return { W, marks };
}
const eqs = [];
let tried = 0, used = 0;
while (used < 12000 && tried < 120000) {
  tried++;
  const s = randomState();
  if (E_.checkTape(s.W, s.marks).length) continue;
  const st = { W: s.W, marks: s.marks, lastD: null, lastKind: null, chain: 0, maxChain: 0, best: -Infinity };
  const nx = E_.doRound(st, {});
  if (nx.stop) continue;                 // a close or an uncovered case: skip
  if (E_.checkTape(nx.W, nx.marks).length) continue;
  const a = feats(s.W, s.marks), b = feats(nx.W, nx.marks);
  eqs.push(a.map((x, i) => b[i] - x)); used++;
}
console.log('transitions used', used, 'of', tried, 'random states; unknowns', NU);
const mod = (x, k) => ((x % k) + k) % k;
function kernelMod(rows, k) {
  const K = BigInt(k); const A = rows.map(r => r.map(x => mod(x, K))); const m = A.length, n = NU; const piv = []; let r = 0;
  const inv = x => { let [g, s0, s1, a, b] = [0n, 1n, 0n, mod(x, K), K]; let [t0, t1] = [0n, 1n]; while (b) { const q = a / b; [a, b] = [b, a - q * b]; [s0, t0] = [t0, s0 - q * t0]; } return mod(s0, K); };
  for (let c = 0; c < n && r < m; c++) {
    let pr = -1; for (let i = r; i < m; i++) if (A[i][c] % K) { pr = i; break; }
    if (pr < 0) continue;
    [A[r], A[pr]] = [A[pr], A[r]]; const iv = inv(A[r][c]); A[r] = A[r].map(x => mod(x * iv, K));
    for (let i = 0; i < m; i++) if (i !== r && A[i][c]) { const f = A[i][c]; A[i] = A[i].map((x, j) => mod(x - f * A[r][j], K)); }
    piv.push(c); r++;
  }
  const free = []; for (let c = 0; c < n; c++) if (!piv.includes(c)) free.push(c);
  return free.map(fc => { const w = new Array(n).fill(0n); w[fc] = 1n; piv.forEach((pc, i) => { w[pc] = mod(-A[i][fc], K); }); return w; });
}
for (const k of [3, 5, 7, 9, 11, 13, 21, 63, 2, 4, 8, 16, 1000003]) {
  const ker = kernelMod(eqs, k);
  // drop the pure constant
  const nontriv = ker.filter(w => w.some((x, i) => x !== 0n && names[i] !== 'const'));
  console.log('mod ' + k + ': kernel dimension ' + ker.length + ', nontrivial ' + nontriv.length);
  for (const w of nontriv.slice(0, 12)) console.log('   ' + w.map((x, i) => x !== 0n ? names[i] + ':' + x : null).filter(Boolean).join('  '));
}
