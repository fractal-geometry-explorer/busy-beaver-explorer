// Node test of pair.js's engine against the numbers of verify/Eqv_TailWord.v (coq/) and lean/RightEnd.lean.
// usage: node test_pair.js [tm steps]
const E = require("./pair.js"), assert = require("assert");
const N = +(process.argv[2] || 2e6);
// 1. the second table is the first, renamed by g and mirrored
const T1 = E.parse(E.TM), T2 = E.parse(E.TP);
for (let s = 0; s < 6; s++) for (let r = 0; r < 2; r++) {
  const a = T1[2 * s + r], b = T2[2 * E.G[s] + r];
  if (!a) { assert(!b); continue; }
  assert(b.w === a.w && b.d === -a.d && b.q === E.G[a.q]);
}
// 2. after 2 and 49 steps the runs agree; then in lockstep, abstract window always in the closure
const P = new E.Pair();
assert.strictEqual(P.agree(), null);
const C = E.closure(T1);
assert.strictEqual(C.order.length, 28); assert(!C.bad);
const keys = new Set(C.order.map(E.key));
let crossings = 0;
while (P.a.n < N) {
  const before = [P.a.n, P.b.n], r = P.step();
  assert(r === "step" || r === "cross", r + " " + P.bad);
  if (r === "cross") { crossings++; assert.deepStrictEqual([P.a.n - before[0], P.b.n - before[1]], [5, 49]); }
  assert(keys.has(E.key(E.absOf(P.a))), "window outside the list at step " + P.a.n);
  if (r === "cross" || P.m % 997 === 0) assert.strictEqual(P.agree(), null, "at model step " + P.m);
}
// 3. the far end with k words takes 44k + 5 steps
const Q = new E.Pair(); while (Q.cross < 2 || !Q.crossingNow()) Q.step();
const q0 = Q.a.hi;
for (let k = 0; k <= 4; k++) {
  const s = Q.a.clone();
  for (let j = 0; j < k; j++) E.W8.forEach((v, i) => s.set(q0 + 1 + 8 * j + i, v));
  let n = 0; do { s.step(); n++; } while (!(s.q === 3 && s.h === q0 - 1));
  assert.strictEqual(n, 44 * k + 5, "k=" + k);
  assert.deepStrictEqual([s.get(q0), s.get(q0 + 1), s.get(q0 + 2)], [1, 0, 1]);
  for (let j = 0; j < k; j++) E.W8.forEach((v, i) => assert.strictEqual(s.get(q0 + 3 + 8 * j + i), v));
}
console.log(`ok: tables, ${crossings} crossings (5 and 49 steps) in ${P.a.n} steps, 28 window configurations, far end 44k+5 for k=0..4`);
