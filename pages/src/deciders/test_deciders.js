// Tests of the deciders page: the built page is current, the engine reproduces the papers' examples, and it
// re-decides the certificates and parameters that Coq-BB5 hardcodes (all FAR and WFAR, samples of n-gram CPS
// and RepWL, all long halters except the champion, which is checked separately).
// usage: node pages/src/deciders/test_deciders.js [--full]   (--full runs every n-gram CPS and RepWL case, ~80 s)
"use strict";
const assert = require("assert");
const path = require("path");
const fs = require("fs");
const { execFileSync } = require("child_process");
const HERE = __dirname;
const BB = require(path.join(HERE, "engine.js"));
const DATA = JSON.parse(fs.readFileSync(path.join(HERE, "data", "coq_hardcoded.json"), "utf8"));
const FULL = process.argv.includes("--full");
let failed = 0;
function test(name, fn) {
  const t0 = Date.now();
  try { fn(); console.log(`ok   ${name} (${Date.now() - t0} ms)`); } catch (e) { failed++; console.log(`FAIL ${name}\n     ${e.message}`); }
}
function sample(list, k, seed = 1) {
  if (FULL || list.length <= k) return list;
  let x = seed; const out = [], idx = new Set();
  while (idx.size < k) { x = (x * 1103515245 + 12345) % 2147483648; idx.add(x % list.length); }
  for (const i of idx) out.push(list[i]);
  return out;
}

test("built page is current", () => {
  execFileSync("python3", [path.join(HERE, "build.py"), "--check"], { stdio: "pipe" });
});
test("data counts match Coq-BB5", () => {
  assert.deepStrictEqual([DATA.halt.length, DATA.loop.length, DATA.ngram.length, DATA.repwl.length, DATA.far.length, DATA.wfar.length], [183, 2, 1413, 6577, 23, 17]);
});
test("parse and format round trip", () => {
  for (const t of ["1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA", "0RB---_0LC0RA_1RD1LC_1RB0LE_1LD0LE"]) assert.strictEqual(BB.format(BB.parse(t)), t);
});
test("champion halts after 47,176,870 steps with 4,098 ones", () => {
  const r = new BB.Run(BB.parse("1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA"));
  r.run(50000000);
  assert.ok(r.halted);
  assert.strictEqual(r.steps + 1, 47176870);
  assert.strictEqual(r.ones() + 1, 4098);
});
test("long halters halt (all 183 but the champion)", () => {
  for (const m of DATA.halt) {
    if (m === "1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA") continue;
    const r = new BB.Run(BB.parse(m)); r.run(47176870);
    assert.ok(r.halted, m);
  }
});
test("loops: the paper's cycler and translated cycler, the two L = 1,050,000 machines", () => {
  let x = BB.loops(BB.parse("1RB---_0RC0LE_1LD0LA_1LB1RB_1LC1RC"), 130);
  assert.strictEqual(x.result, "nonhalt"); assert.strictEqual(x.kind, "cycler"); assert.strictEqual(x.period, 4);
  for (const m of DATA.loop) {
    x = BB.loops(BB.parse(m), 1050000);
    assert.strictEqual(x.result, "nonhalt", m); assert.strictEqual(x.period, 91995, m);
  }
  assert.strictEqual(BB.loops(BB.parse("1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA"), 4100).result, "unknown");
});
test("n-gram CPS: README example, and the hardcoded parameters (sample)", () => {
  const x = BB.ngramCPS(BB.parse("1RB---_0LC0RB_1RD1LD_0LE0RA_0RC0RA"), 2, { mode: "plain" });
  assert.strictEqual(x.result, "nonhalt");
  for (const [m, mode, k, len] of sample(DATA.ngram, 150)) {
    const r = BB.ngramCPS(BB.parse(m), len, mode === "lru" ? { mode: "lru" } : k ? { mode: "hist", k } : { mode: "plain" });
    assert.strictEqual(r.result, "nonhalt", `${m} ${mode} ${k} ${len}`);
  }
});
test("RepWL (paper rules): the figures' node counts", () => {
  const cases = [["0RB0LC_1LA1RB_1RD0RE_1LC1LA_---0LD", 2, 3, 11], ["1RB0RD_0LC0LA_0LD1LC_1RA0LE_0RC---", 5, 2, 42],
    ["1RB---_1LB1RC_1RA1RD_1LE0RD_0LB0LC", 2, 3, 845], ["1RB---_0RC1RD_0LD1RC_1LE0RA_1RA0LE", 20, 2, 143181],
    ["1RB1LA_1LA0RC_1LD1RC_---0LA", 4, 3, 3130]];
  for (const [m, l, T, n] of cases) {
    const x = BB.repWLPaper(BB.parse(m), l, T);
    assert.strictEqual(x.result, "nonhalt", m); assert.strictEqual(x.nodes, n, m);
  }
});
test("RepWL (Coq rules): the hardcoded parameters (sample, plus the l = 28 case)", () => {
  const list = sample(DATA.repwl, 400).concat([["0RB---_0LC0RA_1RD1LC_1RB0LE_1LD0LE", 28, 3]]);
  for (const [m, l, T] of list) assert.strictEqual(BB.repWL(BB.parse(m), l, T).result, "nonhalt", `${m} ${l} ${T}`);
});
test("FAR: the paper's NFA and all 23 certificates", () => {
  const m = BB.parse("1RB0LD_1LC1RA_0RB0LC_---1LA"), x = BB.farNFA(m, [[0, 1], [0, 0]]);
  assert.strictEqual(x.result, "nonhalt");
  assert.ok(BB.farAccepts(m, [[0, 1], [0, 0]], x, "0110", 3, "1").mayHalt === false);
  for (const [t, , dfa] of DATA.far) assert.strictEqual(BB.farNFA(BB.parse(t), dfa).result, "nonhalt", t);
});
test("WFAR: the paper's 54-element closed set and all 17 certificates", () => {
  const [t0, d0, , wl0, , wr0] = DATA.wfar[0];
  assert.strictEqual(BB.wfar(BB.parse(t0), d0, wl0, wr0).set.length, 54);
  for (const [t, d, , wl, , wr] of DATA.wfar) assert.strictEqual(BB.wfar(BB.parse(t), d, wl, wr).result, "nonhalt", t);
});
test("1RB reduction gives Finned #3", () => {
  assert.strictEqual(BB.reduce1RB(BB.parse("0RB0LD_1RC1RE_1LA1RC_1LC1LD_---0RB")).machine.text, "1RB1RE_1LC1RB_0RA0LD_1LB1LD_---0RA");
});
test("earlier deciders: backward reasoning, halting segment, bouncer formula", () => {
  assert.strictEqual(BB.backward(BB.parse("1RB0LD_1LC0RE_---1LD_1LA1LD_1RA0RA"), 10).result, "nonhalt");
  assert.strictEqual(BB.haltingSegment(BB.parse("1RB1RC_0LA0RA_0LB---"), 2).result, "nonhalt");
  const b = BB.bouncerMoments(BB.parse("1RB1LE_1LC1RD_1LB1RC_1LA0RD_---0LA"), ".111(111)01111(11)C>.", 20000, 14);
  assert.deepStrictEqual(b.hits.slice(0, 3).map((h) => [h.step, h.counts]), [[37, [0, 0]], [76, [1, 1]], [121, [2, 2]]]);
});
if (failed) { console.log(`${failed} failed`); process.exit(1); }
console.log("all passed");
