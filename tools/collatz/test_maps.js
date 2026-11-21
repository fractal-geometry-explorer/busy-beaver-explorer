// Test the map steppers of maps.js against the machines themselves.
// usage: node tools/collatz/test_maps.js [MAX_STEPS]
// For every map with a tape pattern below, the machine is run from blank tape and the first map states of the orbit
// (as long as the run stays under MAX_STEPS) must appear as exact tapes, in order. Maps without a pattern are checked
// against the sequence quoted in their folder ("known").
"use strict";
const { MAPS } = require("./maps.js");
const MAX = Number(process.argv[2] || 3e7);

const r = (s, n) => s.repeat(Number(n));
// pattern(state) -> [left, headState, right]; left is the tape left of the head, right starts at the head cell
const PAT = {
  "1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE": ([n]) => [r("10", n), "A", "0"],
  "1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE": ([p, q]) => ["", "A", "0" + r("1", p) + "0" + r("1", q)],
  "1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB": ([d]) => [r("1", d - 2n), "B", "0"],
  "1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC": ([p, q]) => ["", "D", r("1", p) + "0" + r("1", q)],
  "1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB": ([p, q]) => ["", "C", r("1", p) + "0" + r("1", q)],
  "1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC": ([m, k]) => ["", "D", "110" + r("10", m) + r("110", k)],
  "1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA": ([n, m]) => ["", "A", m < 0n ? "011" + r("01", n) : "011" + r("01", n) + "011" + r("01", m)],
  "1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---": ([z, y]) => ["", "A", "0010" + r("0", z) + r("10", y) + "01"],
  "1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE": ([p, q]) => [r("10", p) + "0" + r("1", q), "E", "0"],
  "1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA": ([a, c]) => ["", "A", "0" + r("1", a) + "0" + r("1", c)],
  "1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC": ([n, m]) => ["", "C", "0" + r("0", n) + r("1", m) + "01"],
  "1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC": ([a, b]) => [r("1", a) + "0", "C", r("1", b)],
  "1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---": ([m, k, b]) => [r("1", m) + r("10", k), "C", r("1", b)],
  "1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA": ([m, n]) => [r("1011", m) + r("1", n) + r("10", 3), "A", "1"],
  "1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE": ([i, j, J]) => [r("1", 2n * i) + "0" + r("1", 2n * j) + "011" + (J ? "011" : ""), "B", "0"],
  "1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD": ([u, v, q]) => ["", "C", "0110" + (q ? "110" : "") + r("11", u) + "0" + r("11", v)],
};

function parse(m) {
  const rows = m.split("_");
  return rows.map((row) => [0, 1].map((b) => {
    const t = row.slice(3 * b, 3 * b + 3);
    return t[0] === "-" ? null : [Number(t[0]), t[1] === "R" ? 1 : -1, t.charCodeAt(2) - 65];
  }));
}
const trimL = (s) => s.replace(/^0+/, "");
const trimR = (s) => s.replace(/0+$/, "");

// cheap filter before the full comparison: the 12 cells on each side of the head
function quick(tape, h, L, R) {
  for (let i = 0; i < 12; i++) { const c = i < R.length ? R.charCodeAt(i) - 48 : 0; if (tape[h + i] !== c) return false; }
  for (let i = 1; i <= 12; i++) { const c = i <= L.length ? L.charCodeAt(L.length - i) - 48 : 0; if (tape[h - i] !== c) return false; }
  return true;
}

function check(map) {
  const pat = PAT[map.m];
  const orbit = [map.start];
  for (let i = 0; i < 60; i++) { const n = map.step(orbit[orbit.length - 1]); if (!Array.isArray(n)) break; orbit.push(n); }
  if (map.known) {
    for (let i = 0; i < map.known.length; i++) {
      const want = Array.isArray(map.known[i]) ? map.known[i] : [map.known[i]];
      const got = orbit[i];
      if (!got || want.some((w, j) => w !== got[j])) return `known value ${i} differs: ${want} vs ${got}`;
    }
  }
  if (!pat) return map.known ? `ok (${map.known.length} quoted values)` : "NO CHECK";
  const T = parse(map.m);
  const W = 1 << 22; const tape = new Uint8Array(W); let h = W >> 1, lo = h, hi = h, s = 0;
  let idx = 0; let want = pat(orbit[0]); let wantL = trimL(want[0]), wantR = trimR(want[2]), wantS = want[1].charCodeAt(0) - 65;
  for (let st = 0; st < MAX; st++) {
    if (s === wantS && quick(tape, h, wantL, wantR)) {
      let L = ""; for (let i = lo; i < h; i++) L += tape[i];
      let R = ""; for (let i = h; i <= hi; i++) R += tape[i];
      if (trimL(L) === wantL && trimR(R) === wantR) {
        idx++;
        if (idx >= orbit.length) return `ok (${idx} map states found in the run)`;
        want = pat(orbit[idx]); wantL = trimL(want[0]); wantR = trimR(want[2]); wantS = want[1].charCodeAt(0) - 65;
      }
    }
    const tr = T[s][tape[h]];
    if (!tr) return `machine halted after matching ${idx} states`;
    tape[h] = tr[0]; h += tr[1]; s = tr[2];
    if (h < lo) lo = h; if (h > hi) hi = h;
    if (h <= 0 || h >= W - 1) return `tape overflow after ${idx} states`;
  }
  return idx >= 4 ? `ok (${idx} map states found in ${MAX} steps)` : `FAIL: only ${idx} map states found (next ${orbit[idx]})`;
}

let bad = 0;
for (const map of MAPS) {
  const res = check(map);
  if (!res.startsWith("ok")) bad++;
  console.log(`${map.m}  ${res}`);
}
process.exit(bad ? 1 : 0);
