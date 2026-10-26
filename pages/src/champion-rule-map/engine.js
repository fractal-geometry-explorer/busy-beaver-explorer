// ---- Engine: the real BB(6) champion plus a decoder for mxdys's tape layout ----
const MACHINE = "1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE";
const SNAME = "ABCDEF";
const TR = [];
MACHINE.split("_").forEach((g, s) => {
  for (let y = 0; y < 2; y++) {
    const x = g.slice(3 * y, 3 * y + 3);
    TR[s * 2 + y] = { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x[2] === "Z" ? -1 : x.charCodeAt(2) - 65, txt: x };
  }
});
const LH = [1, 1, 1, 0, 1, 1];

function lcCells(n, x) { // n binary digits of x, most significant first; 1 -> 100, 0 -> 111
  const out = [];
  for (let i = n - 1; i >= 0; i--) out.push(...(((x >> i) & 1) ? [1, 0, 0] : [1, 1, 1]));
  return out;
}

const SCENARIOS = {
  real: { blank: true },
  halt: { len0: 2, a0: 2, m: 2, a: 0, midv: 0, b: 2 },
  reset: { len0: 1, a0: 1, m: 2, a: 0, midv: 0, b: 2 },
};

function fmt(v) { return v.toString().replace(/\B(?=(\d{3})+(?!\d))/g, ","); }
function nextPhase(m) { return m === 2 ? 1 : m === 1 ? 0 : 2; }

class Sim {
  constructor(key) {
    this.key = key;
    this.cap = 1 << 13; this.t = new Uint8Array(this.cap); this.off = this.cap >> 1;
    this.pos = 0; this.st = 0; this.steps = 0; this.halted = false;
    this.lo = 0; this.hi = 0;
    this.cp = null; this.cpCount = 0; this.segs = []; this.log = []; this.runStart = 0n;
    const sc = SCENARIOS[key];
    if (!sc.blank) {
      const left = [...LH, ...lcCells(sc.len0, sc.a0), 1, 0, 0, 1, 0, ...Array(sc.m).fill(1), ...lcCells(sc.a, sc.midv)];
      const right = [0, 1, 1, 1, 0, 0];
      for (let i = 0; i < 1 + sc.b; i++) right.push(1, 1, 1);
      const cells = left.concat(right);
      cells.forEach((c, i) => { this.t[this.off + i] = c; });
      this.lo = 0; this.hi = cells.length - 1;
      this.pos = left.length - 1; this.st = 4;
      const cp = this.check();
      this.accept(cp);
    }
  }
  grow() {
    const ncap = this.cap * 2, nt = new Uint8Array(ncap), noff = this.off + (this.cap >> 1);
    nt.set(this.t, this.cap >> 1);
    this.t = nt; this.cap = ncap; this.off = noff;
  }
  rule() { return this.halted ? null : TR[this.st * 2 + this.t[this.pos + this.off]]; }
  step() {
    if (this.halted) return false;
    const idx = this.pos + this.off, r = TR[this.st * 2 + this.t[idx]];
    this.t[idx] = r.w;
    this.pos += r.d; this.steps++;
    if (this.pos < this.lo) this.lo = this.pos;
    if (this.pos > this.hi) this.hi = this.pos;
    const pi = this.pos + this.off;
    if (pi < 64 || pi > this.cap - 64) this.grow();
    if (r.n < 0) {
      this.halted = true;
      this.log.push({ step: this.steps, kind: "halt", text: this.haltText() });
      return false;
    }
    this.st = r.n;
    if (this.st === 4) { const cp = this.check(); if (cp) this.accept(cp); }
    return true;
  }
  // Is the tape in mxdys's S1 layout with the head here? Returns the decoded numbers.
  check() {
    const t = this.t, p = this.pos + this.off;
    if (t[p + 1] !== 0 || t[p + 2] !== 1 || t[p + 3] !== 1 || t[p + 4] !== 1 || t[p + 5] !== 0 || t[p + 6] !== 0) return null;
    let q = p + 7; while (t[q] === 1) q++;
    const k = q - (p + 7);
    if (k === 0 || k % 3) return null;
    const hiI = this.hi + this.off;
    for (let j = q; j <= hiI + 1; j++) if (t[j]) return null;
    let L = this.lo + this.off; while (L < p && t[L] === 0) L++;
    if (p - L + 1 < 11) return null;
    for (let i = 0; i < 6; i++) if (t[L + i] !== LH[i]) return null;
    let r = p; const mid = [];
    while (r - 2 >= L + 6) {
      const a = t[r - 2], b = t[r - 1], c = t[r];
      if (a === 1 && b === 0 && c === 0) mid.push(1);
      else if (a === 1 && b === 1 && c === 1) mid.push(0);
      else break;
      r -= 3;
    }
    for (let m = 0; m < 3; m++) {
      const tail = [1, 0, 0, 1, 0, ...Array(m).fill(1)], tl = tail.length;
      let ok = r - tl + 1 >= L + 6;
      for (let i = 0; ok && i < tl; i++) if (t[r - tl + 1 + i] !== tail[i]) ok = false;
      if (!ok) continue;
      const end = r - tl; // last index of countdown digits
      const cnt = end - (L + 6) + 1;
      if (cnt < 0 || cnt % 3) continue;
      let a0 = 0n, good = true;
      for (let i = L + 6; i <= end; i += 3) {
        const a = t[i], b = t[i + 1], c = t[i + 2];
        if (a === 1 && b === 0 && c === 0) a0 = a0 * 2n + 1n;
        else if (a === 1 && b === 1 && c === 1) a0 = a0 * 2n;
        else { good = false; break; }
      }
      if (!good) continue;
      let midv = 0n;
      for (let i = mid.length - 1; i >= 0; i--) midv = midv * 2n + BigInt(mid[i]);
      const o = this.off, len0 = cnt / 3;
      const c0 = L + 6, dv = c0 + 3 * len0, ph = dv + 5, md = ph + m, gp = p + 1, pl = p + 7;
      return {
        step: this.steps, len0, a0, m, a: mid.length, bits: mid.slice().reverse(), midv, b: k / 3 - 1,
        segs: [
          [L - o, c0 - 1 - o, "frame"], [c0 - o, dv - 1 - o, "count"], [dv - o, ph - 1 - o, "frame"],
          [ph - o, md - 1 - o, "phase"], [md - o, p - o, "mid"], [gp - o, pl - 1 - o, "frame"],
          [pl - o, q - 1 - o, "pile"],
        ].filter(s => s[1] >= s[0]),
      };
    }
    return null;
  }
  accept(cp) {
    if (cp.len0 === 0) return; // a stray match during the warm-up
    const pr = this.cp;
    this.cpCount++;
    const say = (kind, text) => this.log.push({ step: cp.step, kind, text });
    if (!pr) {
      this.runStart = cp.midv;
      if (this.key === "real") say("start", `Starting layout is in place. Countdown ${cp.a0} (binary ${cp.a0.toString(2)}), phase ${cp.m}, middle counter ${fmt(cp.midv)} (${cp.a} one-digits), pile 0.`);
      else say("start", `Hand-built start. Countdown ${cp.a0}, phase ${cp.m}, middle counter ${fmt(cp.midv)}, pile ${cp.b}.`);
    } else if (pr.midv > 0n && cp.midv === pr.midv - 1n) {
      if (cp.midv === 0n) say("empty", `Middle counter reached 0 after ${fmt(this.runStart)} ticks. Pile = ${fmt(cp.b)}.`);
    } else if (pr.midv === 0n && pr.a0 > 0n && cp.a0 === pr.a0 - 1n) {
      this.runStart = cp.midv;
      say("convert", `Convert. Countdown ${pr.a0} → ${cp.a0}, phase ${pr.m} → ${cp.m}. The ${fmt(pr.b)}-unit pile became ${fmt(pr.b)} one-digits, so the middle counter is 2^${pr.b} − 1 = ${fmt(cp.midv)}.`);
    } else if (pr.midv === 0n && pr.a0 === 0n) {
      this.runStart = cp.midv;
      say("reset", `Reset. The countdown was 0 in phase 1, so it absorbed the middle block and refilled: ${cp.len0} digits, value ${fmt(cp.a0)}. The ${fmt(pr.b)}-unit pile became the middle counter, 2^${pr.b} − 1 = ${fmt(cp.midv)}. Phase → ${cp.m}.`);
    } else {
      this.runStart = cp.midv;
      say("other", `New layout: countdown ${cp.a0}, phase ${cp.m}, middle counter ${fmt(cp.midv)}, pile ${fmt(cp.b)}.`);
    }
    this.cp = cp; this.segs = cp.segs;
  }
  haltText() {
    const c = this.cp;
    if (c && c.a0 === 0n && c.m === 0) return `Halted. The countdown was 0 and the phase was 0 when the middle counter emptied. Final pile ${fmt(c.b)}.`;
    return "Halted.";
  }
  now() {
    const c = this.cp;
    if (this.halted) return { tag: "Halted", text: "The machine reached its halt rule (state B reading 1). Nothing more happens." };
    if (!c) return { tag: "Warm-up", text: "The machine is writing its starting layout. The decoded numbers appear at step 821." };
    if (c.midv > 0n) {
      const done = this.runStart - c.midv;
      return { tag: "Tick", text: `Tick ${fmt(done + 1n)} of ${fmt(this.runStart)}. The head walks left to the middle counter's lowest 1-digit, subtracts 1, then walks right and adds one unit to the end of the pile. When the counter empties the pile will hold ${fmt(BigInt(c.b) + c.midv)}.` };
    }
    if (c.a0 > 0n) return { tag: "Convert", text: `The middle counter is empty, so the machine converts: countdown ${c.a0} → ${c.a0 - 1n}, phase ${c.m} → ${nextPhase(c.m)}, and the ${fmt(c.b)}-unit pile becomes ${fmt(c.b)} one-digits in the middle counter.` };
    if (c.m === 1) return { tag: "Reset", text: "Countdown 0, phase 1: the machine resets. The countdown swallows the middle block and refills to nearly all 1-digits." };
    if (c.m === 0) return { tag: "Halting", text: "Countdown 0, phase 0: the machine is walking to its halt rule." };
    return { tag: "Phase 2", text: "Countdown 0 in phase 2." };
  }
}
if (typeof module !== "undefined") module.exports = { Sim, TR, SNAME, fmt };
