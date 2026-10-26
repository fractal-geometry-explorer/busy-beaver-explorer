const M = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const S = "ABCDEF";
const TR = []; M.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65, txt: x }; } });
class T {
  constructor(cells = "", head = 0, state = 0) { this.cap = 1 << 16; this.t = new Uint8Array(this.cap); this.off = this.cap >> 1; for (let i = 0; i < cells.length; i++) this.t[this.off + i] = cells[i] === '1' ? 1 : 0; this.pos = head; this.st = state; this.steps = 0; this.lo = 0; this.hi = Math.max(0, cells.length - 1); this.halted = false; }
  step() { const r = TR[this.st*2 + this.t[this.pos+this.off]]; if (!r) { this.halted = true; return false; } this.t[this.pos+this.off] = r.w; this.pos += r.d; this.st = r.n; this.steps++; if (this.pos < this.lo) this.lo = this.pos; if (this.pos > this.hi) this.hi = this.pos; return true; }
  key() { return S[this.st] + this.t[this.pos+this.off]; }
  str(a = this.lo, b = this.hi) { let r = ''; for (let i = a; i <= b; i++) { const c = this.t[i+this.off] ? '1' : '0'; r += i === this.pos ? `[${c}]` : c; } return r; }
  rle(a = this.lo, b = this.hi) { let s = ''; for (let i = a; i <= b; i++) s += (i === this.pos ? '|' : '') + (this.t[i+this.off] ? '1' : '0'); return s.replace(/(10){2,}/g, m => ` (10)^${m.length/2} `); }
}
module.exports = { T, TR, S, M };
