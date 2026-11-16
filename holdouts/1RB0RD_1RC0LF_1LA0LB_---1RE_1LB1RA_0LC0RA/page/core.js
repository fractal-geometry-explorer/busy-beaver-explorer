// The plain machine and the cycle-rule templates of the Lean files, shared by the panels of this page.
function mkCore(TM, EVS) {
  "use strict";
  var W = [], MV = [], ST = [];
  TM.split("_").forEach(function (g, i) {
    for (var s = 0; s < 2; s++) {
      var t = g.substr(3 * s, 3), k = 2 * i + s;
      if (t[0] === "-") { W[k] = 0; MV[k] = 0; ST[k] = -1; } else { W[k] = +t[0]; MV[k] = t[1] === "R" ? 1 : -1; ST[k] = t.charCodeAt(2) - 65; }
    }
  });
  // The machine on a tape that grows on demand; cell x lives at t[x + o].
  function M() { this.n = 1 << 14; this.t = new Uint8Array(this.n); this.o = this.n >> 1; this.p = 0; this.s = 0; this.k = 0; this.lo = 0; this.hi = 0; this.halted = false; this.ev = 0; }
  M.prototype.grow = function () { var n = this.n * 2, t = new Uint8Array(n); t.set(this.t, this.n >> 1); this.t = t; this.o += this.n >> 1; this.n = n; };
  M.prototype.get = function (x) { var i = x + this.o; return i >= 0 && i < this.n ? this.t[i] : 0; };
  M.prototype.set = function (x, v) { while (x + this.o < 4 || x + this.o >= this.n - 4) this.grow(); this.t[x + this.o] = v; };
  // Writes a 0/1 string from cell 0 on, the head on its first cell, in state s.
  M.prototype.load = function (str, s) { for (var i = 0; i < str.length; i++) this.set(i, +str[i]); this.p = 0; this.s = s; this.lo = 0; this.hi = Math.max(0, str.length - 1); return this; };
  // Runs to the next event: a move to the left, in state EVS, onto the leftmost cell visited so far or beyond it.
  // At most `limit` steps; true at an event, false at the limit or at a halt (then this.halted).
  M.prototype.toEvent = function (limit) {
    var t = this.t, o = this.o, p = this.p + o, s = this.s, k = this.k, end = k + limit, lo = this.lo + o, hi = this.hi + o, hit = false;
    while (k < end) {
      var kk = 2 * s + t[p], ns = ST[kk];
      if (ns < 0) { this.halted = true; break; }
      t[p] = W[kk]; p += MV[kk]; s = ns; k++;
      if (p > hi) hi = p;
      if (MV[kk] < 0 && p <= lo) { lo = p; if (s === EVS) { hit = true; break; } }
      if (p < 4 || p >= this.n - 4) {
        this.p = p - o; this.s = s; this.k = k; this.lo = lo - o; this.hi = hi - o; this.grow();
        t = this.t; o = this.o; p = this.p + o; lo = this.lo + o; hi = this.hi + o;
      }
    }
    this.p = p - o; this.s = s; this.k = k; this.lo = lo - o; this.hi = hi - o;
    if (hit) this.ev++;
    return hit;
  };
  // Runs `n` steps or to a halt; returns the number of steps done.
  M.prototype.run = function (n) {
    var k0 = this.k;
    while (this.k - k0 < n && !this.halted) {
      var kk = 2 * this.s + this.get(this.p), ns = ST[kk];
      if (ns < 0) { this.halted = true; break; }
      this.set(this.p, W[kk]); this.p += MV[kk]; this.s = ns; this.k++;
      if (this.p < this.lo) this.lo = this.p; if (this.p > this.hi) this.hi = this.p;
    }
    return this.k - k0;
  };
  // The cells from the head to the last 1 right of it.
  M.prototype.right = function () { var b = this.hi; while (b > this.p && !this.get(b)) b--; var a = []; for (var x = this.p; x <= b; x++) a.push(this.get(x)); return a.join(""); };
  M.prototype.cells = function (a, b) { var r = []; for (var x = a; x <= b; x++) r.push(this.get(x)); return r.join(""); };

  function rep(w, n) { return n > 0 ? new Array(n + 1).join(w) : ""; }
  function trim(s) { return s.replace(/0+$/, ""); }
  function nvars(rule) { return rule.t.filter(function (x) { return x[0] === "v"; }).length; }
  // The counts of the variable blocks of a cycle rule: b0 + M x before, b1 + M x after.
  function counts(rule, xs, after) { var j = 0, out = []; rule.t.forEach(function (x) { if (x[0] === "v") out.push((after ? x[3] : x[2]) + rule.mod * xs[j++]); }); return out; }
  // The template as cells, the variable blocks having the given counts.
  function inst(rule, cs) {
    var o = "", j = 0;
    rule.t.forEach(function (x) { o += x[0] === "c" ? x[1] : x[0] === "f" ? rep(x[1], x[2]) : rep(x[1], cs[j++]); });
    return o;
  }
  // The x values for which the tape (head cell first) is the template before the rule, or null.
  function match(rule, tape) {
    var re = "^", vs = [];
    rule.t.forEach(function (x) {
      if (x[0] === "c") re += x[1]; else if (x[0] === "f") re += rep(x[1], x[2]); else { re += "((?:" + x[1] + ")*)"; vs.push(x); }
    });
    var m = new RegExp(re + "0*$").exec(tape + "0");
    if (!m) return null;
    var xs = [];
    for (var i = 0; i < vs.length; i++) {
      var c = m[i + 1].length / vs[i][1].length;
      if (c < vs[i][2] || (c - vs[i][2]) % rule.mod) return null;
      xs.push((c - vs[i][2]) / rule.mod);
    }
    return xs;
  }
  // A template as text: (w)^n for blocks, with "b0+Mx" for the variable ones (or the given counts).
  function text(rule, cs) {
    var o = [], j = 0, lit = "";
    rule.t.forEach(function (x) {
      if (x[0] === "c") { lit += x[1]; return; }
      if (lit) { o.push(lit); lit = ""; }
      if (x[0] === "f") o.push(x[2] === 1 ? x[1] : "(" + x[1] + ")^" + x[2]);
      else { var c = cs ? cs[j] : x[2] + "+" + rule.mod + "x" + (j + 1); j++; o.push("(" + x[1] + ")^" + c); }
    });
    if (lit) o.push(lit);
    return o.join(" ");
  }
  // Checks a cycle rule on the machine: the template with these x, run for the rule's number of events, must be the
  // template after. Returns {ok, steps, before, after, got}.
  function checkRule(rule, xs, limit) {
    var b = inst(rule, counts(rule, xs, false)), a = inst(rule, counts(rule, xs, true));
    var m = new M().load(b, EVS), ok = true;
    for (var e = 0; e < rule.ev && ok; e++) ok = m.toEvent(limit || 4e8);
    var got = m.right();
    return { ok: ok && m.p === m.lo && trim(got) === trim(a), events: m.ev, steps: m.k, before: b, after: a, got: got, halted: m.halted };
  }
  // Checks a shift rule on the machine with n crossings and random cells around it. Right: the head in state q on
  // the first cell of (w)^(k n), the carried word u left of it (u nearest cell first); it must end in q on the first
  // cell after the copies, with u v^n behind it (nearest first), in n s steps, without leaving those cells.
  // Left: the head on the first cell of u, (w)^(k n) left of it (w nearest cell first); it must end in q on the
  // first cell of u, now where the copies began, with v^n right of u.
  function rev(s) { return s.split("").reverse().join(""); }
  function checkShift(r, n, rnd) {
    var pad = 12, L = "", R = "", i;
    for (i = 0; i < pad; i++) { L += rnd() < 0.5 ? "0" : "1"; R += rnd() < 0.5 ? "0" : "1"; }
    var q = r.q.charCodeAt(0) - 65, wk = rep(r.w, r.k * n), m = new M(), tape, start, endPos, want;
    if (r.d === "R") {
      tape = L + rev(r.u) + wk + R; start = pad + r.u.length;
      want = L + rev(rep(r.v, n)) + rev(r.u) + R; endPos = pad + r.u.length + r.v.length * n;
    } else {
      tape = L + rev(wk) + r.u + R; start = pad + wk.length;
      want = L + r.u + rep(r.v, n) + R; endPos = pad;
    }
    m.load(tape, q); m.p = start;
    var lo = pad - (r.d === "L" ? 1 : 0), hi = tape.length - pad - (r.d === "R" ? 0 : 1), inside = true, steps = 0;
    while (steps < r.s * n) {
      m.run(1); steps++;
      if (m.halted) break;
      if (steps < r.s * n && (m.p < pad || m.p > tape.length - pad - 1)) { inside = false; break; }
    }
    var got = m.cells(0, tape.length - 1);
    return { ok: !m.halted && inside && m.s === q && m.p === endPos && got === want, steps: steps, tape: tape, start: start, got: got, want: want, end: m.p, endPos: endPos };
  }
  // A small seeded random generator, so that a check can be repeated.
  function rng(seed) { var x = seed >>> 0 || 1; return function () { x ^= x << 13; x >>>= 0; x ^= x >>> 17; x ^= x << 5; x >>>= 0; return x / 4294967296; }; }
  // Draws a tape (string of 0/1) on a canvas, coloured by segments [[from, to, cssVar], ...] (cell indices, `to`
  // excluded); a 1 is drawn in the segment's colour, a 0 pale. Long tapes are drawn one pixel column per several
  // cells, shaded by the share of 1s. `head`: index of the head cell (marked below the strip).
  function drawTape(cv, str, segs, head) {
    var w = cv.clientWidth || 600, h = cv.clientHeight || 46, dpr = window.devicePixelRatio || 1;
    cv.width = Math.round(w * dpr); cv.height = Math.round(h * dpr);
    var g = cv.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, w, h);
    var n = Math.max(str.length, 1), cw = w / n, y0 = 4, ch = h - 16, col = {}, bg = css("--sunk");
    function c(v) { return col[v] || (col[v] = css(v)); }
    var segOf = new Array(n);
    segs.forEach(function (S) { for (var i = S[0]; i < S[1] && i < n; i++) segOf[i] = S[2]; });
    g.fillStyle = bg; g.fillRect(0, y0, w, ch);
    if (cw >= 2) {
      for (var i = 0; i < n; i++) {
        g.globalAlpha = str[i] === "1" ? 1 : 0.22; g.fillStyle = c(segOf[i] || "--muted");
        g.fillRect(i * cw, y0, Math.max(cw - (cw >= 5 ? 1 : 0), 1), ch);
      }
    } else {
      for (var x = 0; x < w; x++) {
        var a = Math.floor(x / cw), b = Math.max(a + 1, Math.floor((x + 1) / cw)), ones = 0;
        for (var j = a; j < b && j < n; j++) ones += str[j] === "1" ? 1 : 0;
        g.globalAlpha = 0.22 + 0.78 * ones / Math.max(1, Math.min(b, n) - a); g.fillStyle = c(segOf[a] || "--muted");
        g.fillRect(x, y0, 1, ch);
      }
    }
    g.globalAlpha = 1;
    if (head != null) {
      var hx = (head + 0.5) * cw; g.fillStyle = c("--head");
      g.beginPath(); g.moveTo(hx, y0 + ch + 1); g.lineTo(hx - 5, y0 + ch + 10); g.lineTo(hx + 5, y0 + ch + 10); g.fill();
    }
  }
  function fmt(x) { return Number(x).toLocaleString("en-US"); }
  function css(name) { return getComputedStyle(document.documentElement).getPropertyValue(name).trim(); }
  function onTheme(f) {
    try { window.matchMedia("(prefers-color-scheme: dark)").addEventListener("change", f); } catch (e) {}
    try { new MutationObserver(f).observe(document.documentElement, { attributes: true, attributeFilter: ["data-theme"] }); } catch (e) {}
    window.addEventListener("resize", f);
  }
  return { TM: TM, M: M, rep: rep, trim: trim, rev: rev, nvars: nvars, counts: counts, inst: inst, match: match, text: text,
           checkRule: checkRule, checkShift: checkShift, rng: rng, fmt: fmt, drawTape: drawTape, css: css, onTheme: onTheme };
}
if (typeof module !== "undefined") module.exports = mkCore;
