(function (D) {
  "use strict";
  // The machine 1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC: TR[state][read] = {w, m, s} or null (D reading 0).
  var SN = "ABCDEF";
  var TR = D.machine.split("_").map(function (g) {
    return [g.slice(0, 3), g.slice(3, 6)].map(function (t) {
      return t[2] === "-" ? null : { w: +t[0], m: t[1] === "R" ? 1 : -1, s: SN.indexOf(t[2]) };
    });
  });

  // ---- Level 1: the plain machine on a byte array that grows on both sides.
  function Machine(str, st) {
    str = str || "";
    this.N = 1 << 14; while (this.N < 4 * str.length) this.N *= 2;
    this.t = new Uint8Array(this.N); this.o = this.N >> 1;
    for (var i = 0; i < str.length; i++) this.t[this.o + i] = str.charCodeAt(i) - 48;
    this.h = this.o; this.s = st || 0; this.n = 0; this.halted = false;
    this.lone = this.N; this.hi = this.o + str.length;      // first cell holding a 1, one past the last cell visited
    for (var x = 0; x < this.N; x++) if (this.t[x]) { this.lone = x; break; }
  }
  Machine.prototype.grow = function () {
    var N = this.N * 2, t = new Uint8Array(N), d = this.N >> 1;
    t.set(this.t, d); this.t = t; this.o += d; this.h += d; this.hi += d; this.lone = this.lone >= this.N ? N : this.lone + d; this.N = N;
  };
  // Runs up to step T; calls cb(this) at every left-end moment (state B, no 1 at or left of the head, reading 0).
  // cb returning false stops the run there.
  Machine.prototype.run = function (T, cb) {
    var t = this.t, h = this.h, s = this.s, n = this.n, hi = this.hi, lone = this.lone, N = this.N;
    while (n < T) {
      if (h < 2 || h > N - 3) {
        this.h = h; this.s = s; this.n = n; this.hi = hi; this.lone = lone;
        this.grow(); t = this.t; h = this.h; hi = this.hi; lone = this.lone; N = this.N;
      }
      var a = TR[s][t[h]];
      if (!a) { this.halted = true; break; }
      t[h] = a.w;
      if (a.w) { if (h < lone) lone = h; } else if (h === lone) { while (lone < hi && !t[lone]) lone++; if (lone >= hi) lone = N; }
      h += a.m; s = a.s; n++;
      if (h >= hi) hi = h + 1;
      if (s === 1 && a.m < 0 && t[h] === 0 && h < lone && cb) {
        this.h = h; this.s = s; this.n = n; this.hi = hi; this.lone = lone;
        if (cb(this) === false) return this;
      }
    }
    this.h = h; this.s = s; this.n = n; this.hi = hi; this.lone = lone;
    return this;
  };
  // The tape from the head to the last 1, as a string of 0s and 1s.
  Machine.prototype.fromHead = function () {
    var e = this.hi; while (e > this.h && this.t[e - 1] === 0) e--;
    var s = ""; for (var x = this.h; x < e; x++) s += this.t[x];
    return s;
  };
  Machine.prototype.cells = function (a, b) { var r = []; for (var x = a; x < b; x++) r.push(this.t[x + this.o] || 0); return r; };

  // ---- Level 2: the tape as a list. Items: strings of literal cells and numbers n meaning (01)^n.
  // The same greedy reading as py/regimes.py: two or more 01s in a row become a number.
  function parse(s) {
    var out = [], i = 0, lit = "";
    while (i < s.length) {
      var n = 0; while (s.substr(i + 2 * n, 2) === "01") n++;
      if (n >= 2) { if (lit) { out.push(lit); lit = ""; } out.push(n); i += 2 * n; }
      else { lit += s[i]; i++; }
    }
    if (lit) out.push(lit);
    return out;
  }
  // The same reading of a list of atoms: "0", "1" and {r: m} for (01)^m (m may be huge).
  function canon(atoms) {
    var out = [], lit = "", i = 0;
    while (i < atoms.length) {
      var cnt = 0, j = i;
      for (;;) {
        if (j < atoms.length && typeof atoms[j] === "object") { cnt += atoms[j].r; j++; }
        else if (atoms[j] === "0" && atoms[j + 1] === "1") { cnt++; j += 2; }
        else break;
      }
      if (cnt >= 2) { if (lit) { out.push(lit); lit = ""; } out.push(cnt); i = j; }
      else { lit += atoms[i] === undefined ? "" : (typeof atoms[i] === "object" ? "01" : atoms[i]); i++; }
    }
    if (lit) out.push(lit);
    // drop trailing zeros
    while (out.length && typeof out[out.length - 1] === "string") {
      var l = out[out.length - 1].replace(/0+$/, "");
      if (l) { out[out.length - 1] = l; break; }
      out.pop();
    }
    return out;
  }
  function listEq(a, b) {
    if (a.length !== b.length) return false;
    for (var i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
    return true;
  }
  function unparse(l) { return l.map(function (x) { return typeof x === "number" ? "01".repeat(x) : x; }).join(""); }

  // ---- Level 3: the 62 templates B> 00 (01)^(3k+4) sep (01)^(3j+beta) rest.
  function tplList(t, k, j) {
    var d = D.tpl[t], l = ["00", 3 * k + 4, d.sep, 3 * j + d.beta].concat(d.rest);
    var atoms = [];
    l.forEach(function (x) { if (typeof x === "number") atoms.push({ r: x }); else for (var q = 0; q < x.length; q++) atoms.push(x[q]); });
    return canon(atoms);
  }
  function tplStr(t, k, j) { return unparse(tplList(t, k, j)); }
  // Which template (t, k, j) a list is, or null.
  function whichTpl(l) {
    if (l.length < 4 || l[0] !== "00" || typeof l[1] !== "number" || typeof l[3] !== "number") return null;
    var a = l[1], b = l[3];
    if (a < 4 || (a - 4) % 3) return null;
    for (var t = 0; t < D.tpl.length; t++) {
      var d = D.tpl[t];
      if (l[2] !== d.sep || b < d.beta || (b - d.beta) % 3) continue;
      var k = (a - 4) / 3, j = (b - d.beta) / 3;
      if (listEq(tplList(t, k, j), l)) return [t, k, j];
    }
    return null;
  }
  // The tables' own sequence from the template the run reaches at step 1,277,431.
  function nextTpl(x) {
    var t = x[0], k = x[1], j = x[2];
    if (k > 0) return [D.nxt[t], k - 1, j + D.dj[t], "round"];
    return [D.endT[t], j - 200 + D.endC1[t], D.endC2[t], "end"];
  }
  var START = [31, 38, 163];
  function macro(n) { var out = [START]; while (out.length < n) out.push(nextTpl(out[out.length - 1])); return out; }
  function phi(x) { return x[2] + 2 * x[1] + D.potL[x[0]]; }

  // ---- The shift-rule simulator: the tape as two stacks of tokens {w, n} (w a word of cells, n copies).
  // Every step is a real step of the machine; a whole run of copies of a word is crossed in one move when one copy,
  // tried on its own with a few cells of context, takes the head through in the same state (as cross_r / cross_l in
  // Lean, and as auto in lean/SymCheck.lean does it with formulas).
  function Fast(list, st) {
    this.L = []; this.R = []; this.s = st; this.steps = 0; this.moves = 0; this.cross = 0; this.halted = false;
    for (var i = list.length - 1; i >= 0; i--) {
      var x = list[i];
      if (typeof x === "number") this.R.push({ w: "01", n: x });
      else for (var q = x.length - 1; q >= 0; q--) this.R.push({ w: x[q], n: 1 });
    }
    this.cache = {}; this.trace = null;
  }
  function popR(S) {
    if (!S.length) return "0";
    var T = S[S.length - 1], b = T.w[0];
    if (T.w.length === 1) { if (--T.n === 0) S.pop(); }
    else { S.pop(); if (T.n > 1) S.push({ w: T.w, n: T.n - 1 }); S.push({ w: T.w.slice(1), n: 1 }); }
    return b;
  }
  function popL(S) {
    if (!S.length) return "0";
    var T = S[S.length - 1], b = T.w[T.w.length - 1];
    if (T.w.length === 1) { if (--T.n === 0) S.pop(); }
    else { S.pop(); if (T.n > 1) S.push({ w: T.w, n: T.n - 1 }); S.push({ w: T.w.slice(0, -1), n: 1 }); }
    return b;
  }
  function push(S, b) {
    if (!S.length && b === "0") return;            // blank beyond the end
    var T = S[S.length - 1];
    if (T && T.w === b) T.n++; else S.push({ w: b, n: 1 });
  }
  function peekBits(S, c, fromLeft) {          // the c cells nearest the head on stack S, in tape order
    var out = [], i = S.length - 1, off = 0, got = 0, cells = [];
    while (got < c) {
      if (i < 0) { cells.push("0"); got++; continue; }
      var T = S[i], len = T.w.length * T.n;
      if (off >= len) { i--; off = 0; continue; }
      var p = off % T.w.length;
      cells.push(fromLeft ? T.w[p] : T.w[T.w.length - 1 - p]); off++; got++;
    }
    return fromLeft ? cells.join("") : cells.reverse().join("");
  }
  function trial(win, h0, s, right, ctx) {      // one copy on its own: returns [steps, new window] or null
    var c = win.split("").map(Number), h = h0, st = s, k = 0;
    for (;;) {
      var a = TR[st][c[h]];
      if (!a) return null;
      c[h] = a.w; h += a.m; st = a.s; k++;
      if (k > 400 || h < 0) return null;
      if (h >= c.length) return right && st === s ? [k, c.join("")] : null;
      if (!right && h === 0 && st === s && c.slice(0, ctx).join("") === win.slice(win.length - ctx)) return [k, c.join("")];
    }
  }
  Fast.prototype.tryCross = function () {
    var R = this.R, L = this.L, s = this.s, T, g, c, W, key, res, N;
    // rightward: the token ahead, after c cells of context behind the head
    T = R[R.length - 1];
    if (T && T.n >= 2) {
      for (g = 1; g <= 3; g++) {
        N = Math.floor(T.n / g); if (N < 1 || N * g < 2) continue;
        W = T.w.repeat(g);
        for (c = 0; c <= 3; c++) {
          var ctxL = peekBits(L, c, false);
          key = "r" + s + "|" + ctxL + "|" + W;
          res = this.cache[key];
          if (res === undefined) {
            var tr = trial(ctxL + W, c, s, true, c);
            res = tr && tr[1].slice(W.length) === ctxL ? [tr[0], tr[1].slice(0, W.length)] : null;
            this.cache[key] = res;
          }
          if (res) {
            for (var q = 0; q < c; q++) popL(L);
            R.pop(); if (T.n - N * g > 0) R.push({ w: T.w, n: T.n - N * g });
            L.push({ w: res[1], n: N });
            for (q = 0; q < c; q++) push(L, ctxL[q]);
            if (this.trace) this.trace.push({ dir: "R", st: s, ctx: ctxL, from: W, to: res[1], n: N, k: res[0], at: this.steps - res[0] * N });
            this.steps += res[0] * N; this.moves++; this.cross++;
            return true;
          }
        }
      }
    }
    // leftward: the token behind the head, with c cells of context ahead (the head cell first)
    T = L[L.length - 1];
    if (T && T.n >= 2) {
      for (g = 1; g <= 3; g++) {
        N = Math.floor(T.n / g); if (N < 1 || N * g < 2) continue;
        W = T.w.repeat(g);
        for (c = 1; c <= 3; c++) {
          var ctxR = peekBits(R, c, true);
          key = "l" + s + "|" + ctxR + "|" + W;
          res = this.cache[key];
          if (res === undefined) {
            var tl = trial(W + ctxR, W.length, s, false, c);
            res = tl ? [tl[0], tl[1].slice(c)] : null;
            this.cache[key] = res;
          }
          if (res) {
            for (var r = 0; r < c; r++) popR(R);
            L.pop(); if (T.n - N * g > 0) L.push({ w: T.w, n: T.n - N * g });
            R.push({ w: res[1], n: N });
            for (r = c - 1; r >= 0; r--) R.push({ w: ctxR[r], n: 1 });
            if (this.trace) this.trace.push({ dir: "L", st: s, ctx: ctxR, from: W, to: res[1], n: N, k: res[0], at: this.steps - res[0] * N });
            this.steps += res[0] * N; this.moves++; this.cross++;
            return true;
          }
        }
      }
    }
    return false;
  };
  Fast.prototype.step = function () {
    var b = this.R.length ? this.R[this.R.length - 1].w[0] : "0";
    var a = TR[this.s][+b];
    if (!a) { this.halted = true; return false; }
    popR(this.R);
    if (a.m > 0) push(this.L, String(a.w));
    else { push(this.R, String(a.w)); push(this.R, popL(this.L)); }
    this.s = a.s; this.steps++; this.moves++;
    if (this.trace) { var lt = this.trace[this.trace.length - 1]; if (lt && lt.dir === "S") lt.n++; else this.trace.push({ dir: "S", n: 1, at: this.steps - 1 }); }
    return true;
  };
  Fast.prototype.leftEmpty = function () {
    for (var i = 0; i < this.L.length; i++) if (this.L[i].w.indexOf("1") >= 0) return false;
    return true;
  };
  Fast.prototype.list = function () {           // the tape from the head, read as a list
    var atoms = [];
    for (var i = this.R.length - 1; i >= 0; i--) {
      var T = this.R[i];
      if (/^(01)+$/.test(T.w)) atoms.push({ r: T.w.length / 2 * T.n });
      else if (T.w.length * T.n <= 4096) { for (var q = 0; q < T.n; q++) for (var p = 0; p < T.w.length; p++) atoms.push(T.w[p]); }
      else return null;
    }
    return canon(atoms);
  };
  // At a left-end moment nothing is written left of the head: rewrite the right side in normal form, with every
  // stretch of 01s as one token (what auto does when it compares normal forms at the left end).
  Fast.prototype.normalize = function () {
    var l = this.list(); if (!l) return;
    var f = new Fast(l, this.s); this.L = []; this.R = f.R;
  };
  // Runs to the next left-end moment (state B, nothing written left of the head, reading 0).
  Fast.prototype.toLeftEnd = function (maxMoves) {
    var lim = this.moves + (maxMoves || 1e6);
    while (this.moves < lim) {
      if (!this.tryCross()) {
        if (!this.step()) return "halt";
        var hb = this.R.length ? this.R[this.R.length - 1].w[0] : "0";
        if (this.s === 1 && hb === "0" && this.leftEmpty()) { this.normalize(); return "left"; }
      }
    }
    return "limit";
  };

  function fmt(x) { return Number(x).toLocaleString("en-US"); }
  function css(n) { return getComputedStyle(document.documentElement).getPropertyValue(n).trim(); }

  // A tape list drawn as a strip of cells and bars (into element el, of class pw-strip).
  function strip(el, list, opt) {
    opt = opt || {};
    el.textContent = "";
    if (opt.head !== false) { var h = document.createElement("span"); h.className = "head"; h.textContent = opt.head || "B>"; el.appendChild(h); }
    var r = 0;
    list.forEach(function (x) {
      if (typeof x === "string") {
        var w = document.createElement("span"); w.className = "lit";
        for (var q = 0; q < x.length; q++) { var c = document.createElement("span"); c.className = "c" + (x[q] === "1" ? " one" : ""); c.textContent = x[q]; w.appendChild(c); }
        el.appendChild(w);
      } else {
        var b = document.createElement("span");
        var cls = x.cls || (r === 0 ? "a" : r === 1 ? "b" : "o");
        b.className = "run " + cls + (x.v ? " v" : "");
        b.textContent = "(01) \u00d7 " + (x.label !== undefined ? x.label : fmt(typeof x === "number" ? x : x.n));
        el.appendChild(b); r++;
      }
    });
  }
  function tplSym(t, ka, jb) {
    var d = D.tpl[t];
    return ["00", { label: ka, v: true, cls: "a" }, d.sep, { label: jb, v: true, cls: "b" }].concat(d.rest.map(function (x) {
      return typeof x === "number" ? { n: x, cls: "o" } : x;
    }));
  }
  function name(t) { return D.tpl[t].name; }

  return { D: D, SN: SN, TR: TR, Machine: Machine, Fast: Fast, parse: parse, canon: canon, listEq: listEq, unparse: unparse,
           tplList: tplList, tplStr: tplStr, whichTpl: whichTpl, nextTpl: nextTpl, macro: macro, phi: phi, START: START,
           fmt: fmt, css: css, strip: strip, tplSym: tplSym, name: name };
})
