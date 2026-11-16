"""The XOR-sweep widgets of the explainer pages (family F08, the machines with the 111110 block).

A machine whose tape, read in pairs at each turn at the right end, is a word changed by one XOR sweep per round
trip (see holdouts/1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA/README.md) gives its explainer an object

  xs   {state, off, cost}: the state of the head at a turn at the right end, where the head pair 11 starts
       (0: under the head, -1: one cell left of it), and the constant of the step count 4 d + cost of a sweep

and sections that carry "widget": one of "layers" (one moment of the real run at every layer), "sweep" (one sweep
stage by stage, checked against the real machine), "block" (the block's length enters only mod 3) or "orbit" (the
zone orbit of lean/Zone.lean, run in the browser).

`XS_ENGINE` extends the simulator's engine (`BB.xsWord`, `BB.xsNext`, `BB.xsRun`, `BB.xsSweep`, `BB.pat`,
`BB.Zone`), in a script of its own after it, so that tools/tests can run the two in Node; tools/tests/test_tools.py checks it against the real machines
and against the state that Lean computes at zone step 3 * 10^7.
"""

XS_ENGINE = r"""
(function (BB) {
  "use strict";
  var Run = BB.Run;
  // ---- XOR sweep machines (family F08, the 111110 block) ----
  // `xc` = {state, off}: a turn at the right end has the head in `state`, the pair 11 under it starting at
  // head + off (off is 0 or -1), blank tape to the right of that pair, and pairs (b, 1) to its left.
  // Words are arrays of 0/1 read left to right on the tape; the last letter is the head pair (always 1).
  function xsWord(r, xc) {
    if (r.halted || r.state !== xc.state) return null;
    var p = r.head + xc.off;
    if (r.get(p) !== 1 || r.get(p + 1) !== 1) return null;
    for (var q = p + 2; q <= r.hi + 1; q++) if (r.get(q) !== 0) return null;
    var w = [];
    for (q = p; ; q -= 2) {
      if (r.get(q + 1) !== 1) break;
      w.push(r.get(q));
    }
    for (var e = q + 1; e >= r.lo - 1; e--) if (r.get(e) !== 0) return null;
    return w.reverse();
  }
  // Steps the run (at least one step) to the next turn at the right end; returns the word, or null on a halt
  // or when `max` steps have passed.
  function xsNext(r, xc, max) {
    var stop = r.steps + (max || 1e9), w;
    do { if (!r.step()) return null; w = xsWord(r, xc); } while (w === null && r.steps < stop);
    return w;
  }
  // A run whose tape is the word `w` at a turn at the right end.
  function xsRun(m, xc, w) {
    var r = new Run(m), L = 2 * w.length + 8;
    r.cells = new Uint8Array(3 * L + 64); r.off = L + 32;
    for (var i = w.length - 1; i >= 0; i--) { r.cells[r.off - 2 * (w.length - 1 - i)] = w[i]; r.cells[r.off - 2 * (w.length - 1 - i) + 1] = 1; }
    r.head = -xc.off; r.state = xc.state; r.lo = -2 * (w.length - 1); r.hi = 1;
    if (r.head > r.hi) r.hi = r.head;
    var n1 = 0; for (i = 0; i < w.length; i++) n1 += 1 + w[i]; r.nOnes = n1;
    return r;
  }
  // One XOR sweep of the word u (left to right), without the letters it appends: returns {kind: "ok", i, d, x}
  // where (i, i + 1) is the rightmost 00, d = u.length - 2 - i letters stand right of it, and x (one letter
  // shorter than u) is u with u[i-1] flipped and u[k] replaced by u[k] xor u[k+1] for k > i.  The new word is
  // x ++ [1, 1].  {kind: "halt"} when the only 00 is at the very left; {kind: "reset"} when there is none.
  function xsSweep(u) {
    var L = u.length, i = L - 2;
    while (i >= 0 && !(u[i] === 0 && u[i + 1] === 0)) i--;
    if (i < 0) return { kind: "reset" };
    if (i === 0) return { kind: "halt", i: 0, d: L - 2 };
    var x = u.slice(0, L - 1);
    x[i - 1] ^= 1;
    for (var k = i + 1; k <= L - 2; k++) x[k] = u[k] ^ u[k + 1];
    return { kind: "ok", i: i, d: L - 2 - i, x: x };
  }
  // The block letters: pat(k) = 1 unless k = 2 mod 3; the reversed word at a turn is pat(0) pat(1) ... (head
  // first) along the block.
  function pat(k) { return k % 3 === 2 ? 0 : 1; }
  // The zone orbit (Lean: `cstep` in lean/Zone.lean): the reversed word is blk(n + 1) ++ Z; z holds Z in tape
  // order (z[z.length - 1] is next to the block).  `cost` is the 12 of 4 (n + d) + 12.
  function Zone(m, xc, cost) {
    this.m = m; this.xc = xc; this.cost = cost; this.t = 0; this.k = 0; this.halted = false;
    var r = new Run(m), w = xsWord(r, xc) || xsNext(r, xc);
    this.t = r.steps; this.load(w);
    this.resets = [];
  }
  Zone.prototype.load = function (w) {
    // w is the whole word; split the block off the reversed word after the head letter (Lean: cpr 1 0)
    var j = w.length - 2, n = 0;
    while (j >= 0 && w[j] === pat(n + 1)) { n++; j--; }
    this.n = n; this.z = w.slice(0, j + 1);
  };
  Zone.prototype.word = function () {
    var w = this.z.slice();
    for (var k = this.n; k >= 1; k--) w.push(pat(k));
    w.push(1);
    return w;
  };
  // One step: returns "ok" (d = depth of the 00 in the zone, counted from the block), "reset" or "halt".
  Zone.prototype.step = function () {
    if (this.halted) return "halt";
    var z = this.z, L = z.length + 1, p = pat(this.n), i = L - 2, get = function (q) { return q === L - 1 ? p : z[q]; };
    while (i >= 0 && !(get(i) === 0 && get(i + 1) === 0)) i--;
    this.k++;
    if (i > 0) {
      var d = L - 2 - i;
      z[i - 1] ^= 1;
      for (var q = i + 1; q <= L - 2; q++) z[q] ^= get(q + 1);
      this.t += 4 * (this.n + d) + this.cost; this.n++; this.d = d;
      return "ok";
    }
    if (i === 0) { this.halted = true; this.d = L - 2; return "halt"; }
    // no 00: a reset; the real machine decides what comes next
    var r = xsRun(this.m, this.xc, this.word()), w = xsNext(r, this.xc);
    if (w === null) { this.halted = true; this.t += r.steps; return "halt"; }
    this.t += r.steps; this.d = z.length; this.resets.push([this.k, this.t]); this.load(w);
    return "reset";
  };
  BB.xsWord = xsWord; BB.xsNext = xsNext; BB.xsRun = xsRun; BB.xsSweep = xsSweep; BB.pat = pat; BB.Zone = Zone;
})(BB);
"""

XS_UI = r"""
(function () {
  "use strict";
  var spec = JSON.parse(document.getElementById("spec").textContent), X = spec.xs;
  if (!X || !document.querySelector("[data-xs]")) return;
  var M = BB.parse(spec.machine), XC = { state: BB.STATES.indexOf(X.state), off: X.off }, COST = X.cost, pat = BB.pat;
  var fmt = function (n) { return n.toLocaleString("en-US"); };
  var css = function (v) { return getComputedStyle(document.documentElement).getPropertyValue(v).trim(); };
  function sci(x) {
    if (x < 1e7) return fmt(x);
    var e = Math.floor(Math.log10(x)), m = x / Math.pow(10, e);
    return m.toFixed(2) + "&middot;10<sup>" + e + "</sup>";
  }
  function el(html) { var d = document.createElement("div"); d.innerHTML = html; return d.firstElementChild; }
  function q(box, sel) { return box.querySelector(sel); }
  // the turns at the right end of the real machine, from blank tape, cached: turn(k) for k = 1, 2, ...
  var TC = { r: new BB.Run(M), list: [] };
  function turn(k) {
    while (TC.list.length < k) {
      var w = BB.xsNext(TC.r, XC, 1e8);
      if (!w) return null;
      TC.list.push({ w: w, t: TC.r.steps });
    }
    return TC.list[k - 1];
  }
  // the parts of a word: zone w[0, zl), block w[zl, zl + n), head letter w[L - 1] (Lean: cpr 1 0)
  function parts(w) {
    var j = w.length - 2, n = 0;
    while (j >= 0 && w[j] === pat(n + 1)) { n++; j--; }
    return { n: n, zl: j + 1 };
  }
  function roleOf(p, k, L) { return k === L - 1 ? "hd" : k >= p.zl ? "bl" : "zn"; }
  // a word as letters; cls(k) gives extra classes, tip(k) a title; long words keep the ranges in `keep`
  function strip(w, cls, tip, keep) {
    var L = w.length, show = new Uint8Array(L), out = "", gap = 0;
    if (L <= 140) show.fill(1);
    else {
      (keep || []).concat([[0, 12], [L - 60, L]]).forEach(function (r) {
        for (var k = Math.max(0, r[0]); k < Math.min(L, r[1]); k++) show[k] = 1;
      });
    }
    for (var k = 0; k < L; k++) {
      if (!show[k]) { gap++; continue; }
      if (gap) { out += '<span class="xgap">&hellip;' + fmt(gap) + "&hellip;</span>"; gap = 0; }
      var t = tip ? tip(k) : "";
      out += '<span class="xl x' + w[k] + " " + (cls ? cls(k) : "") + '" data-k="' + k + '"' + (t ? ' title="' + t + '"' : "") + ">" + w[k] + "</span>";
    }
    if (gap) out += '<span class="xgap">&hellip;' + fmt(gap) + "&hellip;</span>";
    return out;
  }
  function zstr(a) { return a.length > 90 ? a.slice(0, 40).join("") + "&hellip;(" + fmt(a.length - 80) + ")&hellip;" + a.slice(-40).join("") : a.join(""); }

  // ---- 1. one moment at every layer ----
  function layers(box) {
    box.innerHTML = '<div class="controls"><button type="button" data-a="-1" aria-label="previous turn">&lsaquo;</button>' +
      '<input type="range" min="1" max="1000" value="150" aria-label="turn at the right end"><button type="button" data-a="1" aria-label="next turn">&rsaquo;</button>' +
      '<button type="button" class="primary" data-a="play">Play</button><span class="small">turn <b class="xk mono"></b> at the right end, machine step <b class="xt mono"></b></span></div>' +
      '<div class="xlayers">' +
      '<div class="xrow"><span class="xlab">1 &middot; Cells</span><div class="xcvw"><canvas class="xcv" aria-label="the tape at this turn, cell by cell, with the pairs and their letters"></canvas></div></div>' +
      '<div class="xrow"><span class="xlab">2 &middot; Letters</span><div class="xw xletters"></div></div>' +
      '<div class="xrow"><span class="xlab">3 &middot; Parts</span><div class="xparts"></div></div>' +
      '<div class="xrow"><span class="xlab">4 &middot; Zone state</span><div class="xstate mono"></div></div></div>' +
      '<div class="cap">Layer 1 is the real tape, simulated in your browser from blank tape. Each pair of cells under a bracket is one letter (layer 2): <code>11</code> is 1, <code>01</code> is 0. Blue letters are the zone, green ones the block, orange the head&rsquo;s pair. Layer 3 counts them; layer 4 is what the zone orbit keeps: the block&rsquo;s length and the zone. Drag the slider or press Play.</div>';
    var rng = q(box, "input"), timer = 0;
    function draw() {
      var k = +rng.value, T = turn(k);
      if (!T) return;
      var w = T.w, L = w.length, p = parts(w);
      q(box, ".xk").textContent = fmt(k); q(box, ".xt").textContent = fmt(T.t);
      // cells
      var cv = q(box, ".xcv"), wrap = q(box, ".xcvw"), W = wrap.clientWidth || 600, nc = 2 * L + 2;
      var cs = Math.max(3, Math.min(14, Math.floor(W / nc))), dpr = window.devicePixelRatio || 1;
      var cw = nc * cs, ch = 64;
      cv.width = cw * dpr; cv.height = ch * dpr; cv.style.width = cw + "px"; cv.style.height = ch + "px";
      var g = cv.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, cw, ch);
      var ink = css("--ink"), c0 = css("--cell0"), line = css("--line-strong"), head = css("--head");
      var col = { zn: css("--native"), bl: css("--kernel"), hd: head };
      var y0 = 16, hh = 12;
      for (var c = 0; c < 2 * L; c++) {
        var letter = Math.floor(c / 2), v = c % 2 ? 1 : w[letter];
        g.fillStyle = v ? ink : c0; g.fillRect(c * cs + 0.5, y0, cs - 1, hh);
        if (!v && cs >= 4) { g.strokeStyle = line; g.lineWidth = 1; g.strokeRect(c * cs + 1, y0 + 0.5, cs - 2, hh - 1); }
      }
      var hc = 2 * (L - 1) - XC.off;
      g.fillStyle = head; g.beginPath(); g.moveTo(hc * cs + cs / 2, y0 - 2); g.lineTo(hc * cs + cs / 2 - 4, y0 - 9); g.lineTo(hc * cs + cs / 2 + 4, y0 - 9); g.fill();
      g.font = "700 10px " + css("--mono"); g.textAlign = "center"; g.fillText(X.state, hc * cs + cs / 2 + (hc * cs > 12 ? -10 : 10), y0 - 6);
      for (var a = 0; a < L; a++) {
        var r = roleOf(p, a, L), x = 2 * a * cs;
        g.fillStyle = col[r]; g.fillRect(x + 1, y0 + hh + 4, 2 * cs - 2, 3);
        if (cs >= 5) {
          g.fillStyle = col[r]; g.font = "600 " + Math.min(12, 2 * cs - 2) + "px " + css("--mono");
          g.fillText(String(w[a]), x + cs, y0 + hh + 20);
        }
      }
      wrap.scrollLeft = wrap.scrollWidth;
      q(box, ".xletters").innerHTML = strip(w, function (k) { return roleOf(p, k, L); });
      q(box, ".xparts").innerHTML = '<span class="xp zn">zone &middot; ' + fmt(p.zl) + ' letters</span><span class="xp bl">block &middot; ' + fmt(p.n) +
        ' letters <span class="mono">' + (p.n ? (p.n > 9 ? "&hellip;" : "") + w.slice(Math.max(p.zl, L - 1 - 9), L - 1).join("") : "") + '</span></span><span class="xp hd">head &middot; 1</span>';
      var Z = w.slice(0, p.zl).reverse();
      q(box, ".xstate").innerHTML = "n = " + fmt(p.n) + " &nbsp;(n mod 3 = " + (p.n % 3) + ") &nbsp; Z = " + (Z.length ? zstr(Z) : "(empty)") +
        ' <span class="small">(Z is read from the block outwards)</span>';
    }
    rng.oninput = draw;
    box.querySelectorAll("button[data-a]").forEach(function (b) {
      b.onclick = function () {
        if (b.dataset.a === "play") {
          if (timer) { clearInterval(timer); timer = 0; b.textContent = "Play"; return; }
          b.textContent = "Pause";
          timer = setInterval(function () { if (+rng.value >= +rng.max) { clearInterval(timer); timer = 0; b.textContent = "Play"; return; } rng.value = +rng.value + 1; draw(); }, 140);
          return;
        }
        rng.value = Math.max(1, Math.min(+rng.max, +rng.value + +b.dataset.a)); draw();
      };
    });
    window.addEventListener("resize", draw);
    draw();
  }

  // ---- 2. one sweep, stage by stage ----
  function sweep(box) {
    box.innerHTML = '<div class="controls"><label class="small">turn <input type="text" class="xturn" inputmode="numeric" value="25" style="width:6em"></label>' +
      '<button type="button" data-a="load">Load</button><label class="small">or a word <input type="text" class="xword" value="1101001101011" spellcheck="false" autocomplete="off"></label>' +
      '<button type="button" data-a="word">Use it</button></div>' +
      '<div class="controls" style="margin-top:8px"><button type="button" data-a="back">&lsaquo; Back</button><button type="button" class="primary" data-a="fwd">Next stage &rsaquo;</button>' +
      '<button type="button" data-a="all">All stages</button><button type="button" data-a="next">Apply and go to the next turn</button></div>' +
      '<ol class="xstages"></ol><div class="xcheck"></div>' +
      '<div class="cap">Hover a letter in the XOR row to see the two letters it comes from. Long words are shortened in the middle; the parts that change are always shown. The check at the bottom puts the word on a tape, runs the real machine until its head is back at the right end, and reads the word off again.</div>';
    var u = null, k = 0, stage = 0, S = null;
    function setWord(w, kk) { u = w; k = kk; S = BB.xsSweep(u); stage = 0; draw(); }
    function draw() {
      var L = u.length, ol = q(box, ".xstages"), html = "", i = S.i, keep = S.kind === "ok" || S.kind === "halt" ? [[i - 14, i + 16]] : [];
      var p = parts(u);
      var base = function (k) { return roleOf(p, k, L); };
      var desc = k ? "Turn " + fmt(k) + " of the real run" : "Your word";
      html += '<li class="on"><span class="xlab">' + desc + "</span><div class=\"xw\">" + strip(u, function (j) {
        var c = base(j);
        if (S.kind !== "reset" && (j === i || j === i + 1)) c += " hz";
        if (S.kind === "ok" && j === i - 1) c += " hfo";
        if (S.kind === "ok" && j > i) c += " hxr";
        return c;
      }, null, keep) + "</div><p class=\"small\">" + (S.kind === "reset" ? "There is no <code>00</code> anywhere: the pass will run off the left end of the word (a <b>reset</b>). The XOR rule does not cover this; the machine itself decides, see the check below." :
        S.kind === "halt" ? "The only <code>00</code> is the first two letters: the pass reaches the left end with nothing to flip, and <b>the machine halts</b>." :
        "Find the rightmost <code>00</code> (outlined): it is at letters " + fmt(i + 1) + "&ndash;" + fmt(i + 2) + ", with d = " + fmt(S.d) + " letters right of it.") + "</p></li>";
      if (S.kind === "ok") {
        var f = u.slice(); f[i - 1] ^= 1;
        var xw = f.slice(); for (var j = i + 1; j < L; j++) xw[j] = f[j] ^ (j + 1 < L ? f[j + 1] : 0);
        var fin = xw.concat([1]);
        var rows = [
          ["Flip", strip(f, function (j) { return base(j) + (j === i - 1 ? " hf" : j === i || j === i + 1 ? " hz" : ""); }, null, keep),
            "Flip the letter just left of the <code>00</code>: " + u[i - 1] + " becomes " + f[i - 1] + "."],
          ["XOR", strip(xw, function (j) { return base(j) + (j > i ? " hx" : j === i - 1 ? " hf" : ""); },
            function (j) { return j > i ? (f[j] + " xor " + (j + 1 < L ? f[j + 1] : "0 (past the end)") + " = " + xw[j]) : ""; }, keep),
            "Replace every letter right of the <code>00</code> by itself XOR its right neighbour (past the end counts as 0, so the head&rsquo;s 1 stays). " +
            "Inside the block, <code>&hellip;110110</code> becomes <code>&hellip;011011</code>: the same pattern, moved by one."],
          ["Append", strip(fin, function (j) { return j === L ? "hd ha" : (j > i ? "hx" : ""); }, null, keep),
            "Append a new head letter 1 (the pair <code>11</code>): the tape is one pair longer. This is the next turn&rsquo;s word."]
        ];
        rows.forEach(function (rw, n) {
          html += '<li class="' + (stage > n ? "on" : "off") + '"><span class="xlab">' + (n + 1) + " &middot; " + rw[0] + '</span><div class="xw"' + (n === 1 ? ' data-x="1"' : "") + ">" + rw[1] + '</div><p class="small">' + rw[2] + "</p></li>";
        });
      }
      ol.innerHTML = html;
      // light cone: hovering a letter of the XOR row lights its two inputs in the flip row
      var xr = ol.querySelector('[data-x="1"]'), fr = ol.children[1] && ol.children[1].querySelector(".xw");
      if (xr && fr) xr.querySelectorAll(".xl").forEach(function (s) {
        s.onmouseenter = function () { var j = +s.dataset.k; fr.querySelectorAll(".xl").forEach(function (t) { var tk = +t.dataset.k; t.classList.toggle("lit", tk === j || (j > i && tk === j + 1)); }); };
        s.onmouseleave = function () { fr.querySelectorAll(".lit").forEach(function (t) { t.classList.remove("lit"); }); };
      });
      // the real machine
      var r = BB.xsRun(M, XC, u), w2 = BB.xsNext(r, XC, 50 * L * L + 1e5), ck = q(box, ".xcheck");
      if (!w2) { ck.innerHTML = '<p class="xok' + (S.kind === "halt" ? "" : " bad") + '">The real machine ' + (r.halted ? "halts after " + fmt(r.steps) + " steps" : "did not come back") + (S.kind === "halt" ? ", as predicted." : ".") + "</p>"; return; }
      if (S.kind === "ok") {
        var same = w2.join("") === u.slice(0, 0).concat(fin).join(""), st = 4 * S.d + COST;
        ck.innerHTML = '<p class="xok' + (same && r.steps === st ? "" : " bad") + '">' + (same && r.steps === st ? "&#10003; " : "&#10007; ") +
          "The real machine, run from this tape, is back at the right end after <b>" + fmt(r.steps) + "</b> steps with exactly this word" + (same ? "" : " (it differs!)") +
          ". The rule predicts 4&middot;d + " + COST + " = 4&middot;" + fmt(S.d) + " + " + COST + " = <b>" + fmt(st) + "</b> steps.</p>";
      } else ck.innerHTML = '<p class="xok">The real machine handles this reset itself: it is back at the right end after <b>' + fmt(r.steps) + "</b> steps, with the word " +
        '<span class="mono">' + zstr(w2) + "</span> (" + fmt(w2.length) + " letters).</p>";
      box._next = w2;
    }
    box.querySelectorAll("button[data-a]").forEach(function (b) {
      b.onclick = function () {
        var a = b.dataset.a;
        if (a === "load") { var kk = Math.max(1, Math.min(20000, parseInt(q(box, ".xturn").value, 10) || 1)); q(box, ".xturn").value = kk; setWord(turn(kk).w, kk); }
        else if (a === "word") {
          var s = q(box, ".xword").value.replace(/[^01]/g, "");
          if (!s.length) return;
          if (s[s.length - 1] !== "1") s += "1";
          q(box, ".xword").value = s; setWord(s.split("").map(Number), 0);
        }
        else if (a === "fwd") { stage = Math.min(3, stage + 1); draw(); }
        else if (a === "back") { stage = Math.max(0, stage - 1); draw(); }
        else if (a === "all") { stage = 3; draw(); }
        else if (a === "next" && box._next) { if (k) q(box, ".xturn").value = k + 1; setWord(box._next, k ? k + 1 : 0); }
      };
    });
    setWord(turn(25).w, 25);
  }

  // ---- 3. the block's length matters only mod 3 ----
  function block(box) {
    var T = turn(30), p0 = parts(T.w), Z0 = T.w.slice(0, p0.zl);
    box.innerHTML = '<div class="controls"><label class="small">block length m <input type="range" min="1" max="40" value="7"></label><b class="xm mono"></b>' +
      '<label class="small">zone <input type="text" class="xz" value="' + Z0.join("") + '" spellcheck="false" autocomplete="off" style="width:16em"></label><button type="button" data-a="z">Use it</button></div>' +
      '<div class="xtab"></div><div class="cap">Each row is the word &laquo;zone, block of m letters, head&raquo; for one block length, swept once. The zone part of the result is the same in rows whose m differ by 3, and only the leftmost block letter, <code>pat(m)</code>, reaches the zone. The default zone is the real one at turn 30.</div>';
    var rng = q(box, "input[type=range]"), Z = Z0;
    function draw() {
      var m = +rng.value, html = '<table class="xbt"><thead><tr><th>m</th><th>m mod 3</th><th>before</th><th>after one sweep</th><th>zone after</th></tr></thead><tbody>', zs = [];
      q(box, ".xm").textContent = m;
      for (var mm = m; mm <= m + 3; mm++) {
        var w = Z.slice(); for (var k = mm; k >= 1; k--) w.push(pat(k)); w.push(1);
        var S = BB.xsSweep(w), zl = Z.length, L = w.length;
        var cls = function (j) { return j === L - 1 ? "hd" : j >= zl ? "bl" : "zn"; };
        var after = "", za = "";
        if (S.kind === "ok") {
          var x = S.x.concat([1, 1]);
          after = strip(x, function (j) { return j === x.length - 1 || j === x.length - 2 && false ? "hd" : j >= zl ? "bl" : "zn"; });
          za = x.slice(0, zl).join("");
        } else after = S.kind === "halt" ? "halt" : "reset (no 00 in the zone and the block&rsquo;s edge)";
        zs.push(za);
        html += "<tr><td class=\"mono\">" + mm + "</td><td class=\"mono\">" + (mm % 3) + '</td><td><div class="xw sm">' + strip(w, cls) + '</div></td><td><div class="xw sm">' + after +
          '</div></td><td class="mono">' + (za || "&mdash;") + (mm === m + 3 ? (za === zs[0] ? ' <span class="xok">&#10003; same as m = ' + m + "</span>" : ' <span class="xok bad">differs</span>') : "") + "</td></tr>";
      }
      q(box, ".xtab").innerHTML = html + "</tbody></table>";
    }
    rng.oninput = draw;
    q(box, "button[data-a=z]").onclick = function () { var s = q(box, ".xz").value.replace(/[^01]/g, ""); Z = s.split("").map(Number); draw(); };
    draw();
  }

  // ---- 4. the zone orbit, run in the browser ----
  function orbit(box) {
    var targets = [[1e4, "10<sup>4</sup>"], [1e5, "10<sup>5</sup>"], [1e6, "10<sup>6</sup>"], [1e7, "10<sup>7</sup>"], [3e7, "3&middot;10<sup>7</sup>"]];
    box.innerHTML = '<div class="controls"><span class="small">Run the zone orbit to step</span>' + targets.map(function (t) { return '<button type="button" data-t="' + t[0] + '">' + t[1] + "</button>"; }).join("") +
      '<button type="button" data-a="stop">Stop</button></div>' +
      '<div class="readout"><span>zone step <b class="ok_k">0</b></span><span>machine step <b class="ok_t">0</b></span><span>block n <b class="ok_n">0</b></span><span>zone <b class="ok_z">0</b> letters</span><span>resets <b class="ok_r">0</b></span></div>' +
      '<div class="xbar" aria-label="the parts of the tape now"></div>' +
      '<h3>How deep each sweep goes</h3><div class="stwrap"><canvas class="xdep" aria-label="depth of the sweeps against zone step, log scales"></canvas></div>' +
      '<div class="cap">x: zone step (one per round trip of the head), log scale. y: how far into the zone the sweep found its <code>00</code>, in letters, log scale; for each column the deepest sweep is drawn. Red lines are resets, sweeps that found no <code>00</code> and ran to the left end of the tape.</div>' +
      '<div class="xst"><div><h3>Next to the block, the first 400 sweeps</h3><div class="stwrap"><canvas class="xnear"></canvas></div><div class="cap xncap">One row per sweep, time going down: the 96 letters of the zone next to the block (the block is on the right). Dark = 1, grey = no zone there yet.</div></div>' +
      '<div><h3>At the left end, every sweep that changed it</h3><div class="stwrap"><canvas class="xleft"></canvas></div><div class="cap xlcap">Once the zone is longer than 192 letters: one row per sweep that changed one of the 96 leftmost letters of the tape (the left end is on the left); red rows are resets.</div></div></div>' +
      '<div class="log xrs"></div>';
    var Z = new BB.Zone(M, XC, COST), NB = 560, LX = 7.6, bins = new Float64Array(NB), rst = new Uint8Array(NB), W = 96, near = [], left = [], running = 0, target = 0, resets = [];
    function snapRight() { var z = Z.z, a = new Uint8Array(W).fill(2); for (var j = 0; j < Math.min(W, z.length); j++) a[W - 1 - j] = z[z.length - 1 - j]; return a; }
    function snapLeft() { var z = Z.z, a = new Uint8Array(W).fill(2); for (var j = 0; j < Math.min(W, z.length); j++) a[j] = z[j]; return a; }
    function post(res) {
      var k = Z.k, b = Math.min(NB - 1, Math.floor(Math.log10(k) / LX * NB)), z = Z.z;
      if (res === "reset") { rst[b] = 1; resets.push([k, Z.t, z.length, Z.n]); if (z.length > 2 * W) left.push([k, snapLeft(), 1]); }
      else if (res === "ok") {
        if (Z.d + 2 > bins[b]) bins[b] = Z.d + 2;
        if (z.length - 2 - Z.d < W && z.length > 2 * W && left.length < 600) left.push([k, snapLeft(), 0]);
      }
      if (near.length < 400) near.push([k, snapRight(), res === "reset" ? 1 : 0]);
    }
    function grid(cv, rows, w) {
      var cs = 4, rh = Math.max(2, Math.min(10, Math.floor(400 / Math.max(1, rows.length)))), H = Math.max(1, rows.length) * rh;
      cv._rows = rows; cv._rh = rh;
      cv.width = w * cs; cv.height = H; cv.style.width = w * cs + "px"; cv.style.height = H + "px";
      var g = cv.getContext("2d"), ink = css("--ink"), c0 = css("--cell0"), red = css("--open"), sunk = css("--sunk");
      g.fillStyle = c0; g.fillRect(0, 0, w * cs, H);
      rows.forEach(function (r, y) {
        for (var x = 0; x < w; x++) {
          var v = r[1][x];
          if (v === 2) { g.fillStyle = sunk; g.fillRect(x * cs, y * rh, cs, rh); }
          else if (v) { g.fillStyle = ink; g.fillRect(x * cs, y * rh, cs, rh); }
        }
        if (r[2]) { g.fillStyle = red; g.globalAlpha = 0.5; g.fillRect(0, y * rh, w * cs, rh); g.globalAlpha = 1; }
      });
    }
    function depth() {
      var cv = q(box, ".xdep"), Wd = Math.max(320, Math.min(760, (cv.parentNode.clientWidth || 700))), H = 220, pl = 46, pb = 26, dpr = window.devicePixelRatio || 1;
      cv.width = Wd * dpr; cv.height = H * dpr; cv.style.width = Wd + "px"; cv.style.height = H + "px";
      var g = cv.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, Wd, H);
      var maxd = 1; for (var b = 0; b < NB; b++) if (bins[b] > maxd) maxd = bins[b];
      var LY = Math.max(4, Math.ceil(Math.log2(Math.max(maxd, Z.z.length + 2)))), pw = Wd - pl - 8, ph = H - pb - 8;
      g.font = "10px " + css("--mono"); g.fillStyle = css("--muted"); g.strokeStyle = css("--line"); g.lineWidth = 1;
      for (var e = 0; e <= 7; e++) { var x = pl + e / LX * pw; g.beginPath(); g.moveTo(x, 8); g.lineTo(x, 8 + ph); g.stroke(); g.textAlign = "center"; g.fillText("10^" + e, x, H - 8); }
      for (var yv = 0; yv <= LY; yv += Math.max(1, Math.round(LY / 6))) { var y = 8 + ph - yv / LY * ph; g.beginPath(); g.moveTo(pl, y); g.lineTo(pl + pw, y); g.stroke(); g.textAlign = "right"; g.fillText(String(Math.pow(2, yv)), pl - 4, y + 3); }
      g.fillStyle = css("--accent");
      for (b = 0; b < NB; b++) if (bins[b]) { var hy = Math.log2(bins[b]) / LY * ph; g.fillRect(pl + b / NB * pw, 8 + ph - hy, Math.max(1, pw / NB), Math.max(1, hy)); }
      g.fillStyle = css("--open");
      for (b = 0; b < NB; b++) if (rst[b]) g.fillRect(pl + b / NB * pw, 8, 1.5, ph);
      // zone length
      g.strokeStyle = css("--muted"); g.setLineDash([4, 3]); var zy = 8 + ph - Math.log2(Z.z.length + 1) / LY * ph; g.beginPath(); g.moveTo(pl, zy); g.lineTo(pl + pw, zy); g.stroke(); g.setLineDash([]);
      g.fillStyle = css("--muted"); g.textAlign = "right"; g.fillText("zone length now", pl + pw - 2, zy - 4);
    }
    // the parts of the zone now: a period-3 stretch of 30 letters or more is a stranded block
    function bar() {
      var z = Z.z, L = z.length, a = -1, b = -1, j = L - 4;
      while (j >= 0) {
        if (z[j] === z[j + 3]) { var e = j; while (j >= 0 && z[j] === z[j + 3]) j--; if (e - j >= 30) { a = j + 1; b = e + 3; break; } }
        else j--;
      }
      var segs = a < 0 ? [["zn", "zone", L]] : [["old", "old zone", a], ["str", "stranded block", b - a + 1], ["zn", "new zone", L - 1 - b]];
      segs.push(["bl", "growing block", Z.n], ["hd", "head", 1]);
      var tot = 0; segs.forEach(function (s) { s.w = 1 + Math.log10(1 + s[2]); tot += s.w; });
      q(box, ".xbar").innerHTML = segs.map(function (s) { return '<div class="' + s[0] + '" style="flex:' + s.w.toFixed(3) + '"><b>' + s[1] + "</b><span>" + fmt(s[2]) + "</span></div>"; }).join("") ;
    }
    function draw() {
      q(box, ".ok_k").textContent = fmt(Z.k); q(box, ".ok_t").innerHTML = sci(Z.t); q(box, ".ok_n").textContent = fmt(Z.n);
      q(box, ".ok_z").textContent = fmt(Z.z.length); q(box, ".ok_r").textContent = fmt(resets.length) + (Z.halted ? " (halted!)" : "");
      depth(); bar(); grid(q(box, ".xnear"), near, W); grid(q(box, ".xleft"), left, W);
      q(box, ".xrs").innerHTML = resets.map(function (r) { return "<div><span>zone step " + fmt(r[0]) + "</span><span></span><span></span><span>machine step " + sci(r[1]).replace(/<[^>]+>/g, function (t) { return t === "<sup>" ? "^" : ""; }) + ": a sweep found no 00 and ran to the left end; zone now " + fmt(r[2]) + " letters, block " + fmt(r[3]) + "</span></div>"; }).join("");
    }
    function tick() {
      var stop = performance.now() + 30;
      while (Z.k < target && !Z.halted && performance.now() < stop) for (var c = 0; c < 4000 && Z.k < target && !Z.halted; c++) post(Z.step());
      draw();
      if (Z.k < target && !Z.halted && running) requestAnimationFrame(tick); else running = 0;
    }
    box.querySelectorAll("button").forEach(function (b) {
      b.onclick = function () {
        if (b.dataset.a === "stop") { running = 0; return; }
        target = +b.dataset.t; if (!running) { running = 1; requestAnimationFrame(tick); }
      };
    });
    [[".xnear", ".xncap"], [".xleft", ".xlcap"]].forEach(function (c) {
      var cv = q(box, c[0]), cap = q(box, c[1]), txt = cap.innerHTML;
      cv.onmousemove = function (e) {
        var rows = cv._rows || [], y = Math.floor((e.clientY - cv.getBoundingClientRect().top) / (cv._rh || 2)), r = rows[y];
        cap.innerHTML = r ? "Row " + (y + 1) + ": zone step <b>" + fmt(r[0]) + "</b>" + (r[2] ? " (a reset)" : "") + "." : txt;
      };
      cv.onmouseleave = function () { cap.innerHTML = txt; };
    });
    target = 1e4; running = 1; requestAnimationFrame(tick);
    window.addEventListener("resize", depth);
  }

  var W = { layers: layers, sweep: sweep, block: block, orbit: orbit };
  document.querySelectorAll("[data-xs]").forEach(function (box) { if (W[box.dataset.xs]) W[box.dataset.xs](box); });
})();
"""

XS_CSS = """
.xlayers{display:grid;gap:10px;margin-top:14px}
.xrow{display:grid;grid-template-columns:8.5em minmax(0,1fr);gap:12px;align-items:start}
.xlab{font:600 .74rem/1.3 var(--body);letter-spacing:.06em;text-transform:uppercase;color:var(--muted);padding-top:4px}
.xcvw{overflow-x:auto}
.xw{display:flex;flex-wrap:wrap;gap:2px;font-family:var(--mono);font-size:.8rem;line-height:1}
.xw.sm{font-size:.7rem}
.xl{display:inline-block;min-width:1.25em;text-align:center;padding:3px 0;border-radius:3px;border:1px solid var(--line);background:var(--surface)}
.xl.x1{font-weight:700}
.xl.zn{color:var(--native);border-color:var(--native);background:var(--native-bg)}
.xl.bl{color:var(--kernel);border-color:var(--kernel);background:var(--kernel-bg)}
.xl.hd{color:var(--surface);border-color:var(--head);background:var(--head)}
.xl.hz{outline:2px solid var(--open);outline-offset:1px}
.xl.hfo{outline:2px dashed var(--computed);outline-offset:1px}
.xl.hf{color:var(--surface);background:var(--computed);border-color:var(--computed)}
.xl.hxr{box-shadow:inset 0 -3px 0 var(--heur)}
.xl.hx{color:var(--surface);background:var(--heur);border-color:var(--heur)}
.xl.ha{outline:2px solid var(--head);outline-offset:1px}
.xl.lit{outline:3px solid var(--fg);outline-offset:1px}
.xgap{color:var(--muted);padding:3px 4px;font-size:.75rem}
.xparts{display:flex;flex-wrap:wrap;gap:6px}
.xp{font-size:.84rem;border-radius:6px;padding:2px 8px;border:1px solid var(--line)}
.xp.zn{color:var(--native);background:var(--native-bg)} .xp.bl{color:var(--kernel);background:var(--kernel-bg)}
.xp.hd{color:var(--surface);background:var(--head)}
.xstate{font-size:.82rem;overflow-wrap:anywhere;padding-top:3px}
.xstages{list-style:none;padding:0;margin:14px 0 0;display:grid;gap:10px}
.xstages li{display:grid;grid-template-columns:8.5em minmax(0,1fr);gap:4px 12px;transition:opacity .2s}
.xstages li p{grid-column:2;margin:.1rem 0}
.xstages li.off{opacity:.18}
.xok{color:var(--kernel);font-weight:600} .xok.bad{color:var(--open)}
.xcheck{margin-top:12px;border-top:1px solid var(--line);padding-top:8px}
.xtab{overflow-x:auto}
.xbt td{vertical-align:middle}
.xbt td:nth-child(3),.xbt td:nth-child(4){min-width:12em}
.xbar{display:flex;gap:3px;margin:14px 0 6px;min-height:48px}
.xbar div{border-radius:6px;padding:4px 6px;font-size:.74rem;min-width:0;overflow:hidden;display:flex;flex-direction:column;justify-content:center}
.xbar div b{font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis} .xbar div span{font-family:var(--mono)}
.xbar .old{background:var(--open-bg);color:var(--open)} .xbar .str{background:var(--computed-bg);color:var(--computed)}
.xbar .zn{background:var(--native-bg);color:var(--native)} .xbar .bl{background:var(--kernel-bg);color:var(--kernel)}
.xbar .hd{background:var(--head);color:var(--surface);flex:0 0 auto!important}
.xst{display:grid;grid-template-columns:repeat(auto-fit,minmax(300px,1fr));gap:16px}
.xst>div{min-width:0} .xst .stwrap{max-height:420px;overflow:auto}
.xrs div{grid-template-columns:10em 0 0 minmax(0,1fr)}
.ladder{list-style:none;padding:0;margin:18px 0;display:grid;gap:0;counter-reset:rung}
.ladder li{display:grid;grid-template-columns:2.4em minmax(0,1fr);gap:0 12px;position:relative;padding:0 0 14px}
.ladder li::before{counter-increment:rung;content:counter(rung);grid-row:span 3;width:2.1em;height:2.1em;border-radius:50%;display:flex;align-items:center;justify-content:center;
  font:700 .95rem var(--display);background:var(--accent-soft);color:var(--accent);border:1px solid var(--accent)}
.ladder li:not(:last-child)::after{content:"";position:absolute;left:1.05em;top:2.2em;bottom:0;border-left:2px solid var(--line-strong)}
.ladder b{font-family:var(--display);font-size:1.04rem}
.ladder p{margin:.15rem 0}
.ladder .arrow{font-size:.88rem;color:var(--fg2)}
@media (max-width:560px){ .xrow,.xstages li{grid-template-columns:1fr} .xstages li p{grid-column:1} }
"""
