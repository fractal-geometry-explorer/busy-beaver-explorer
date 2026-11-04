// Engine of the deciders page: a Turing machine simulator and in-browser versions of the deciders used by the
// Busy Beaver Challenge. Each decider follows the algorithm of the cited source (Coq-BB5, the BB(5) paper or
// bbchallenge-deciders); tests in test_engine.js check them against the results those sources report.
// Machines are in the standard text format, e.g. 1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA (state A first, symbol 0 first).
"use strict";
const BB = (() => {
  const L = (i) => String.fromCharCode(65 + i);

  // ---------------------------------------------------------------- machines
  function parse(text) {
    const rows = text.trim().split("_");
    const n = rows.length;
    const tr = [];
    for (let s = 0; s < n; s++) {
      if (rows[s].length !== 6) throw new Error("bad machine " + text);
      for (let r = 0; r < 2; r++) {
        const t = rows[s].slice(3 * r, 3 * r + 3);
        if (t[2] === "-" || t[2] === "Z" || t.indexOf("-") >= 0) { tr.push(null); continue; }
        const ns = t.charCodeAt(2) - 65;
        if (!(t[0] === "0" || t[0] === "1") || !(t[1] === "L" || t[1] === "R") || ns < 0 || ns >= n)
          throw new Error("bad transition " + t + " in " + text);
        tr.push({ w: +t[0], d: t[1] === "R" ? 1 : -1, s: ns });
      }
    }
    return { n, tr, text: text.trim() };
  }
  const trText = (t) => (t ? "" + t.w + (t.d > 0 ? "R" : "L") + L(t.s) : "---");
  function format(m) {
    const out = [];
    for (let s = 0; s < m.n; s++) out.push(trText(m.tr[2 * s]) + trText(m.tr[2 * s + 1]));
    return out.join("_");
  }

  // A run on a tape that grows in both directions.
  class Run {
    constructor(m) {
      this.m = m; this.size = 1024; this.tape = new Uint8Array(this.size); this.off = 512;
      this.pos = 0; this.state = 0; this.steps = 0; this.halted = false; this.lo = 0; this.hi = 0;
    }
    grow() {
      const t = new Uint8Array(this.size * 2), shift = this.size / 2;
      t.set(this.tape, shift); this.tape = t; this.off += shift; this.size *= 2;
    }
    read(p) { const i = p + this.off; return i >= 0 && i < this.size ? this.tape[i] : 0; }
    step() {
      if (this.halted) return false;
      const i = this.pos + this.off, sym = this.tape[i], t = this.m.tr[2 * this.state + sym];
      if (!t) { this.halted = true; this.haltSym = sym; return false; }
      this.tape[i] = t.w; this.pos += t.d; this.state = t.s; this.steps++;
      if (this.pos < this.lo) this.lo = this.pos;
      if (this.pos > this.hi) this.hi = this.pos;
      const j = this.pos + this.off;
      if (j < 2 || j >= this.size - 2) this.grow();
      return true;
    }
    // Runs at most n steps; returns true if the machine halted. Fast path for long runs.
    run(n) {
      const tr = this.m.tr, W = new Int8Array(tr.length), D = new Int8Array(tr.length), S = new Int8Array(tr.length);
      for (let k = 0; k < tr.length; k++) if (tr[k]) { W[k] = tr[k].w; D[k] = tr[k].d; S[k] = tr[k].s; } else S[k] = -1;
      let tape = this.tape, off = this.off, pos = this.pos, st = this.state, steps = this.steps, size = this.size;
      let lo = this.lo, hi = this.hi;
      const end = steps + n;
      while (steps < end) {
        const i = pos + off, k = 2 * st + tape[i];
        if (S[k] < 0) { this.halted = true; this.haltSym = tape[i]; break; }
        tape[i] = W[k]; pos += D[k]; st = S[k]; steps++;
        if (pos < lo) lo = pos; else if (pos > hi) hi = pos;
        const j = pos + off;
        if (j < 2 || j >= size - 2) {
          this.tape = tape; this.off = off; this.size = size; this.grow();
          tape = this.tape; off = this.off; size = this.size;
        }
      }
      this.tape = tape; this.off = off; this.pos = pos; this.state = st; this.steps = steps; this.lo = lo; this.hi = hi;
      return this.halted;
    }
    ones() { let c = 0; for (let p = this.lo; p <= this.hi; p++) c += this.read(p); return c; }
    // The tape between lo and hi with the head shown as [S] before the read cell.
    configStr(lo = this.lo, hi = this.hi) {
      let s = "";
      for (let p = lo; p <= hi; p++) s += (p === this.pos ? (this.halted ? "[H]" : "[" + L(this.state) + "]") : "") + this.read(p);
      return s;
    }
  }

  // Space-time rows: for each step t < n, the tape cells [lo, hi] and the head. Used by the canvas renderer.
  function spaceTime(m, n, width) {
    const r = new Run(m), rows = [];
    for (let t = 0; t < n; t++) {
      rows.push({ pos: r.pos, state: r.state, cells: null, snap: snapshot(r, width) });
      if (!r.step()) { rows.push({ pos: r.pos, state: -1, snap: snapshot(r, width) }); break; }
    }
    return rows;
  }
  function snapshot(r, width) {
    const half = width >> 1, a = new Uint8Array(width);
    for (let k = 0; k < width; k++) a[k] = r.read(k - half);
    return a;
  }

  // -------------------------------------------------------------- Loops
  // Coq-BB5 loop1_decider (Decider_Loop.v): simulate L steps, then look backwards for a transcript suffix of
  // (state, read symbol) pairs repeated twice and rewind it to a point where the head is at the same place
  // (Cycler) or at the edge of the visited tape (Translated Cycler). Only the state, read symbol, head position and
  // whether the stored left/right half tape is empty matter, so that is all we record.
  function loops(m, L) {
    const S = new Int8Array(L + 1), M = new Uint8Array(L + 1), D = new Int32Array(L + 1);
    const LE = new Uint8Array(L + 1), RE = new Uint8Array(L + 1);
    const r = new Run(m);
    let lo = 0, hi = 0; // extent of cells visited before the current step
    for (let t = 0; t <= L; t++) {
      S[t] = r.state; M[t] = r.read(r.pos); D[t] = r.pos;
      // ListES keeps a cell in l (r) once the head has been to its right (left): it is empty iff the head is at or
      // beyond the leftmost (rightmost) visited cell.
      LE[t] = r.pos <= lo ? 1 : 0; RE[t] = r.pos >= hi ? 1 : 0;
      if (t === L) break;
      if (!r.step()) return { result: "halt", steps: t, state: r.state, sym: r.haltSym };
      if (r.pos < lo) lo = r.pos;
      if (r.pos > hi) hi = r.pos;
    }
    // find_loop1: h0 = time L, h1 = L - k, h2 = L - 2k for k = 1, 2, ...
    for (let k = 1; L - 2 * k >= 0; k++) {
      const t0 = L, t1 = L - k, t2 = L - 2 * k;
      if (!(S[t0] === S[t1] && S[t0] === S[t2] && M[t0] === M[t1] && M[t0] === M[t2])) continue;
      const v = verify(t0, t1, k, D[t0] - D[t1]);
      if (v) return { result: "nonhalt", kind: v.kind, period: k, start: v.start, shift: D[t0] - D[t1], L,
        transcript: { S: S.slice(0, L + 1), M: M.slice(0, L + 1), D: D.slice(0, L + 1) } };
    }
    return { result: "unknown", L };

    // verify_loop1: walk the pair (t0 - i, t1 - i) backwards while (state, symbol) agree; once at least k pairs
    // agree, accept at a point where the head positions coincide (dpos = 0) or the earlier head is at the edge.
    function verify(t0, t1, k, dpos) {
      let n = k;
      for (let i = 0; ; i++) {
        const a = t0 - i, b = t1 - i;
        if (b < 0) return null;
        if (!(S[a] === S[b] && M[a] === M[b])) return null;
        if (n === 0) {
          if (dpos === 0) { if (D[b] === D[a]) return { kind: "cycler", start: b }; }
          else if (dpos > 0) { if (RE[b] && D[b] < D[a]) return { kind: "translated cycler (right)", start: b }; }
          else if (LE[b] && D[a] < D[b]) return { kind: "translated cycler (left)", start: b };
        }
        if (n > 0) n--;
        if (b === 0) return null;
      }
    }
  }

  // ------------------------------------------------------------- n-gram CPS
  // The n-gram Closed Position Set decider (paper Algorithm decider-NGramCPS; Coq-BB5 Decider_NGramCPS.v), with the
  // two alphabet augmentations of Coq-BB5: a history of the last k (state, symbol) pairs seen on each cell, and an
  // LRU list of them. Symbols are strings "b" or "b|A0,B1,...". Returns the closed sets when it succeeds.
  function augment(m, mode, k) {
    // Returns step(state, symbol) -> {w, d, s} | null on augmented symbols.
    return (st, sym) => {
      const bar = sym.indexOf("|"), bit = bar < 0 ? +sym : +sym.slice(0, bar);
      const t = m.tr[2 * st + bit];
      if (!t) return null;
      if (mode === "plain") return { w: "" + t.w, d: t.d, s: t.s };
      const hist = bar < 0 || bar === sym.length - 1 ? [] : sym.slice(bar + 1).split(",");
      const me = L(st) + bit;
      let nh;
      if (mode === "hist") nh = [me].concat(hist).slice(0, k);
      else nh = [me].concat(hist.filter((x) => x !== me));
      return { w: t.w + "|" + nh.join(","), d: t.d, s: t.s };
    };
  }
  function ngramCPS(m, n, opts = {}) {
    const mode = opts.mode || "plain", k = opts.k || 0, gas = opts.gas || 5000001;
    const step = augment(m, mode, k);
    const Z = mode === "plain" ? "0" : "0|";
    const key = (g) => g.join(" ");
    const zero = Array(n).fill(Z);
    // L and R as maps from the (n-1)-gram next to the head to the symbols that can extend it.
    const Lx = new Map(), Rx = new Map(), Lset = new Set(), Rset = new Set();
    // As in Coq-BB5 (but not in the paper's pseudo-code), a new n-gram counts as an update: a context visited
    // earlier in the pass may have successors through it.
    const addL = (g) => { const kk = key(g); if (Lset.has(kk)) return false; Lset.add(kk); const s = key(g.slice(1));
      if (!Lx.has(s)) Lx.set(s, []); Lx.get(s).push(g[0]); return true; };
    const addR = (g) => { const kk = key(g); if (Rset.has(kk)) return false; Rset.add(kk); const s = key(g.slice(0, -1));
      if (!Rx.has(s)) Rx.set(s, []); Rx.get(s).push(g[n - 1]); return true; };
    addL(zero); addR(zero);
    const C = new Map(), order = [];
    const ckey = (c) => key(c.l) + " [" + L(c.s) + " " + c.c + "] " + key(c.r);
    const add = (c) => { const kk = ckey(c); if (C.has(kk)) return false; C.set(kk, c); order.push(c); return true; };
    add({ l: zero, r: zero, c: Z, s: 0 });
    let visits = 0, passes = 0;
    const trace = opts.trace ? [] : null;
    while (true) {
      passes++;
      let any = false;
      const V = order.slice();
      while (V.length) {
        if (++visits > gas) return { result: "unknown", reason: "gas", visits, passes };
        const c = V.pop();
        const t = step(c.s, c.c);
        if (!t) return { result: "unknown", reason: "halt", at: ckey(c), visits, passes, L: [...Lset], R: [...Rset], C: order.map(ckey) };
        const news = [];
        if (t.d > 0) {
          if (addL(c.l)) any = true;
          const nl = c.l.slice(1).concat([t.w]), mid = c.r[0], pre = c.r.slice(1);
          for (const x of Rx.get(key(pre)) || []) {
            const nc = { l: nl, r: pre.concat([x]), c: mid, s: t.s };
            if (add(nc)) { V.push(nc); news.push(ckey(nc)); any = true; }
          }
        } else {
          if (addR(c.r)) any = true;
          const nr = [t.w].concat(c.r.slice(0, -1)), mid = c.l[n - 1], suf = c.l.slice(0, -1);
          for (const x of Lx.get(key(suf)) || []) {
            const nc = { l: [x].concat(suf), r: nr, c: mid, s: t.s };
            if (add(nc)) { V.push(nc); news.push(ckey(nc)); any = true; }
          }
        }
        if (trace && trace.length < 4000) trace.push({ from: ckey(c), news, L: Lset.size, R: Rset.size, C: order.length });
      }
      if (!any) return { result: "nonhalt", visits, passes, L: [...Lset], R: [...Rset], C: order.map(ckey), trace };
    }
  }

  // ------------------------------------------------------------- RepWL
  // Repeated Word List, as Coq-BB5 implements it (RepWL_ES_decider in Decider_RepWL.v). The tape is two stacks of
  // repeated words of length l on either side of a directed head: r is the stack the head faces, l the one behind it,
  // tops nearest the head, and each word is stored outwards from the head. A word repeated T or more times becomes
  // (w)^T+. A step pops one word from r (popping from (w)^T+ branches: the rest is (w)^(T-1) exactly, or still
  // (w)^T+), runs the machine on that word alone until the head leaves it (at most B steps), and pushes the new word
  // on the side the head left it, merging it with an equal word on top of that stack. The machine does not halt if the
  // set of such configurations reachable from A> closes without a halt or a timeout.
  function repWL(m, l, T, opts = {}) {
    const B = opts.B || 320, N = opts.N || 150001, keepGraph = !!opts.graph;
    const zeroW = "0".repeat(l);
    const rw = (w, k, c) => ({ w, k, c }); // (w)^k exactly if c, (w)^k+ otherwise
    function pop(wl) {
      if (!wl.length) return [zeroW, [[]]];
      const v = wl[0], rest = wl.slice(1);
      const conts = [v.k > 1 ? [rw(v.w, v.k - 1, true)].concat(rest) : rest];
      if (!v.c) conts.push(wl);
      return [v.w, conts];
    }
    function push(wl, w0) {
      if (!wl.length) return /^0*$/.test(w0) ? [] : [rw(w0, 1, true)];
      const v = wl[0];
      if (v.w === w0) {
        const cnt = v.k + 1;
        return [cnt < T ? rw(w0, cnt, v.c) : rw(w0, T, false)].concat(wl.slice(1));
      }
      return [rw(w0, 1, true)].concat(wl);
    }
    // Runs the machine on word w0 (first cell under the head, the rest outwards). Returns null on halt or timeout.
    function wordUpdate(s0, w0, sgn0) {
      let lft = [], rgt = [], mid = +w0[0], s = s0;
      const rest = w0.slice(1).split("").map(Number);
      if (sgn0 > 0) rgt = rest; else lft = rest;
      for (let k = 0; k < B; k++) {
        const t = m.tr[2 * s + mid];
        if (!t) return { halt: true };
        s = t.s;
        if (t.d > 0) {
          if (rgt.length) { lft.unshift(t.w); mid = rgt.shift(); }
          else return { s, w: [t.w].concat(lft).join(""), back: sgn0 < 0 };
        } else {
          if (lft.length) { rgt.unshift(t.w); mid = lft.shift(); }
          else return { s, w: [t.w].concat(rgt).join(""), back: sgn0 > 0 };
        }
      }
      return { timeout: true };
    }
    const keyOf = (x) => x.sgn + x.s + "|" + x.l.map((v) => v.w + v.k + (v.c ? "" : "+")).join(",") + "|" +
      x.r.map((v) => v.w + v.k + (v.c ? "" : "+")).join(",");
    const rev = (w) => w.split("").reverse().join("");
    const side = (st, left) => st.map((v) => "(" + (left ? rev(v.w) : v.w) + ")^" + v.k + (v.c ? "" : "+"));
    const str = (x) => {
      const [lst, rst] = x.sgn > 0 ? [x.l, x.r] : [x.r, x.l];
      const a = side(lst, true).reverse(), b = side(rst, false);
      const head = x.sgn > 0 ? L(x.s) + ">" : "<" + L(x.s);
      return ["0∞"].concat(a, [head], b, ["0∞"]).join(" ");
    };
    function stepOf(x) {
      const [w0, conts] = pop(x.r), out = [];
      const u = wordUpdate(x.s, w0, x.sgn);
      if (u.halt || u.timeout) return u;
      for (const r1 of conts) {
        if (u.back) out.push({ l: push(r1, u.w), r: x.l, s: u.s, sgn: -x.sgn });
        else out.push({ l: push(x.l, u.w), r: r1, s: u.s, sgn: x.sgn });
      }
      return { next: out, branched: conts.length > 1 };
    }
    const init = { l: [], r: [], s: 0, sgn: 1 };
    const seen = new Map([[keyOf(init), 0]]), list = [init], q = [init], edges = keepGraph ? [] : null;
    let expansions = 0;
    while (q.length) {
      if (++expansions > N) return { result: "unknown", reason: "too many nodes", nodes: seen.size };
      const x = q.pop(), from = seen.get(keyOf(x));
      const st = stepOf(x);
      if (st.halt || st.timeout) {
        if (keepGraph) edges.push([from, -1, st.halt ? "halt" : "timeout"]);
        return { result: "unknown", reason: st.halt ? "halting transition reached" : "block simulation timed out",
          at: str(x), nodes: seen.size, graph: keepGraph ? { nodes: list.map(str), edges } : null };
      }
      for (const y of st.next) {
        const k = keyOf(y);
        if (!seen.has(k)) { seen.set(k, list.length); list.push(y); q.push(y); }
        if (keepGraph) edges.push([from, seen.get(k), st.branched ? "branch" : "block"]);
      }
    }
    return { result: "nonhalt", nodes: seen.size, graph: keepGraph ? { nodes: list.map(str), edges } : null };
  }

  // The same idea as the Python reproduction in bbchallenge-deciders implements it (decider.py, tm_regex_tape.py),
  // which drew the RepWL figures of the BB(5) paper and gives its node counts (42, 845 and 143,181 for its three
  // examples). It differs from Coq-BB5 in two details: a constant block (w)^k is simulated as one piece, and blocks
  // of zeros next to 0∞ are kept. Both are sound.
  function repWLPaper(m, l, T, opts = {}) {
    const B = opts.B || 320, N = opts.N || 150001, keepGraph = !!opts.graph;
    const zeroW = "0".repeat(l);
    const bstr = (b) => "(" + b.w + ")^" + b.k + (b.p ? "+" : "");
    const str = (t) => {
      let s = "0∞ ";
      for (const b of t.bh) s += bstr(b) + " ";
      s += t.right ? L(t.s) + ">" : "<" + L(t.s);
      for (let i = t.ah.length - 1; i >= 0; i--) s += " " + bstr(t.ah[i]);
      return s + " 0∞";
    };
    const cp = (b) => ({ w: b.w, k: b.k, p: b.p });
    const clone = (t) => ({ bh: t.bh.map(cp), ah: t.ah.map(cp), s: t.s, right: t.right });
    function compressGeneralise(t) {
      for (const sd of ["bh", "ah"]) {
        const out = [];
        for (const b of t[sd]) {
          if (out.length && out[out.length - 1].w === b.w) { const o = out[out.length - 1]; o.k += b.k; o.p = o.p || b.p; }
          else out.push(cp(b));
        }
        for (const b of out) if (b.k >= T) { b.p = true; b.k = T; }
        t[sd] = out;
      }
    }
    function readBlock(t) {
      if (t.right && t.ah.length) return t.ah[t.ah.length - 1];
      if (!t.right && t.bh.length) return t.bh[t.bh.length - 1];
      return { w: zeroW, k: 1, p: false };
    }
    function macro(t0) {
      const t = clone(t0), blk = readBlock(t);
      if (blk.p) return "plus";
      const cells = blk.w.repeat(blk.k).split("").map(Number), len = cells.length;
      let h = t.right ? 0 : len, right = t.right, s = t.s, steps = 0;
      while (true) {
        if ((right && h === len) || (!right && h === 0)) break;
        if (steps === B) return "timeout";
        const idx = right ? h : h - 1, tr = m.tr[2 * s + cells[idx]];
        if (!tr) return "halt";
        cells[idx] = tr.w;
        if (tr.d < 0) { if (right) right = false; else h--; } else { if (!right) right = true; else h++; }
        s = tr.s; steps++;
      }
      const word = cells.join(""), nb = [];
      for (let i = 0; i < len; i += l) nb.push({ w: word.slice(i, i + l), k: 1, p: false });
      if (t.right) {
        const rv = nb.slice().reverse();
        if (t.ah.length === 0) t.ah.push(...rv);
        else { t.ah[t.ah.length - 1] = rv[0]; for (let i = 1; i < rv.length; i++) t.ah.push(rv[i]); }
      } else if (t.bh.length === 0) t.bh.push(...nb);
      else { t.bh[t.bh.length - 1] = nb[0]; for (let i = 1; i < nb.length; i++) t.bh.push(nb[i]); }
      const n = nb.length;
      if (right !== t.right) t.right = right;
      else if (right) for (let i = 0; i < n; i++) t.bh.push(t.ah.pop());
      else for (let i = 0; i < n; i++) t.ah.push(t.bh.pop());
      t.s = s;
      compressGeneralise(t);
      return t;
    }
    function branches(t) {
      const blk = readBlock(t), b1 = clone(t), b2 = clone(t), sd = t.right ? "ah" : "bh";
      b1[sd].push({ w: blk.w, k: 1, p: false });
      const top = b2[sd][b2[sd].length - 1];
      top.p = false;
      if (top.k > 1) { top.k -= 1; b2[sd].push({ w: blk.w, k: 1, p: false }); }
      return [b1, b2];
    }
    const init = { bh: [], ah: [], s: 0, right: true };
    const visited = new Set(), todo = [init], nodes = keepGraph ? new Map() : null, edges = keepGraph ? [] : null;
    const id = (x) => { if (!nodes.has(x)) nodes.set(x, nodes.size); return nodes.get(x); };
    if (keepGraph) id(str(init));
    while (todo.length) {
      const t = todo.pop(), x = str(t);
      if (visited.has(x)) continue;
      visited.add(x);
      if (visited.size > N) return { result: "unknown", reason: "too many nodes", nodes: visited.size };
      const r = macro(t);
      if (r === "halt" || r === "timeout") {
        if (keepGraph) edges.push([id(x), -1, r]);
        return { result: "unknown", reason: r === "halt" ? "halting transition reached" : "block simulation timed out",
          at: x, nodes: visited.size, graph: keepGraph ? { nodes: [...nodes.keys()], edges } : null };
      }
      if (r === "plus") {
        const bs = branches(t);
        if (keepGraph) bs.forEach((y) => edges.push([id(x), id(str(y)), "branch"]));
        todo.push(...bs);
      } else {
        if (keepGraph) edges.push([id(x), id(str(r)), "block"]);
        todo.push(r);
      }
    }
    return { result: "nonhalt", nodes: visited.size, graph: keepGraph ? { nodes: [...nodes.keys()], edges } : null };
  }

  // ------------------------------------------------------------- FAR
  // Coq-BB5 dfa_nfa_verifier (Verifier_FAR.v): from a DFA that reads the tape to the left of the head (left to
  // right), build the NFA that reads the head symbol and the tape to its right, with states (TM state, DFA state)
  // and a sink None (= "can halt"); it accepts at least every configuration that eventually halts. The machine does
  // not halt if the DFA ignores leading zeros and the run of the start configuration on zeros never reaches None.
  // dfa: array of [next on 0, next on 1], state 0 initial.
  function farNFA(m, dfa) {
    const nU = dfa.length, nS = m.n, N = nS * nU + 1, NONE = nS * nU;
    const idx = (s, u) => s * nU + u;
    // T[sym][a] = Set of b
    const T = [0, 1].map(() => Array.from({ length: N }, () => new Set()));
    for (const i of [0, 1]) T[i][NONE].add(NONE);
    for (let s = 0; s < nS; s++) for (let i = 0; i < 2; i++) {
      const t = m.tr[2 * s + i];
      for (let u = 0; u < nU; u++) {
        if (!t) T[i][idx(s, u)].add(NONE);
        else if (t.d > 0) T[i][idx(s, u)].add(idx(t.s, dfa[u][t.w]));
      }
    }
    // Left moves: Some(s0, dfa u1 i2) -i0-> su3 whenever Some(s1,u1) -i2-> su2 -i1-> su3. Iterate to a fixpoint.
    let changed = true, rounds = 0;
    while (changed) {
      changed = false; rounds++;
      for (let s0 = 0; s0 < nS; s0++) for (let i0 = 0; i0 < 2; i0++) {
        const t = m.tr[2 * s0 + i0];
        if (!t || t.d > 0) continue;
        for (let u1 = 0; u1 < nU; u1++) for (let i2 = 0; i2 < 2; i2++) {
          const from = idx(s0, dfa[u1][i2]), tgt = T[i0][from];
          for (const su2 of T[i2][idx(t.s, u1)]) for (const su3 of T[t.w][su2]) if (!tgt.has(su3)) { tgt.add(su3); changed = true; }
        }
      }
    }
    // States reachable from (A, U0) reading zeros (the tape right of the start head is all 0).
    const acc = new Set([idx(0, 0)]), stack = [idx(0, 0)];
    while (stack.length) { const a = stack.pop(); for (const b of T[0][a]) if (!acc.has(b)) { acc.add(b); stack.push(b); } }
    const dfa0 = dfa[0][0] === 0;
    const ok = dfa0 && !acc.has(NONE);
    const name = (a) => (a === NONE ? "⊥" : u2s(a % nU) + L(Math.floor(a / nU)));
    function u2s(u) { return "" + u; }
    return { result: ok ? "nonhalt" : "unknown", dfa0, haltReachable: acc.has(NONE), rounds, N, NONE, T, acc, name, nU };
  }
  // Does the NFA accept (i.e. say "may halt") the configuration left [S] head right? left/right are 0/1 strings.
  function farAccepts(m, dfa, nfa, left, st, right) {
    let u = 0;
    for (const ch of left) u = dfa[u][+ch];
    let cur = new Set([st * nfa.nU + u]);
    const path = [[...cur]];
    for (const ch of right) {
      const nx = new Set();
      for (const a of cur) for (const b of nfa.T[+ch][a]) nx.add(b);
      cur = nx; path.push([...cur]);
    }
    // trailing zeros: the accepting set is the halting sink None, which loops on 0 and 1; look through zeros too.
    const seen = new Set(cur), stack = [...cur];
    while (stack.length) { const a = stack.pop(); for (const b of nfa.T[0][a]) if (!seen.has(b)) { seen.add(b); stack.push(b); } }
    return { u, path, mayHalt: seen.has(nfa.NONE) };
  }

  // ------------------------------------------------------------- WFAR
  // Coq-BB5 MITM_WDFA_verifier (Verifier_WFAR.v). Two deterministic weighted automata read the tape: the left one
  // from the far left towards the head, the right one from the far right towards the head. An abstract configuration
  // is (left state, right state, head symbol, TM state, d, g): with g = null the total weight W = d exactly, with
  // g = +1 W >= d, with g = -1 W <= d. Exact weights beyond maxD are generalised. Starting from (0,0,0,A,0,null) the
  // verifier explores successors until the set is closed (no halting transition met), discarding configurations whose
  // weight bound contradicts the signs the automata force on their states.
  // wl, wr: arrays of [next0, weight0, next1, weight1].
  function wfar(m, maxD, wl, wr, opts = {}) {
    const gas = opts.gas || 10000000;
    const dl = (u, i) => [wl[u][2 * i], wl[u][2 * i + 1]], dr = (u, i) => [wr[u][2 * i], wr[u][2 * i + 1]];
    const zeroOk = wl[0][0] === 0 && wl[0][1] === 0 && wr[0][0] === 0 && wr[0][1] === 0;
    // sgn[dir][u] = every word ending in u has weight * dir >= 0 (computed as in wdfa_sgn_rec).
    const sgnOf = (w) => {
      const res = {};
      for (const d of [1, -1]) {
        const bad = new Set();
        let changed = true;
        while (changed) {
          changed = false;
          for (let u = 0; u < w.length; u++) for (let i = 0; i < 2; i++) {
            const nu = w[u][2 * i], wt = w[u][2 * i + 1];
            if (wt * d >= 0 && !bad.has(u)) continue;
            if (!bad.has(nu)) { bad.add(nu); changed = true; }
          }
        }
        res[d] = w.map((_, u) => !bad.has(u));
      }
      return res;
    };
    const sl = sgnOf(wl), sr = sgnOf(wr);
    // The Coq check that the sign sets are closed holds by construction of the fixpoint above.
    const popL = (u0) => { const r = []; for (let i = 0; i < 2; i++) for (let u = 0; u < wl.length; u++) if (wl[u][2 * i] === u0) r.push([u, i, wl[u][2 * i + 1]]); return r; };
    const popR = (u0) => { const r = []; for (let i = 0; i < 2; i++) for (let u = 0; u < wr.length; u++) if (wr[u][2 * i] === u0) r.push([u, i, wr[u][2 * i + 1]]); return r; };
    const good = (e) => {
      const [l, r, , , d, g] = e, gz = g || 0;
      return !((d > 0 && gz >= 0 && sl[-1][l] && sr[-1][r]) || (d < 0 && gz <= 0 && sl[1][l] && sr[1][r]));
    };
    const simplify = (e) => {
      const [l, r, mm, s, d, g] = e;
      if (g === null) {
        if (Math.abs(d) >= maxD && d !== 0) return [[l, r, mm, s, d, d > 0 ? 1 : -1]];
        return [e];
      }
      const x = Math.abs(d) - maxD;
      if (x > 0) return [[l, r, mm, s, d - g, g]];
      if (x < 0) return [[l, r, mm, s, d, null], [l, r, mm, s, d + g, g]];
      return [e];
    };
    const filt = (ls) => ls.filter(good).flatMap(simplify);
    const keyOf = (e) => e.join(",");
    const init = [0, 0, 0, 0, 0, null];
    const seen = new Map([[keyOf(init), init]]), todo = [init];
    let steps = 0;
    while (todo.length) {
      if (++steps > gas) return { result: "unknown", reason: "gas", zeroOk };
      const e = todo.pop();
      const [l, r, mm, s, d, g] = e, t = m.tr[2 * s + mm];
      if (!t) return { result: "unknown", reason: "halting configuration " + L(s) + mm + " reached", zeroOk, set: [...seen.values()] };
      let next;
      if (t.d > 0) { const [l2, wd] = dl(l, t.w); next = popR(r).map(([r2, m3, wd2]) => [l2, r2, m3, t.s, d + wd - wd2, g]); }
      else { const [r2, wd] = dr(r, t.w); next = popL(l).map(([l2, m3, wd2]) => [l2, r2, m3, t.s, d + wd - wd2, g]); }
      for (const x of filt(next)) { const k = keyOf(x); if (!seen.has(k)) { seen.set(k, x); todo.push(x); } }
    }
    return { result: zeroOk ? "nonhalt" : "unknown", zeroOk, set: [...seen.values()], sl, sr };
  }
  // Weighted run of a configuration through the two automata (for the page's evaluator).
  function wfarRead(wl, wr, left, right) {
    let u = 0, W = 0; const lp = [[0, 0]];
    for (const ch of left) { const i = +ch; W += wl[u][2 * i + 1]; u = wl[u][2 * i]; lp.push([u, W]); }
    let v = 0, V = 0; const rp = [[0, 0]];
    for (let k = right.length - 1; k >= 0; k--) { const i = +right[k]; V += wr[v][2 * i + 1]; v = wr[v][2 * i]; rp.push([v, V]); }
    return { l: u, wl: W, r: v, wr: V, lp, rp };
  }

  // ------------------------------------------------------------- 1RB reduction
  // Coq-BB5 TM_to_NF: from the blank tape, transitions that write 0 leave the tape blank, so follow them to the first
  // state whose 0-transition writes a 1, and rename (and mirror, if it moves left) so that the machine starts there.
  // States are then renamed in order of first use from the start, as the tree normal form does.
  function reduce1RB(m) {
    let s = 0; const seen = new Set();
    while (true) {
      if (seen.has(s)) return { result: "never writes", chain: [...seen] };
      seen.add(s);
      const t = m.tr[2 * s];
      if (!t) return { result: "halts", chain: [...seen] };
      if (t.w === 1) break;
      s = t.s;
    }
    const mirror = m.tr[2 * s].d < 0;
    // Rename states in order of first visit by the run from s on the blank tape (the tree normal form order), then
    // any states the first 100000 steps do not reach in order of appearance in the table.
    const order = [s], pos = new Map([[s, 0]]);
    const tmp = { n: m.n, tr: m.tr.map((t) => (t ? { w: t.w, d: mirror ? -t.d : t.d, s: t.s } : null)) };
    const run = new Run(tmp); run.state = s;
    for (let k = 0; k < 100000 && order.length < m.n && run.step(); k++)
      if (!pos.has(run.state)) { pos.set(run.state, order.length); order.push(run.state); }
    for (let q = 0; q < order.length; q++) for (let i = 0; i < 2; i++) {
      const t = m.tr[2 * order[q] + i];
      if (t && !pos.has(t.s)) { pos.set(t.s, order.length); order.push(t.s); }
    }
    for (let x = 0; x < m.n; x++) if (!pos.has(x)) { pos.set(x, order.length); order.push(x); }
    const tr = [];
    for (const old of order) for (let i = 0; i < 2; i++) {
      const t = m.tr[2 * old + i];
      tr.push(t ? { w: t.w, d: mirror ? -t.d : t.d, s: pos.get(t.s) } : null);
    }
    const out = { n: m.n, tr };
    out.text = format(out);
    return { result: "reduced", start: s, chain: [...seen], mirror, machine: out };
  }

  // ------------------------------------------------------------- Backward reasoning
  // bbchallenge decider-backward-reasoning (correctness paper, Algorithm decider-backward-reasoning): from each
  // halting transition, apply transitions backwards on a partial tape until every branch meets a contradiction.
  function backward(m, maxDepth) {
    const roots = [];
    for (let s = 0; s < m.n; s++) for (let i = 0; i < 2; i++) if (!m.tr[2 * s + i]) roots.push({ s, i });
    const nodes = [];
    const stack = roots.map(({ s, i }) => ({ s, pos: 0, tape: new Map([[0, i]]), depth: 0, parent: -1, via: null }));
    let ok = true, maxSeen = 0;
    while (stack.length) {
      const c = stack.pop();
      const id = nodes.length;
      nodes.push({ s: c.s, pos: c.pos, tape: [...c.tape.entries()].sort((a, b) => a[0] - b[0]), depth: c.depth, parent: c.parent, via: c.via, dead: [] });
      if (nodes.length > 20000) return { result: "unknown", reason: "tree too large", nodes };
      if (c.depth > maxDepth) { ok = false; nodes[id].open = true; break; }
      maxSeen = Math.max(maxSeen, c.depth);
      for (let s = 0; s < m.n; s++) for (let i = 0; i < 2; i++) {
        const t = m.tr[2 * s + i];
        if (!t || t.s !== c.s) continue;
        const prev = c.pos - t.d;
        const via = L(s) + i + "→" + trText(t);
        if (c.tape.has(prev) && c.tape.get(prev) !== t.w) { nodes[id].dead.push(via + " (cell holds " + c.tape.get(prev) + ", not " + t.w + ")"); continue; }
        const tape = new Map(c.tape); tape.set(prev, i);
        stack.push({ s, pos: prev, tape, depth: c.depth + 1, parent: id, via });
      }
    }
    return { result: ok ? "nonhalt" : "unknown", depth: maxSeen, nodes, roots };
  }

  // ------------------------------------------------------------- Halting segment
  // The halting segment graph (correctness paper, Definition "Halting Segment graph"), built forwards from the n + 2
  // initial nodes. A node is (state, segment word, head position in [-1, n]). The machine does not halt if, for every
  // halting transition, some head position has no reachable halting node.
  function haltingSegment(m, n) {
    const nodes = new Map(), edges = [], todo = [];
    const k = (s, w, p) => s + ":" + w + ":" + p;
    const add = (s, w, p, from) => {
      const kk = k(s, w, p);
      if (!nodes.has(kk)) { nodes.set(kk, { s, w, p, id: nodes.size }); todo.push(kk); }
      if (from !== undefined) edges.push([nodes.get(from).id, nodes.get(kk).id]);
    };
    for (let p = -1; p <= n; p++) add(0, "0".repeat(n), p);
    const halts = [];
    while (todo.length) {
      const kk = todo.shift(), { s, w, p } = nodes.get(kk);
      if (s < 0) continue;
      if (p >= 0 && p < n) {
        const i = +w[p], t = m.tr[2 * s + i];
        if (!t) { add(-1 - (2 * s + i), w, p, kk); continue; }
        const nw = w.slice(0, p) + t.w + w.slice(p + 1);
        add(t.s, nw, p + t.d, kk);
      } else {
        for (let i = 0; i < 2; i++) {
          const t = m.tr[2 * s + i];
          if (!t) { add(-1 - (2 * s + i), w, p, kk); continue; }
          const towards = (p < 0 && t.d > 0) || (p >= n && t.d < 0);
          add(t.s, w, p, kk);
          if (towards) add(t.s, w, p < 0 ? 0 : n - 1, kk);
        }
      }
    }
    // For each halting transition, the head positions covered by reachable halting nodes.
    const cover = {};
    for (let s = 0; s < m.n; s++) for (let i = 0; i < 2; i++) if (!m.tr[2 * s + i]) cover[L(s) + i] = new Set();
    for (const v of nodes.values()) if (v.s < 0) { const code = -1 - v.s; cover[L(code >> 1) + (code & 1)].add(v.p); }
    const decided = Object.values(cover).every((c) => c.size < n + 2);
    const list = [...nodes.values()].sort((a, b) => a.id - b.id);
    const name = (v) => {
      let out = (v.s < 0 ? "⊥ " + L((-1 - v.s) >> 1) + ((-1 - v.s) & 1) : L(v.s)) + " ";
      out += v.p < 0 ? "[-]" : "-";
      for (let q = 0; q < n; q++) out += " " + (q === v.p ? "[" + v.w[q] + "]" : v.w[q]);
      out += " " + (v.p >= n ? "[-]" : "-");
      return out;
    };
    return { result: Object.keys(cover).length && decided ? "nonhalt" : "unknown", nodes: list, edges,
      cover: Object.fromEntries(Object.entries(cover).map(([a, b]) => [a, [...b].sort((x, y) => x - y)])), name };
  }

  // ------------------------------------------------------------- Bouncer formula tapes
  // Parses a bouncer certificate tape from bbchallenge-deciders/decider-bouncers-reproduction, e.g.
  // ".111(111)01111(11)C>." (dots are 0∞, parentheses are repeaters), and finds the moments of a run whose tape
  // matches it, reporting the repeat counts. This shows the certificate at work; it is not the decider's proof.
  function parseFormula(f) {
    const parts = []; let i = 0;
    while (i < f.length) {
      const c = f[i];
      if (c === ".") { parts.push({ t: "inf" }); i++; }
      else if (c === "(") { const j = f.indexOf(")", i); parts.push({ t: "rep", w: f.slice(i + 1, j) }); i = j + 1; }
      else if (/[A-Z]/.test(c) && f[i + 1] === ">") { parts.push({ t: "head", s: c.charCodeAt(0) - 65, right: true }); i += 2; }
      else if (c === "<") { parts.push({ t: "head", s: f.charCodeAt(i + 1) - 65, right: false }); i += 2; }
      else { let j = i; while (j < f.length && (f[j] === "0" || f[j] === "1")) j++; parts.push({ t: "wall", w: f.slice(i, j) }); i = j; }
    }
    return parts;
  }
  // Directed-head tape word of a run: the visited cells with the head as "S>" before the cell it reads, or as "<S"
  // after it.
  function directedWord(r, right) {
    let a = "", b = "";
    const cut = right ? r.pos : r.pos + 1;
    for (let p = r.lo; p < cut; p++) a += r.read(p);
    for (let p = cut; p <= r.hi; p++) b += r.read(p);
    return { left: a, right: b, s: r.state };
  }
  function matchFormula(parts, word) {
    // Build a regex: walls literal, repeaters (w)*, head S>, the 0∞ ends as 0*.
    let re = "^", groups = [];
    for (const p of parts) {
      if (p.t === "inf") re += "0*";
      else if (p.t === "wall") re += p.w;
      else if (p.t === "rep") { re += "((?:" + p.w + ")*)"; groups.push(p.w.length); }
      else re += "\\|" + L(p.s) + (p.right ? ">" : "<") + "\\|";
    }
    re += "$";
    const head = parts.find((p) => p.t === "head");
    if (!head || head.s !== word.s) return null;
    const text = word.left + "|" + L(word.s) + (head.right ? ">" : "<") + "|" + word.right;
    const mm = new RegExp(re).exec(text);
    if (!mm) return null;
    return groups.map((len, gi) => mm[gi + 1].length / len);
  }
  function bouncerMoments(m, formula, steps, max = 30) {
    const parts = parseFormula(formula), r = new Run(m), hits = [];
    const head = parts.find((p) => p.t === "head");
    for (let t = 0; t <= steps && hits.length < max; t++) {
      const c = matchFormula(parts, directedWord(r, head.right));
      if (c) hits.push({ step: r.steps, counts: c, tape: r.configStr() });
      if (!r.step()) break;
    }
    return { parts, hits };
  }

  return { parse, format, trText, L, Run, spaceTime, loops, ngramCPS, repWL, repWLPaper, farNFA, farAccepts, wfar, wfarRead,
    reduce1RB, backward, haltingSegment, parseFormula, bouncerMoments };
})();
if (typeof module !== "undefined") module.exports = BB;
