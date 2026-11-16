// The interactive parts of the "one halting question for two machines" sections, shared by the explainers of
// 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE and 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC.
// Embedded in both pages by py/pair_page.py; the engine part (everything above "UI") is tested in Node by
// py/pair/test_pair.js against the Coq file's numbers (2 and 49 steps, 5 and 44k+5, 28 abstract configurations).
(function () {
"use strict";
const TM = "1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE";
const TP = "1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC";
const SN = "ABCDEF";
const G = [3, 4, 0, 1, 2, 5];                 // g: A->D, B->E, C->A, D->B, E->C, F->F (Coq's g)
const W8 = [1, 0, 0, 0, 1, 1, 0, 1];          // the extra word, as the first machine reads it, left to right
const B = 1, D = 3;

function parse(s) {
  const T = [];
  s.split("_").forEach((p, i) => {
    for (let r = 0; r < 2; r++) {
      const t = p.substr(3 * r, 3);
      T[2 * i + r] = t[2] === "-" ? null : { w: +t[0], d: t[1] === "R" ? 1 : -1, q: SN.indexOf(t[2]) };
    }
  });
  return T;
}
function unparse(T) {
  let o = [];
  for (let i = 0; i < 6; i++) {
    let p = "";
    for (let r = 0; r < 2; r++) { const t = T[2 * i + r]; p += t ? t.w + (t.d > 0 ? "R" : "L") + SN[t.q] : "---"; }
    o.push(p);
  }
  return o.join("_");
}

// A plain simulator on a growable tape.
class Sim {
  constructor(T) { this.T = T; this.N = 1 << 12; this.o = this.N >> 1; this.t = new Uint8Array(this.N);
    this.h = 0; this.q = 0; this.n = 0; this.lo = 0; this.hi = 0; this.halted = false; }
  get(p) { const i = p + this.o; return i >= 0 && i < this.N ? this.t[i] : 0; }
  set(p, v) {
    let i = p + this.o;
    if (i < 1 || i >= this.N - 1) {
      const N2 = this.N * 2, o2 = this.o + (this.N >> 1), t2 = new Uint8Array(N2);
      t2.set(this.t, this.N >> 1); this.t = t2; this.N = N2; this.o = o2; i = p + this.o;
    }
    this.t[i] = v;
  }
  step() {
    const r = this.T[2 * this.q + this.get(this.h)];
    if (!r) { this.halted = true; return false; }
    this.set(this.h, r.w); this.h += r.d; this.q = r.q; this.n++;
    if (this.h < this.lo) this.lo = this.h; if (this.h > this.hi) this.hi = this.h;
    return true;
  }
  clone() { const s = new Sim(this.T); Object.assign(s, this, { t: this.t.slice() }); return s; }
}

// The two real runs in lockstep, one model step at a time (Coq's f): one step of each machine, or the far-end
// crossing (5 steps of the first, 49 of the second) when the first is in B on a 1 at its rightmost cell q.
class Pair {
  constructor() {
    this.a = new Sim(parse(TM)); this.b = new Sim(parse(TP));
    for (let i = 0; i < 2; i++) this.a.step();
    for (let i = 0; i < 49; i++) this.b.step();
    this.m = 0; this.cross = 0; this.bad = null;
  }
  // position of the second machine's cell that mirrors cell p of the first
  mir(p) { return this.a.h + this.b.h - p; }
  crossingNow() { const a = this.a; return a.h === a.hi && a.q === B && a.get(a.h) === 1; }
  step() {
    const a = this.a, b = this.b;
    if (this.crossingNow()) {
      for (let i = 0; i < 5; i++) a.step();
      for (let i = 0; i < 49; i++) b.step();
      this.cross++; this.m++; return "cross";
    }
    const r = a.T[2 * a.q + a.get(a.h)];
    if (!r) return "halt";
    if (a.h === a.hi && r.d > 0) { this.bad = "the head leaves q in state " + SN[a.q]; return "bad"; }
    a.step(); b.step(); this.m++; return "step";
  }
  // Coq's to_config relation: same state up to g, same cells up to q, then W8, then blank
  agree() {
    const a = this.a, b = this.b, q = a.hi;
    if (b.q !== G[a.q]) return "state";
    const lo = Math.min(a.lo, this.mir(b.hi)) - 1;
    for (let p = lo; p <= q; p++) if (a.get(p) !== b.get(this.mir(p))) return "cell " + p;
    for (let i = 0; i < 8; i++) if (b.get(this.mir(q + 1 + i)) !== W8[i]) return "word";
    if (this.mir(b.lo) > q + 8) for (let p = q + 9; p <= this.mir(b.lo); p++) if (b.get(this.mir(p))) return "tail";
    return null;
  }
}

// ---- the abstraction of the Coq proof: the window of the last four cells q-3..q --------------------------------
// inn: {k:"inn", q, wl (left of head, nearest first), a, u (head+1..q)}; out: {k:"out", w (the four cells)}
const key = s => s.k === "inn" ? SN[s.q] + "|" + s.wl.join("") + "|" + s.a + "|" + s.u.join("") : "out|" + s.w.join("");
const RT = [1, 3, 4, 5];                       // the states a move right can produce: B, D, E, F
function anext(T, s) {
  if (s.k === "out") {
    const o = [s];
    if (s.w.length) for (const q of RT) o.push({ k: "inn", q, wl: [], a: s.w[0], u: s.w.slice(1) });
    return o;
  }
  const r = T[2 * s.q + s.a];
  if (!r) return [];
  if (r.d < 0) return s.wl.length ? [{ k: "inn", q: r.q, wl: s.wl.slice(1), a: s.wl[0], u: [r.w].concat(s.u) }]
                                   : [{ k: "out", w: [r.w].concat(s.u) }];
  if (s.u.length) return [{ k: "inn", q: r.q, wl: [r.w].concat(s.wl), a: s.u[0], u: s.u.slice(1) }];
  return s.wl.length ? [{ k: "inn", q: D, wl: [], a: s.wl[0], u: [1, 0, 1] }]
                     : [0, 1].map(a => ({ k: "inn", q: D, wl: [], a, u: [1, 0, 1] }));
}
function okb(T, s) {
  if (s.k === "out") return s.w.length > 0;
  if (s.u.length) return true;
  if (s.q === B && s.a === 1) return true;
  const r = T[2 * s.q + s.a];
  return !(r && r.d > 0);
}
const START = { k: "inn", q: 2, wl: [0, 0], a: 1, u: [1] };   // Coq's cfg0: C, window 0 0 [1] 1
// breadth-first closure; stops at the first configuration that fails okb
function closure(T) {
  const seen = new Map([[key(START), { s: START, from: null, i: 0 }]]), order = [START];
  for (let i = 0; i < order.length; i++) {
    const s = order[i];
    if (!okb(T, s)) return { order, seen, bad: s };
    for (const t of anext(T, s)) if (!seen.has(key(t))) { seen.set(key(t), { s: t, from: s, i: order.length }); order.push(t); }
    if (order.length > 400) return { order, seen, bad: null, big: true };
  }
  return { order, seen, bad: null };
}
// the abstraction of a real configuration of the first machine (after its first 2 steps)
function absOf(a) {
  const q = a.hi;
  if (a.h >= q - 3) {
    const wl = [], u = [];
    for (let p = a.h - 1; p >= q - 3; p--) wl.push(a.get(p));
    for (let p = a.h + 1; p <= q; p++) u.push(a.get(p));
    return { k: "inn", q: a.q, wl, a: a.get(a.h), u };
  }
  return { k: "out", w: [a.get(q - 3), a.get(q - 2), a.get(q - 1), a.get(q)] };
}

const ENGINE = { TM, TP, G, W8, SN, parse, unparse, Sim, Pair, anext, okb, closure, absOf, key, START };
if (typeof module !== "undefined" && module.exports) { module.exports = ENGINE; return; }

// ---- UI ----------------------------------------------------------------------------------------------------------
const $ = id => document.getElementById(id);
const css = n => getComputedStyle(document.documentElement).getPropertyValue(n).trim() || "#888";
const fmt = n => n.toLocaleString("en-US");
const esc = s => String(s).replace(/[&<>]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" }[c]));
const T1 = parse(TM), T2 = parse(TP);

// 1. The two tables -------------------------------------------------------------------------------------------
function tables() {
  const box = $("tqTables"); if (!box) return;
  const cellTxt = t => t ? t.w + (t.d > 0 ? "R" : "L") + SN[t.q] : "---";
  const tbl = (T, id, name, start, extra = "") => {
    let h = `<div class="tq-tt${extra}"><div class="tq-ttname"><code>${name}</code><span class="small">${start}</span></div>` +
      `<table class="tt"><thead><tr><th></th><th>read 0</th><th>read 1</th></tr></thead><tbody>`;
    for (let i = 0; i < 6; i++) {
      h += `<tr><th>${SN[i]}</th>`;
      for (let r = 0; r < 2; r++) h += `<td tabindex="0" data-t="${id}" data-k="${2 * i + r}" class="${T[2 * i + r] ? "" : "halt"}">${cellTxt(T[2 * i + r])}</td>`;
      h += "</tr>";
    }
    return h + "</tbody></table></div>";
  };
  // the second table translated back: state g(s) of tm' becomes s, L and R exchanged
  const back = [];
  for (let s = 0; s < 6; s++) for (let r = 0; r < 2; r++) {
    const t = T2[2 * G[s] + r];
    back[2 * s + r] = t ? { w: t.w, d: -t.d, q: G.indexOf(t.q) } : null;
  }
  box.innerHTML = tbl(T1, 1, TM, "starts in A") + tbl(T2, 2, TP, "starts in A") +
    tbl(back, 3, "the second table, translated back", "starts in C", " tq-back\" hidden data-x=\"");
  const say = $("tqTableSay");
  const show = (t, k) => {
    box.querySelectorAll("td.tq-hl").forEach(e => e.classList.remove("tq-hl"));
    const s = k >> 1, r = k & 1;
    const s1 = t === 2 ? G.indexOf(s) : s, k1 = 2 * s1 + r, k2 = 2 * G[s1] + r;
    box.querySelectorAll(`td[data-t="1"][data-k="${k1}"],td[data-t="3"][data-k="${k1}"],td[data-t="2"][data-k="${k2}"]`)
      .forEach(e => e.classList.add("tq-hl"));
    const a = T1[k1], b = T2[k2];
    const dir = d => d > 0 ? "right" : "left";
    say.innerHTML = a
      ? `First machine, state <b>${SN[s1]}</b> reading ${r}: write ${a.w}, move <b>${dir(a.d)}</b>, go to <b>${SN[a.q]}</b>. ` +
        `Second machine, state <b>${SN[G[s1]]}</b> reading ${r}: write ${b.w}, move <b>${dir(b.d)}</b>, go to <b>${SN[b.q]}</b>. ` +
        `Same symbol, opposite direction, and ${SN[a.q]} renamed ${SN[b.q]}.`
      : `The halting transitions match too: the first machine halts in <b>${SN[s1]}</b> on a 1, the second in <b>${SN[G[s1]]}</b> on a 1.`;
  };
  box.addEventListener("mouseover", e => { const td = e.target.closest("td[data-k]"); if (td) show(+td.dataset.t, +td.dataset.k); });
  box.addEventListener("focusin", e => { const td = e.target.closest("td[data-k]"); if (td) show(+td.dataset.t, +td.dataset.k); });
  box.addEventListener("click", e => { const td = e.target.closest("td[data-k]"); if (td) show(+td.dataset.t, +td.dataset.k); });
  $("tqBack").addEventListener("click", () => {
    const el = box.querySelector(".tq-back"); el.hidden = !el.hidden;
    $("tqBack").textContent = el.hidden ? "Translate the second table back" : "Hide the translation";
    $("tqBackSay").hidden = el.hidden;
  });
  show(1, 3);
}

// 2. Lockstep: two space-time diagrams on one clock ------------------------------------------------------------
function lockstep() {
  const c1 = $("tqLock1"), c2 = $("tqLock2"); if (!c1) return;
  let P = null, rows = [];
  function run(M) {
    P = new Pair(); rows = [];
    const H = 300, every = Math.max(1, Math.floor(M / H));
    const snap = () => {
      const a = P.a, b = P.b, q = a.hi;
      rows.push({ q, h: a.h, lo: a.lo, r1: a.t.slice(a.lo + a.o, q + a.o + 1), o1: a.lo,
        r2: Array.from({ length: q + 9 - a.lo }, (_, i) => b.get(P.mir(a.lo + i))) });
    };
    snap();
    for (let i = 1; i <= M; i++) { const r = P.step(); if (r !== "step" && r !== "cross") break; if (i % every === 0) snap(); }
    draw();
  }
  function draw() {
    const lo = Math.min(...rows.map(r => r.lo)), hi = Math.max(...rows.map(r => r.q)) + 8;
    const W = hi - lo + 1, cs = Math.max(1, Math.min(4, Math.floor(560 / W)));
    const ink = css("--ink"), acc = css("--accent"), head = css("--head"), bg = css("--cell0");
    [c1, c2].forEach((c, j) => {
      c.width = W * cs; c.height = rows.length * 2;
      const x = c.getContext("2d"); x.fillStyle = bg; x.fillRect(0, 0, c.width, c.height);
      rows.forEach((r, y) => {
        const src = j ? r.r2 : r.r1, n = j ? src.length : src.length;
        for (let i = 0; i < n; i++) {
          const p = r.lo + i;
          if (!src[i]) continue;
          x.fillStyle = j && p > r.q ? acc : ink;
          x.fillRect((p - lo) * cs, y * 2, cs, 2);
        }
        if (j && rows[y]) { x.fillStyle = acc; x.globalAlpha = .18; x.fillRect((r.q + 1 - lo) * cs, y * 2, 8 * cs, 2); x.globalAlpha = 1; }
        x.fillStyle = head; x.fillRect((r.h - lo) * cs, y * 2, cs, 2);
      });
    });
    const e = P.agree();
    $("tqLockSay").innerHTML = `${fmt(P.m)} model steps: the first machine has made <b>${fmt(P.a.n)}</b> steps, the second ` +
      `<b>${fmt(P.b.n)}</b>; <b>${fmt(P.cross)}</b> far-end crossings. ` +
      (e ? `<span class="yv-bad">They differ (${esc(e)}).</span>` : `<span class="tq-ok">The tapes agree</span>: the second is the first in a mirror, with <code>10001101</code> after q.`);
  }
  $("tqLockGo").addEventListener("click", () => run(+$("tqLockM").value));
  run(+$("tqLockM").value);
  // the long check, in slices so the page stays responsive
  let stop = true;
  $("tqLockCheck").addEventListener("click", () => {
    if (!stop) { stop = true; return; }
    stop = false; $("tqLockCheck").textContent = "Stop";
    const Q = new Pair(), goal = +$("tqLockN").value, out = $("tqLockCheckSay"); let t0 = performance.now();
    let checks = 0;
    const slice = () => {
      const end = performance.now() + 40;
      while (performance.now() < end && Q.a.n < goal && !stop) {
        for (let i = 0; i < 2000; i++) { const r = Q.step(); if (r !== "step" && r !== "cross") { stop = true; break; } }
        if (Q.cross > checks || (Q.m & 0x3fff) < 2000) { const e = Q.agree(); checks = Q.cross; if (e) { Q.bad = e; stop = true; } }
      }
      const e = Q.bad || (Q.a.n >= goal ? Q.agree() : null);
      out.innerHTML = `First machine: <b>${fmt(Q.a.n)}</b> steps; second: <b>${fmt(Q.b.n)}</b>; ${fmt(Q.cross)} far-end crossings. ` +
        (e ? `<span class="yv-bad">Mismatch: ${esc(e)}</span>` :
        Q.a.n >= goal ? `<span class="tq-ok">Agree at every crossing and at the end.</span>` : "checking ...");
      if (Q.a.n < goal && !stop) requestAnimationFrame(slice);
      else { stop = true; $("tqLockCheck").textContent = "Check the runs in lockstep"; }
    };
    slice();
  });
}

// 3. The far end: the same crossing with k extra words -------------------------------------------------------
function farEnd() {
  if (!$("tqFarA")) return;
  // the configuration before the third crossing of the real run, in the first machine's frame
  const P = new Pair(); while (P.cross < 2 || !P.crossingNow()) P.step();
  const base = P.a, q0 = base.hi;
  let k = 1, t = 0, timer = null, runs = null;
  function make() {
    const lanes = [];
    for (const kk of [0, k]) {
      const s = base.clone();
      for (let j = 0; j < kk; j++) W8.forEach((v, i) => s.set(q0 + 1 + 8 * j + i, v));
      const hist = [{ h: s.h, q: s.q, cells: snapshot(s) }];
      let n = 0;
      // run until the head is back left of q in state D with q+2 written: the crossing ends there
      do { s.step(); n++; hist.push({ h: s.h, q: s.q, cells: snapshot(s) }); } while (!(s.q === D && s.h === q0 - 1) && n < 1000);
      lanes.push({ kk, hist, n });
    }
    return lanes;
  }
  const L0 = q0 - 10;
  function snapshot(s) { const o = []; for (let p = L0; p <= q0 + 8 * k + 4; p++) o.push(s.get(p)); return o; }
  function strip(lane, j) {
    const st = lane.hist[j], n = st.cells.length, sh = j === lane.n ? 2 : 0;   // the words move 2 cells right
    let h = "";
    for (let i = 0; i < n; i++) {
      const p = L0 + i, extra = p > q0 + sh && p <= q0 + sh + 8 * lane.kk;
      const cls = ["cell", st.cells[i] ? "one" : "", extra ? "tq-x" : "", p === q0 ? "tq-q" : "", p === st.h ? "hd" : ""].join(" ");
      h += `<div class="${cls}"${p === st.h ? ` data-s="${SN[st.q]}"` : ""}></div>`;
    }
    return h;
  }
  function show() {
    const [a, b] = runs, tot = b.n, ja = Math.min(a.n, Math.round(t * a.n / tot));
    $("tqFarA").innerHTML = strip(a, ja); $("tqFarB").innerHTML = strip(b, t);
    $("tqFarAs").innerHTML = `without the word: step <b>${ja}</b> of ${a.n}, state <b>${SN[a.hist[ja].q]}</b>`;
    $("tqFarBs").innerHTML = `with ${k} word${k === 1 ? "" : "s"}: step <b>${t}</b> of ${b.n} (= 44&middot;${k} + 5), state <b>${SN[b.hist[t].q]}</b>`;
    $("tqFarT").max = tot; $("tqFarT").value = t;
    const done = t === tot;
    $("tqFarSay").innerHTML = done
      ? `<span class="tq-ok">Both are back</span> in state D, one cell left of q, with <code>1 0 1</code> written from q on. ` +
        `Every cell up to the new q (two cells further right) is the same in both, and the extra words have moved two cells right with it.`
      : t === 0 ? "Both start in state B on the 1 at q (outlined), the rightmost cell visited so far." : "";
  }
  function reset() { runs = make(); t = 0; show(); }
  $("tqFarK").addEventListener("input", e => { k = +e.target.value; $("tqFarKv").textContent = k; stopPlay(); reset(); });
  $("tqFarT").addEventListener("input", e => { stopPlay(); t = +e.target.value; show(); });
  const stopPlay = () => { if (timer) clearInterval(timer); timer = null; $("tqFarPlay").textContent = "Play"; };
  $("tqFarPlay").addEventListener("click", () => {
    if (timer) return stopPlay();
    if (t >= runs[1].n) t = 0;
    $("tqFarPlay").textContent = "Pause";
    timer = setInterval(() => { t++; show(); if (t >= runs[1].n) stopPlay(); }, Math.max(20, 1600 / runs[1].n));
  });
  $("tqFarStep").addEventListener("click", () => { stopPlay(); if (t < runs[1].n) t++; show(); });
  reset();
}

// 4. The window of four cells: the 28 abstract configurations --------------------------------------------------
function windowCheck() {
  const box = $("tqWin"); if (!box) return;
  const C = closure(T1), S = C.order;
  const idx = new Map(S.map((s, i) => [key(s), i]));
  const cellsOf = s => s.k === "inn" ? s.wl.slice().reverse().concat([s.a], s.u) : s.w;
  const label = s => s.k === "inn" ? `${SN[s.q]}, head on cell ${4 - s.u.length}` : "head left of the window";
  const card = (s, i, T) => {
    const cs = cellsOf(s), hp = s.k === "inn" ? s.wl.length : -1;
    const cross = s.k === "inn" && !s.u.length && s.q === B && s.a === 1;
    let h = `<button class="tq-card${cross ? " tq-cross" : ""}" data-i="${i}" aria-label="${label(s)}"><span class="tq-win">`;
    if (s.k === "out") h += `<i class="tq-left" data-s="?">&larr;</i>`;
    cs.forEach((v, j) => { h += `<i class="tq-c${v ? " one" : ""}${j === hp ? " hd" : ""}"${j === hp ? ` data-s="${SN[s.q]}"` : ""}></i>`; });
    h += `</span><span class="tq-lab">${s.k === "inn" ? SN[s.q] : "out &middot; back in B, D, E or F"}${cross ? " &middot; crosses" : ""}</span></button>`;
    return h;
  };
  box.innerHTML = S.map((s, i) => card(s, i)).join("");
  $("tqWinCount").textContent = S.length;
  const say = $("tqWinSay");
  function pick(i) {
    box.querySelectorAll(".tq-card").forEach(e => e.classList.remove("tq-sel", "tq-next"));
    const s = S[i]; box.querySelector(`[data-i="${i}"]`).classList.add("tq-sel");
    const nx = anext(T1, s).map(t => idx.get(key(t)));
    nx.forEach(j => box.querySelector(`[data-i="${j}"]`).classList.add("tq-next"));
    const r = s.k === "inn" ? T1[2 * s.q + s.a] : null;
    let why;
    if (s.k === "out") why = "The head is somewhere left of the window; the window keeps its four cells. The head may stay out, or come back onto the first window cell in any state that a move right can produce (B, D, E or F).";
    else if (!s.u.length && s.q === B && s.a === 1) why = "State B on a 1 at q: the far-end crossing. Both machines cross the end (5 and 49 steps) and come back in D; the window moves two cells right and reads <code>x 1 0 1</code>.";
    else if (!s.u.length) why = `At q, state ${SN[s.q]} reading ${s.a}: the move is to the <b>${r.d > 0 ? "right (would break the lockstep)" : "left"}</b>, so the runs stay together.`;
    else why = `State ${SN[s.q]} reading ${s.a}: write ${r.w}, move ${r.d > 0 ? "right" : "left"}, go to ${SN[r.q]}.`;
    say.innerHTML = `<b>${label(s)}.</b> ${why} Next: ${nx.length} configuration${nx.length === 1 ? "" : "s"}, highlighted, all in the list.`;
  }
  box.addEventListener("click", e => { const b = e.target.closest(".tq-card"); if (b) pick(+b.dataset.i); });
  pick(0);
  // follow the real run
  let R = null, timer = null;
  $("tqWinRun").addEventListener("click", () => {
    if (timer) { clearInterval(timer); timer = null; $("tqWinRun").textContent = "Follow the real run"; return; }
    if (!R) { R = new Pair(); }
    $("tqWinRun").textContent = "Pause";
    const seen = new Set();
    timer = setInterval(() => {
      for (let i = 0; i < 37; i++) { R.step(); seen.add(key(absOf(R.a))); }
      const s = absOf(R.a), i = idx.get(key(s));
      if (i === undefined) { $("tqWinRunSay").innerHTML = `<span class="yv-bad">outside the list</span>`; clearInterval(timer); return; }
      pick(i);
      $("tqWinRunSay").innerHTML = `Real run of the first machine, step <b>${fmt(R.a.n)}</b>: its window is the highlighted card. ` +
        `${seen.size} of the ${S.length} cards visited so far, none outside the list.`;
    }, 120);
  });
  // break it: flip the direction of one transition and redo the closure
  const sel = $("tqWinMut");
  for (let k = 0; k < 12; k++) if (T1[k]) {
    const t = T1[k], f = t.w + (t.d > 0 ? "L" : "R") + SN[t.q];
    sel.insertAdjacentHTML("beforeend", `<option value="${k}">${SN[k >> 1]}${k & 1}: ${t.w}${t.d > 0 ? "R" : "L"}${SN[t.q]} &rarr; ${f}</option>`);
  }
  sel.addEventListener("change", () => {
    const out = $("tqWinMutSay");
    if (sel.value === "") { out.innerHTML = ""; return; }
    const k = +sel.value, T = T1.map(x => x && Object.assign({}, x));
    T[k].d = -T[k].d;
    const R2 = closure(T);
    if (!R2.bad) { out.innerHTML = `With <code>${unparse(T)}</code> the closure ${R2.big ? "grows past 400 configurations, and the check gives up." : `still closes, with ${R2.order.length} configurations: ` +
      "the window check passes; whether the start and the far-end lemmas still hold for that table is a separate question."}`; return; }
    const path = []; let s = R2.bad; while (s) { path.unshift(s); s = R2.seen.get(key(s)).from; }
    out.innerHTML = `With <code>${unparse(T)}</code> the check <span class="yv-bad">fails</span> after ${R2.order.length} configurations: ` +
      `${label(R2.bad)} reading ${R2.bad.a ?? ""} moves right from q in a state other than B on a 1. Path from the start: ` +
      path.map(p => `<code>${esc(cellsOf(p).join(""))}${p.k === "inn" ? "/" + SN[p.q] + "@" + p.wl.length : "/out"}</code>`).join(" &rarr; ");
  });
}

function init() { tables(); lockstep(); farEnd(); windowCheck(); }
if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", init); else init();
})();
