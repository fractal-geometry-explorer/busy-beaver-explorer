// The pass map of lean/Pass.lean on BigInt, and the panel of the explainer section "passes".
// Needs jump() and rowDistance() of py/jumps_panel.js (the section "jumps" loads them first).
// node py/pass_panel_test.js compares passOnce() with `prun run N 1` (c/prun.c).

// growth table by [Y?][a mod 3][j odd]: target tag, c, d, frames constant f, steps s0, s1, s2 (c/prun.c, lean/Pass.lean)
const PASS_G = {
  y: [[["y", 2n, 1n, 8n, 17n, 19n, 7n], ["y", 5n, 4n, 7n, 15n, 19n, 7n]],
      [["y", 7n, 4n, 8n, 20n, 19n, 7n], ["y", 4n, 1n, 9n, 22n, 19n, 7n]],
      [["Y", 2n, 1n, 6n, 29n, 19n, 7n], ["Y", 5n, 4n, 5n, 27n, 19n, 7n]]],
  Y: [[["y", 5n, 1n, 6n, 17n, 19n, 7n], ["y", 8n, 4n, 5n, 15n, 19n, 7n]],
      [["y", 11n, 5n, 14n, 47n, 27n, 11n], ["y", 8n, 2n, 15n, 49n, 27n, 11n]], null],
};
const isStart = (t, a, c) => (t === "y" || t === "Y") && a >= 3n && c >= 2n;

// one pass from a zigzag start: {t, a, b, c, frames, steps, kind, jumps} or {halt, steps}
function passOnce(t, a, b, c) {
  const q = a / 3n, e = a % 3n;
  if (c + 1n <= q) {
    return {t, a: a - 3n * c + 1n, b: 0n, c: 4n * c + 2n * b + 2n, frames: b + 4n * c - 1n,
            steps: 3n + 2n * b + 9n * c + 4n * b * c + 4n * c * c, kind: "drain", jumps: 0n};
  }
  if (c >= q + 7n) {
    if (t === "Y" && e === 2n) {
      return {t: "y", a: 5n, b: b + 2n * q + 2n, c: c - q - 1n, frames: 2n + 2n * q,
              steps: 35n + 13n * q + 4n * b + 4n * q * q + 4n * q * b, kind: "growth", jumps: 0n};
    }
    const g = PASS_G[t][Number(e)][Number(b & 1n)];
    return {t: g[0], a: 4n * q + 2n * b + g[1], b: 0n, c: c - q - g[2], frames: 3n * q + (b + g[3]) / 2n,
            steps: g[4] + g[5] * q + g[6] * b + 4n * q * q + 4n * q * b, kind: "growth", jumps: 0n};
  }
  // near the boundary c = q: jumps to the next zigzag start
  let r = {t, a, b, c}, frames = 0n, steps = 0n, n = 0n;
  do {
    const s = jump(r.t, r.a, r.b, r.c);
    if (s.halt) return {halt: s.halt, steps: steps + s.steps};
    frames += s.frames; steps += s.steps; n++; r = s;
  } while (!isStart(r.t, r.a, r.c));
  return {t: r.t, a: r.a, b: r.b, c: r.c, frames, steps, kind: "near the boundary", jumps: n};
}

if (typeof module !== "undefined") module.exports = {passOnce};

(function () {
  if (typeof document === "undefined") return;
  const root = document.getElementById("passPanel");
  if (!root) return;
  const NS = "http://www.w3.org/2000/svg";
  const fmt = (x) => {
    const s = x.toString();
    if (s.length <= 15) return s.replace(/\B(?=(\d{3})+(?!\d))/g, ",");
    return s[0] + "." + s.slice(1, 4) + "&middot;10<sup>" + (s.length - 1) + "</sup>";
  };
  const svg = root.querySelector("svg.cob");
  const P = 20, Z = 260;                         // plot origin and size in the 300 x 300 view box
  const X = (x) => P + Z * x, Y = (y) => P + Z * (1 - y);
  const web = svg.querySelector(".web"), dots = svg.querySelector(".dots");
  let S;
  function xOf(a, b, c) { return Number(a) / Number(a + b + c); }
  function reset() {
    // the first zigzag start of the run from blank tape (2 machine steps, then frun's jumps)
    let r = {t: "z", a: 0n, b: 0n, c: 2n}, frames = 0n, steps = 2n;
    while (!isStart(r.t, r.a, r.c)) { const s = jump(r.t, r.a, r.b, r.c); frames += s.frames; steps += s.steps; r = s; }
    S = {t: r.t, a: r.a, b: r.b, c: r.c, passes: 0n, frames, steps, halted: null, pts: [xOf(r.a, r.b, r.c)], log: [],
         near: 0n, growth: 0n, drain: 0n, best: null};
    draw();
  }
  function one() {
    if (S.halted) return false;
    const t0 = S.t, a0 = S.a, b0 = S.b, c0 = S.c;
    const d = rowDistance(t0, a0, b0, c0);
    if (d !== null) {
      const ad = d < 0n ? -d : d;
      if (S.best === null || ad <= S.best.ad) S.best = {ad, pass: S.passes + 1n};
    }
    const r = passOnce(S.t, S.a, S.b, S.c);
    S.passes += 1n;
    if (r.halt) { S.halted = r.halt; return false; }
    if (r.kind === "drain") S.drain++; else if (r.kind === "growth") S.growth++; else S.near++;
    S.log.push(`${fmt(S.passes)}: ${t0}(${a0}, ${b0}, ${c0}) &rarr; ${r.t}(${r.a}, ${r.b}, ${r.c}), ${r.kind}` +
               (r.jumps ? ` (${r.jumps} jumps)` : "") + (d !== null && (d < 0n ? -d : d) <= 4n ? `, halting row at distance ${d}` : ""));
    if (S.log.length > 12) S.log.shift();
    S.t = r.t; S.a = r.a; S.b = r.b; S.c = r.c; S.frames += r.frames; S.steps += r.steps;
    S.pts.push(xOf(r.a, r.b, r.c)); if (S.pts.length > 40) S.pts.shift();
    return true;
  }
  function run(n) { for (let i = 0; i < n; i++) if (!one()) break; draw(); }
  function draw() {
    let p = "";
    for (let i = 0; i + 1 < S.pts.length; i++) {
      const u = S.pts[i], v = S.pts[i + 1];
      p += `M${X(u).toFixed(1)},${Y(u).toFixed(1)}V${Y(v).toFixed(1)}H${X(v).toFixed(1)}`;
    }
    web.setAttribute("d", p);
    while (dots.firstChild) dots.removeChild(dots.firstChild);
    S.pts.forEach((u, i) => {
      const c = document.createElementNS(NS, "circle");
      c.setAttribute("cx", X(u).toFixed(1)); c.setAttribute("cy", (P + Z + 8).toFixed(1));
      c.setAttribute("r", i === S.pts.length - 1 ? "3.5" : "2");
      c.setAttribute("fill", i === S.pts.length - 1 ? "var(--accent)" : "var(--muted)");
      dots.appendChild(c);
    });
    const N = S.a + S.b + S.c;
    root.querySelector(".pstate").innerHTML =
      `<b>${S.t}(${S.a}, ${S.b}, ${S.c})</b>: N = a + j + r = ${fmt(N)}, x = a/N = ${xOf(S.a, S.b, S.c).toFixed(6)}`;
    root.querySelector(".pcount").innerHTML =
      `${fmt(S.passes)} passes (${fmt(S.growth)} growth, ${fmt(S.drain)} drain, ${fmt(S.near)} near the boundary), ` +
      `${fmt(S.frames)} frames, ${fmt(S.steps)} machine steps` +
      (S.best ? `; closest halting row so far: distance ${S.best.ad} at pass ${fmt(S.best.pass)}` : "") +
      (S.halted ? `; <b>halted</b> (${S.halted})` : "");
    root.querySelector(".plog").innerHTML = S.log.join("<br>");
  }
  root.querySelector(".p1").onclick = () => run(1);
  root.querySelector(".p10").onclick = () => run(10);
  root.querySelector(".p1k").onclick = () => run(1000);
  root.querySelector(".p100k").onclick = () => run(100000);
  root.querySelector(".preset").onclick = reset;
  reset();
})();
