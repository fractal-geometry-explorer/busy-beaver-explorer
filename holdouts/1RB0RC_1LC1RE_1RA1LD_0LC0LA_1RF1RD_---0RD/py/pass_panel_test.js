// node py/pass_panel_test.js TRACE: the panel's passOnce() (py/pass_panel.js on py/jumps_panel.js and the
// py/gen_js.py cases) against `prun run N 1` (c/prun.c): the same zigzag start, frame count and step count after
// every pass.
const fs = require("fs"), path = require("path"), cp = require("child_process");
const here = __dirname;
const off = (s) => s.replace("if (typeof module", "if (false && typeof module");
const src = cp.execSync("python3 " + path.join(here, "gen_js.py")).toString() + "\n" +
  off(fs.readFileSync(path.join(here, "jumps_panel.js"), "utf8")) + "\n" +
  off(fs.readFileSync(path.join(here, "pass_panel.js"), "utf8"));
const {jump, passOnce} = new Function(src + "\nreturn {jump, passOnce};")();
const lines = fs.readFileSync(process.argv[2], "utf8").trim().split("\n").filter((l) => /^\d/.test(l));
let r = {t: "z", a: 0n, b: 0n, c: 2n}, frames = 0n, steps = 2n, n = 0;
const isStart = (t, a, c) => (t === "y" || t === "Y") && a >= 3n && c >= 2n;
while (!isStart(r.t, r.a, r.c)) { const s = jump(r.t, r.a, r.b, r.c); frames += s.frames; steps += s.steps; r = s; }
for (const line of lines) {
  const [np, f, s, t2, a2, b2, c2] = line.split(" ");
  const q = passOnce(r.t, r.a, r.b, r.c);
  if (q.halt) { console.log("unexpected halt at", n); process.exit(1); }
  frames += q.frames; steps += q.steps; r = q; n++;
  if (String(n) !== np || String(frames) !== f || String(steps) !== s || r.t !== t2 || String(r.a) !== a2 ||
      String(r.b) !== b2 || String(r.c) !== c2) {
    console.log("MISMATCH at pass", n, line, r.t, r.a, r.b, r.c, frames, steps); process.exit(1);
  }
}
console.log(`ok: ${n} passes, the panel's pass map agrees with c/prun.c`);
