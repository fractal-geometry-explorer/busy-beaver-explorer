// node py/jumps_panel_test.js TRACE: the panel's jump() (py/gen_js.py cases + py/jumps_panel.js) against the
// lines of `frun trace N` (c/frun.c): the same frame, frame count and step count after every jump.
const fs = require("fs"), path = require("path"), cp = require("child_process");
const here = __dirname;
const src = cp.execSync("python3 " + path.join(here, "gen_js.py")).toString() + "\n" +
  fs.readFileSync(path.join(here, "jumps_panel.js"), "utf8").replace("if (typeof module", "if (false && typeof module");
const {jump} = new Function(src + "\nreturn {jump};")();
const lines = fs.readFileSync(process.argv[2], "utf8").trim().split("\n").filter((l) => !l.startsWith("END"));
let t = "z", a = 0n, b = 0n, c = 2n, frames = 0n, steps = 2n, n = 0;
for (const line of lines) {
  const [f, s, t2, a2, b2, c2] = line.split(" ");
  const r = jump(t, a, b, c);
  if (r.halt) { console.log("unexpected halt at", n); process.exit(1); }
  frames += r.frames; steps += r.steps; t = r.t; a = r.a; b = r.b; c = r.c; n++;
  if (String(frames) !== f || String(steps) !== s || t !== t2 || String(a) !== a2 || String(b) !== b2 || String(c) !== c2) {
    console.log("MISMATCH at jump", n, line, t, a, b, c, frames, steps); process.exit(1);
  }
}
console.log(`ok: ${n} jumps, the panel's jump map agrees with c/frun.c`);
