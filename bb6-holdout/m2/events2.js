const { T, S } = require('./tm2.js');
const N = +process.argv[2] || 200000;
const m = new T("", 0, 0);
const keys = [], poss = [];
while (m.steps < N) { keys.push(m.key()); poss.push(m.pos); if (!m.step()) { console.log("HALT"); break; } }
const lab = keys.map(() => "x");
const cyc = (pat, name) => { for (let i = 0; i + pat.length - 1 < keys.length; i++) { let ok = true; for (let j = 0; j < pat.length; j++) if (keys[i+j] !== pat[j] || lab[i+j] !== "x") { ok = false; break; } if (ok) for (let j = 0; j < pat.length; j++) lab[i+j] = name; } };
cyc(["A1","E1","B0","C0"], "L");   // carry left
cyc(["A0","B1"], "S");             // shift right
cyc(["E0","F1"], "R");             // pass right
const cnt = {}; let i = 0;
while (i < keys.length) {
  let j = i; while (j + 1 < keys.length && lab[j+1] === lab[i]) j++;
  if (lab[i] === "x") { const sig = keys.slice(i, j+1).join(" "); cnt[sig] = (cnt[sig]||0) + 1; }
  i = j + 1;
}
const share = { L: 0, R: 0, S: 0, x: 0 }; for (const l of lab) share[l]++;
console.log("share", Object.fromEntries(Object.entries(share).map(([k,v]) => [k, (100*v/keys.length).toFixed(2)+'%'])));
for (const [k, v] of Object.entries(cnt).sort((a,b)=>b[1]-a[1]).slice(0, 30)) console.log(String(v).padStart(7), k);
// transitions between modes: sequence of (mode or event) tokens, count bigram patterns
const seq = []; i = 0;
while (i < keys.length) { let j = i; while (j + 1 < keys.length && lab[j+1] === lab[i]) j++; seq.push(lab[i] === "x" ? "[" + keys.slice(i, j+1).join(" ") + "]" : lab[i]); i = j + 1; }
const tri = {}; for (let k = 0; k + 2 < seq.length; k++) { if (seq[k+1][0] !== "[") continue; const key = seq[k] + " " + seq[k+1] + " " + seq[k+2]; tri[key] = (tri[key]||0) + 1; }
console.log("--- event contexts (mode before, event, mode after)");
for (const [k, v] of Object.entries(tri).sort((a,b)=>b[1]-a[1]).slice(0, 20)) console.log(String(v).padStart(7), k);
