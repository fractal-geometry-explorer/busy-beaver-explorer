const { T, S } = require('./tm2.js');
const N = +process.argv[2] || 200000, from = +process.argv[3] || 0, to = +process.argv[4] || N;
const m = new T("", 0, 0);
const keys = [], poss = [];
while (m.steps < N) { keys.push(m.key()); poss.push(m.pos); if (!m.step()) { console.log("HALT"); break; } }
// classify each step as part of L-cycle (A1 E1 B0 C0), R-cycle (E0 F1), or event
const L = ["A1","E1","B0","C0"], R = ["E0","F1"];
const lab = keys.map(() => "x");
for (let i = 0; i + 3 < keys.length; i++) if (keys[i]==="A1"&&keys[i+1]==="E1"&&keys[i+2]==="B0"&&keys[i+3]==="C0") for (let j=0;j<4;j++) lab[i+j]="L";
for (let i = 0; i + 1 < keys.length; i++) if (keys[i]==="E0"&&keys[i+1]==="F1" && lab[i]==="x" && lab[i+1]==="x") { lab[i]="R"; lab[i+1]="R"; }
// summarize runs
const cnt = {}; let i = 0; const evs = [];
while (i < keys.length) {
  let j = i; while (j + 1 < keys.length && lab[j+1] === lab[i]) j++;
  if (lab[i] === "x") { const sig = keys.slice(i, j+1).join(" "); cnt[sig] = (cnt[sig]||0) + 1; if (i >= from && i <= to) evs.push([i, sig]); }
  i = j + 1;
}
const tot = keys.length; const share = { L: 0, R: 0, x: 0 }; for (const l of lab) share[l]++;
console.log("share", Object.fromEntries(Object.entries(share).map(([k,v]) => [k, (100*v/tot).toFixed(2)+'%'])));
for (const [k, v] of Object.entries(cnt).sort((a,b)=>b[1]-a[1])) console.log(String(v).padStart(6), k);
