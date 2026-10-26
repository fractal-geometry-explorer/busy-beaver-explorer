// at every marker turn: d = cells of stripes between gap's last 0 and marker's first 1; outcome normal/swap/merge
const M = "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE";
const TR = []; M.split("_").forEach((g, s) => { for (let y = 0; y < 2; y++) { const x = g.slice(3*y, 3*y+3); TR[s*2+y] = (x === "---") ? null : { w: +x[0], d: x[1] === "R" ? 1 : -1, n: x.charCodeAt(2) - 65 }; } });
const N = +process.argv[2];
let cap = 1 << 22, t = new Uint8Array(cap), off = cap >> 1, pos = 0, st = 0, steps = 0;
const KN = k => "ABCDEF"[k >> 1] + (k & 1);
const hist = []; // last keys
const pending = []; const tab = {}; let mid = { ok: 0, bad: 0 }; const firstEp = {};
let prevKey = -1, prev2 = -1;
while (steps < N) {
  const k = st * 2 + t[pos + off];
  // detect a marker turn start: E1 reached from F1 (pass right)
  if (k === 9 && prevKey === 11) {
    const mk = pos - 1; let g = mk - 1; while (g > 2 && !(t[g+off] === 0 && t[g-1+off] === 0 && t[g-2+off] === 0)) g--;
    pending.push({ at: steps, d: mk - g - 1, mk, g });
  }
  const r = TR[k]; if (!r) { console.log('HALT', steps); break; }
  hist.push(k); if (hist.length > 24) hist.shift();
  t[pos + off] = r.w; pos += r.d; st = r.n; steps++;
  prevKey = k;
  if (pending.length && steps === pending[0].at + 21) {
    const p = pending.shift(); const seq = hist.slice(-21).map(KN).join(' ');
    let type = seq.startsWith('E1 B1 A0 B0 C1 D0 A0 B1 A1 E1 B0 C0 A1 E1 B0 C0 A0 B1 A1') ? 'swap'
      : seq.startsWith('E1 B1 A0 B0 C1 D0 A0 B1 A1 E1 B0 C0 A1 E1 B0 C1 D0 A0 B1') ? 'merge'
      : seq.startsWith('E1 B1 A0 B0 C1 D0 A0 B1 A1 E1 B0 C0 A1 E1 B0 C1 D0') ? 'normal' : 'other:' + seq;
    const key = type + ' d%4=' + (p.d % 4) + (type !== 'normal' ? ' d=' + p.d : '');
    const kk = type.startsWith('other') ? type.slice(0, 40) : (type === 'normal' ? 'normal d%4=' + (p.d % 4) : type + ' d=' + p.d);
    tab[kk] = (tab[kk] || 0) + 1;
  }
}
console.log(Object.entries(tab).sort().map(([k, v]) => v + '  ' + k).join('\n'));
