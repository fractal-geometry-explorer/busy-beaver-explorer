// token stream: cycles L (A1 E1 B0 C0), R (E0 F1), S (A0 B1) with repeat counts, events in [..]
const { T, S } = require('./tm2.js');
function tokenize(m, a, b) {
  while (m.steps < a) m.step();
  const keys = [], st = [], pos = [];
  while (m.steps < b) { keys.push(m.key()); st.push(m.steps); pos.push(m.pos - m.lo); if (!m.step()) { keys.push('HALT'); break; } }
  const lab = keys.map(() => 'x');
  const cyc = (pat, name) => { for (let i = 0; i + pat.length - 1 < keys.length; i++) { let ok = true; for (let j = 0; j < pat.length; j++) if (keys[i+j] !== pat[j] || lab[i+j] !== 'x') { ok = false; break; } if (ok) { for (let j = 0; j < pat.length; j++) lab[i+j] = name; i += pat.length - 1; } } };
  cyc(['A1','E1','B0','C0'], 'L'); cyc(['A0','B1'], 'S'); cyc(['E0','F1'], 'R');
  const toks = []; let i = 0;
  const per = { L: 4, S: 2, R: 2 };
  while (i < keys.length) { let j = i; while (j + 1 < keys.length && lab[j+1] === lab[i]) j++;
    if (lab[i] === 'x') toks.push({ t: '[' + keys.slice(i, j+1).join(' ') + ']', s: st[i], p: pos[i] });
    else toks.push({ t: lab[i] + ((j - i + 1) / per[lab[i]]), s: st[i], p: pos[i] });
    i = j + 1; }
  return toks;
}
module.exports = { tokenize };
if (require.main === module) {
  const [a, b] = process.argv.slice(2).map(Number);
  const toks = tokenize(new T('', 0, 0), a, b);
  console.log(toks.map(t => t.t).join(' '));
}
