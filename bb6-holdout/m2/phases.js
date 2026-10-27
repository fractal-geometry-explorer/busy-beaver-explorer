const { T, S } = require('./tm2.js');
const [N, from] = [+process.argv[2], +process.argv[3] || 0];
const m = new T("", 0, 0);
const rleNoHead = () => { let s=''; for (let i=m.lo;i<=m.hi;i++) s += m.t[i+m.off] ? '1':'0'; return s.replace(/(10){2,}/g, x => ` (10)^${x.length/2} `).replace(/\s+/g,' ').trim(); };
const shape = r => r.replace(/\^\d+/g, '^k');
let lastDir = 0; const ring = []; let groups = [];
while (m.steps < N) {
  ring.push(m.pos); if (ring.length > 9) ring.shift();
  if (ring.length === 9) {
    const d = Math.sign(ring[8] - ring[0]);
    if (d !== 0 && d !== lastDir) {
      if (m.steps >= from) {
        const r = rleNoHead(), sh = shape(r), side = d === -1 ? 'R-end' : 'L-end';
        const ext = lastDir === 1 ? Math.max(...ring) : Math.min(...ring);
        const g = groups[groups.length - 1];
        const rec = { step: m.steps, at: ext - m.lo, w: m.hi - m.lo, r, side };
        if (g && g.sh === sh) g.items.push(rec); else groups.push({ sh, items: [rec] });
      }
      lastDir = d;
    }
  }
  if (!m.step()) { console.log('HALT', m.steps); break; }
}
for (const g of groups) { const a = g.items[0], b = g.items[g.items.length - 1];
  console.log(`${String(g.items.length).padStart(4)}x  ${a.step}..${b.step}  first[${a.side} @${a.at}/${a.w}] ${a.r}`);
  if (g.items.length > 1) console.log(`                         last [${b.side} @${b.at}/${b.w}] ${b.r}`); }
