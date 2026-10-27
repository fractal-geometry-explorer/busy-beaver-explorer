const { T, S } = require('./tm2.js');
const [N, from] = [+process.argv[2], +process.argv[3] || 0];
const m = new T("", 0, 0);
let dirSmooth = 0, lastTurnPos = 0, lastDir = 0, hist = [];
// direction: use a window of last 8 positions
const ring = [];
while (m.steps < N) {
  ring.push(m.pos); if (ring.length > 9) ring.shift();
  if (ring.length === 9) {
    const d = Math.sign(ring[8] - ring[0]);
    if (d !== 0 && d !== lastDir) {
      if (m.steps >= from) {
        // find the extreme position in the window
        const ext = lastDir === 1 ? Math.max(...ring) : Math.min(...ring);
        console.log(String(m.steps).padStart(8), (d === -1 ? 'turn L at' : 'turn R at').padEnd(10), String(ext - m.lo).padStart(5), '/', String(m.hi - m.lo).padEnd(5), m.rle());
      }
      lastDir = d;
    }
  }
  if (!m.step()) { console.log('HALT', m.steps); break; }
}
