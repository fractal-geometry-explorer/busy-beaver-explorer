// run from a hand-written tape: "|" marks the head cell; args: tape state stopWhenPosLE maxSteps
const { T, S, TR } = require('./tm2.js');
function run(tape, state, stopAt, max = 400, show = false) {
  const head = tape.indexOf('|'); const cells = tape.replace('|', '');
  const m = new T(cells, head, S.indexOf(state)); const seq = [];
  while (m.steps < max && m.pos > stopAt) { seq.push(m.key()); if (show) console.log(m.str()); if (!m.step()) { return { halt: true, seq: seq.join(' '), tape: m.str() }; } }
  return { halt: false, steps: m.steps, seq: seq.join(' '), tape: m.str(0, cells.length - 1), state: S[m.st] };
}
module.exports = { run };
if (require.main === module) {
  const [tape, st, stop, max] = process.argv.slice(2);
  console.log(run(tape, st, +stop, +(max || 400)));
}
