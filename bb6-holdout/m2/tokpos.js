const { T } = require('./tm2.js');
const { tokenize } = require('./tokens.js');
const [a, b] = process.argv.slice(2).map(Number);
const m = new T('', 0, 0);
const toks = tokenize(m, a, b);
console.log(toks.map(t => `${t.s}@${t.p}:${t.t}`).join('  '));
