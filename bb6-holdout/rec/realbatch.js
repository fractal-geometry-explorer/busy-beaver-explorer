const fs = require('fs');
const src = fs.readFileSync(__dirname + '/realf.js', 'utf8').split('const ns =')[0];
eval(src + '; global.realf = realf;');
const [a, b, stp] = process.argv.slice(2).map(Number);
const out = {};
for (let n = a; n <= b; n += stp) out[n] = realf(n, 2e10);
fs.writeFileSync(process.argv[5], JSON.stringify(out));
console.log('done', Object.keys(out).length);
