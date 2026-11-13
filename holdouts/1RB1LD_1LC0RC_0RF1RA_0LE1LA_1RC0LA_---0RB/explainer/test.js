// Checks of the explainer's event maps (core.js, spec.js) against the real machines, cell by cell.
//   node holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/explainer/test.js [steps]
// 1. every example of the rule viewer, over its whole slider range: the machine reaches the predicted tape;
// 2. the event orbit from blank tape: the machine passes through every event's tape, in order (default: the
//    events of the first 2*10^7 steps; 4e8 steps takes about a minute per machine and checks 457 and 467 events);
// 3. 30,000 events give a right block above 10^130 (10^137), the numbers of lean/Far.lean.
const fs=require('fs'),path=require('path');
const src=f=>fs.readFileSync(path.join(__dirname,f),'utf8');
eval(src('core.js').replace(/if\(typeof module[^\n]*/,''));eval(src('spec.js'));
const LIMIT=Number(process.argv[2]||2e7);let fail=0;
for(const [M,blankSteps,digits] of [[QS_D,14,131],[QS_C,10,138]]){
  let n=0,bad=0;
  for(const p of M.spec.presets){const want=p.label.split(/[:,]/)[0];
    const pr=p.p||[0,0,1];for(let pv=pr[0];pv<=pr[1];pv+=pr[2])for(let cv=p.c[0];cv<=p.c[1];cv++){
      const s=p.make(BigInt(pv),BigInt(cv)),info={},t=M.event(s,info);n++;
      if(!t||info.name!==want){bad++;continue;}
      const c=M.raw(s),k=M.key(t);let ok=false;while(c.n<30000){if(!M.rawstep(c))break;if(c.q===t.q&&M.rawkey(c)===k){ok=true;break;}}
      if(!ok)bad++;}}
  console.log(M.spec.anchor+'-anchor machine: rule examples',n,'failed',bad);fail+=bad;
  const c={L:[],R:[],q:'A',n:0};for(let i=0;i<blankSteps;i++)M.rawstep(c);
  if(M.rawkey(c)!==M.key(M.first)){console.log('first anchor differs');fail++;}
  let s=M.first,ok=0;const AN=M.spec.anchor;
  for(let k=1;;k++){const t=M.event(s,{});if(!t){console.log('no event at',k);fail++;break;}
    const want=M.key(t);let found=false;
    while(c.n<LIMIT){M.rawstep(c);if(c.q===AN&&(c.R.length===0||c.R[c.R.length-1]===0)&&M.rawkey(c)===want){found=true;break;}}
    if(!found){if(c.n<LIMIT){console.log('event',k,'not met');fail++;}break;}
    ok=k;s=t;}
  console.log('  event orbit agrees with the machine for',ok,'events ('+c.n+' steps)');
  s=M.first;for(let k=0;k<30000;k++)s=M.event(s,{});
  const d=String(s.r[0][1]).length;console.log('  after 30,000 events the right block has',d,'digits');if(d<digits)fail++;
}
console.log(fail?'FAILED':'ALL OK');process.exit(fail?1:0);
