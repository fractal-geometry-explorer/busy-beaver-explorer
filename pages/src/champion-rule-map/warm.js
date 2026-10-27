const { Sim, TR, SNAME } = require(process.argv[2] + '/engine.js');
const N = +process.argv[3] || 821;
const s = new Sim('real');
const lo = -12, hi = 50;
const tape = () => { let r=''; for (let i=lo;i<=hi;i++){ const c=s.t[i+s.off]; r += i===s.pos ? (c?'¹':'⁰') : c; } return r; };
const ev=[];
while (s.steps < N) { ev.push({step:s.steps,k:SNAME[s.st]+s.t[s.pos+s.off],tape:tape(),pos:s.pos}); if(!s.step()) break; }
ev.push({step:s.steps,k:SNAME[s.st]+s.t[s.pos+s.off],tape:tape(),pos:s.pos});
// motif segmentation like motif.js, printing tape at segment starts
let i=0;
const inW=k=>['C0','D1','E1'].includes(k), inR=k=>k==='A1', inX=k=>['C1','F1','E1'].includes(k);
const cyc = (a,b,arr)=>{ const ia=arr.indexOf(a), ib=arr.indexOf(b); return ib===(ia+1)%arr.length; };
while(i<ev.length-1){
  let j=i, name=null;
  if (inR(ev[i].k)) { while(j<ev.length&&inR(ev[j].k)) j++; name='RUN'; }
  else if (inW(ev[i].k) && ev[i+1] && cyc(ev[i].k, ev[i+1].k, ['C0','D1','E1'])) { j=i+1; while(j<ev.length&&inW(ev[j].k)&&cyc(ev[j-1].k,ev[j].k,['C0','D1','E1'])) j++; name='CRAWL'; }
  else if (inX(ev[i].k) && ev[i+1] && cyc(ev[i].k, ev[i+1].k, ['C1','F1','E1'])) { j=i+1; while(j<ev.length&&inX(ev[j].k)&&cyc(ev[j-1].k,ev[j].k,['C1','F1','E1'])) j++; name='RECODE'; }
  if (name && j-i>=3) { console.log(String(ev[i].step).padStart(4), (name+' x'+(j-i)).padEnd(12), ev[i].tape); i=j; continue; }
  // singles: gather until next motif
  let k=i, ks=[]; 
  while(k<ev.length-1){ const a=ev[k].k, b=ev[k+1]&&ev[k+1].k; if ((inR(a))|| (inW(a)&&b&&cyc(a,b,['C0','D1','E1'])&&ev[k+2]&&cyc(b,ev[k+2].k,['C0','D1','E1'])) || (inX(a)&&b&&cyc(a,b,['C1','F1','E1'])&&ev[k+2]&&cyc(b,ev[k+2].k,['C1','F1','E1']))) break; ks.push(a); k++; }
  if (k===i){ ks.push(ev[i].k); k=i+1; }
  console.log(String(ev[i].step).padStart(4), ks.join(' ').padEnd(12), ev[i].tape); i=k;
}
console.log(String(ev[ev.length-1].step).padStart(4), 'END'.padEnd(12), ev[ev.length-1].tape);
