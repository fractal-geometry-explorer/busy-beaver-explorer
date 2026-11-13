// Event maps of the quarter-split pair, transcribed from lean/Events.lean (evT, arr, event, rstep).
// A side is an array of [zeros, ones] pairs (BigInt), nearest the head first.
function QS(spec){
  var G=spec.gap, AN=spec.anchor, T=spec.table;
  function hd(s){for(var i=0;i<s.length;i++){if(s[i][0]>0n)return 0;if(s[i][1]>0n)return 1;}return 0;}
  function pop(s){for(var i=0;i<s.length;i++){var g=s[i][0],b=s[i][1];
      if(g>0n)return [[g-1n,b]].concat(s.slice(i+1));
      if(b>1n)return [[0n,b-1n]].concat(s.slice(i+1));
      if(b===1n)return s.slice(i+1);}
    return [];}
  function push1s(n,s){if(s.length&&s[0][0]===0n)return [[0n,s[0][1]+n]].concat(s.slice(1));
    return n===0n?s:[[0n,n]].concat(s);}
  function push0s(n,s){if(!s.length)return [];return [[s[0][0]+n,s[0][1]]].concat(s.slice(1));}
  function push(x,s){return x?push1s(1n,s):push0s(1n,s);}
  function popn(k,s){for(var i=0;i<k;i++)s=pop(s);return s;}
  function arr(l,Z,info){
    for(;;){
      if(!Z.length)return {l:l,q:AN,r:[[1n,3n]]};
      var g=Z[0][0],b=Z[0][1],rest=Z.slice(1);
      if(g===1n&&b>=2n){l=push1s(b,push0s(1n,l));Z=rest;if(info)info.passed=(info.passed||0)+1;continue;}
      if(g===2n)return {l:l,q:AN,r:[[1n,b+3n]].concat(rest)};
      if(g>=3n)return {l:l,q:AN,r:[[1n,3n],[g-2n,b]].concat(rest)};
      return null;}}
  // the event at the anchor  Y 1^m AN> 0 1^c Z
  function evT(Y,m,c,Z,info){
    function car(l){info.carrier=true;return arr(l,Z,info);}
    if(hd(Y))return null;
    var P=pop(Y);
    function single(name,add){ // a lone 0 (variant B, m=0) or lone 1 with a block behind one 0
      if(P.length&&P[0][0]===0n){var a=P[0][1],Y1=P.slice(1);
        if(hd(Y1))return null;
        if(a%2n===0n){info.name=name+'E';if(a>=2n&&c>=2n)return car(push1s(c,push0s(1n,push1s(a+add,pop(Y1)))));return null;}
        info.name=name+'O';return {l:pop(Y1),q:AN,r:[[1n,a+add+1n],[1n,c]].concat(Z)};}
      return null;}
    if(m===0n){
      if(G===3){
        if(hd(P))return single('zero',0n);
        info.name='zero';if(c>=3n)return car(push1s(c-3n,push0s(3n,push1s(1n,pop(P)))));return null;}
      info.name='zero';if(c>=3n)return car(push1s(c-3n,push0s(2n,push1s(1n,P))));return null;}
    if(m===1n){
      if(hd(P))return single('one',1n);
      info.name='one';if(c>=2n)return car(push1s(c,push0s(1n,push1s(1n,pop(P)))));return null;}
    if(m%2n===1n){
      if(!Y.length){info.name='fold';return {l:[[0n,1n]],q:AN,r:[[1n,c+3n*(m/2n)]].concat(Z)};}
      info.name='odd';return {l:push1s(m-2n,P),q:AN,r:[[1n,c+3n]].concat(Z)};}
    if(G===2?hd(P):(hd(P)||hd(pop(P)))){info.name='shift';return {l:P,q:AN,r:[[1n,m-1n],[2n,c]].concat(Z)};}
    if(m===2n){info.name='two';
      if(G===2){if(c>=2n)return car(push1s(c-2n,push0s(4n,push1s(1n,pop(P)))));return null;}
      return {l:push0s(2n,push1s(2n,popn(3,Y))),q:AN,r:[[1n,c+1n]].concat(Z)};}
    info.name='split';
    return {l:push1s(m%4n,push0s(BigInt(G),push1s(m/4n,popn(G,Y)))),q:AN,r:[[1n,c+3n*(m/4n)]].concat(Z)};}
  function anchor(s){ // {Y,m,c,Z} if s is an anchor
    if(s.q!==AN||!s.r.length||s.r[0][0]!==1n)return null;
    if(s.l.length&&s.l[0][0]===0n)return {Y:s.l.slice(1),m:s.l[0][1],c:s.r[0][1],Z:s.r.slice(1)};
    return {Y:s.l,m:0n,c:s.r[0][1],Z:s.r.slice(1)};}
  function event(s,info){info=info||{};var a=anchor(s);if(!a)return null;return evT(a.Y,a.m,a.c,a.Z,info);}
  function rstep(s){var t=T[s.q][hd(s.r)];if(!t)return null;
    if(t[1]==='R')return {l:push(t[0],s.l),q:t[2],r:pop(s.r)};
    return {l:pop(s.l),q:t[2],r:push(hd(s.l),push(t[0],pop(s.r)))};}
  function cells(side){var o=[];for(var i=0;i<side.length;i++){for(var k=0n;k<side[i][0];k++)o.push(0);for(k=0n;k<side[i][1];k++)o.push(1);}return o;}
  // raw machine on cells: left array (nearest last), right array reversed (head cell last)
  function raw(s){return {L:cells(s.l).reverse(),R:cells(s.r).reverse(),q:s.q,n:0};}
  function rawstep(c){var x=c.R.length?c.R.pop():0,t=T[c.q][x];if(!t){c.R.push(x);return false;}
    if(t[1]==='R'){c.L.push(t[0]);}else{c.R.push(t[0]);c.R.push(c.L.length?c.L.pop():0);}
    c.q=t[2];c.n++;return true;}
  function strip(a){var i=0;while(i<a.length&&a[i]===0)i++;return a.slice(i);}
  function rawkey(c){return strip(c.L).join('')+c.q+strip(c.R).slice().reverse().join('');}
  function key(s){return rawkey(raw(s));}
  return {hd:hd,pop:pop,push1s:push1s,push0s:push0s,arr:arr,evT:evT,anchor:anchor,event:event,rstep:rstep,raw:raw,rawstep:rawstep,rawkey:rawkey,key:key,cells:cells,first:{l:[[0n,1n]],q:AN,r:[[1n,3n]]},spec:spec};
}
function parseTM(s){var o={};s.split('_').forEach(function(row,i){var q='ABCDEF'[i];o[q]=[0,1].map(function(b){var t=row.substr(3*b,3);return t[0]==='-'?null:[+t[0],t[1],t[2]];});});return o;}
var QS_D=QS({gap:2,anchor:'D',table:parseTM('1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB')});
var QS_C=QS({gap:3,anchor:'C',table:parseTM('1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB')});
if(typeof module!=='undefined')module.exports={QS_D:QS_D,QS_C:QS_C};
