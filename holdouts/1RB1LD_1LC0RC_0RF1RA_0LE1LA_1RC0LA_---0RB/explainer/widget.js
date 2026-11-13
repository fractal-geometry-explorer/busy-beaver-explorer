// Interactive parts of the explainer: a rule viewer (the real machine, cell by cell) and an event-by-event stepper.
function QSW(M,P){
  var AN=M.spec.anchor,G=M.spec.gap,B=BigInt,$=function(id){return document.getElementById(P+id);};
  function css(v){return getComputedStyle(document.documentElement).getPropertyValue(v).trim()||'#888';}
  function num(x){var s=String(x);if(s.length<=12)return s.replace(/\B(?=(\d{3})+$)/g,',');
    return s[0]+'.'+s.slice(1,4)+'×10<sup>'+(s.length-1)+'</sup>';}
  function lg(x){var s=String(x);if(s==='0')return 0;return s.length-1+Math.log10(Number(s.slice(0,15))/Math.pow(10,Math.min(s.length,15)-1));}
  function runs(s){ // tape as a list of items, left to right
    var o=[],i;for(i=s.l.length-1;i>=0;i--){if(s.l[i][1]>0n)o.push({k:1,n:s.l[i][1],side:'l',near:i===0&&s.l[i][0]===0n});if(s.l[i][0]>0n)o.push({k:0,n:s.l[i][0]});}
    o.push({k:'h'});
    for(i=0;i<s.r.length;i++){if(s.r[i][0]>0n)o.push({k:0,n:s.r[i][0]});if(s.r[i][1]>0n)o.push({k:1,n:s.r[i][1],side:'r',near:i===0});}
    return o;}
  function text(s,q){return runs(s).map(function(r){
      if(r.k==='h')return '<b style="color:var(--head)">'+(q||s.q)+'&gt;</b>';
      if(r.k===0)return r.n>4n?'0<sup>'+r.n+'</sup>':Array(Number(r.n)+1).join('0 ').trim();
      return '1<sup>'+num(r.n)+'</sup>';}).join(' ');}
  function total(s){var t=0n;s.l.concat(s.r).forEach(function(p){t+=p[1];});return t;}
  function strip(el,s){
    var rs=runs(s),tot=total(s),h='';if(tot===0n)tot=1n;
    rs.forEach(function(r){
      if(r.k==='h'){h+='<div style="flex:0 0 3px;background:var(--head);align-self:stretch;position:relative"><span style="position:absolute;top:-18px;left:-4px;color:var(--head);font:600 12px var(--mono)">'+s.q+'</span></div>';return;}
      if(r.k===0){h+='<div style="flex:0 0 '+(3*Math.min(Number(r.n),5))+'px"></div>';return;}
      var col=r.near?(r.side==='l'?'var(--accent)':'var(--kernel)'):'var(--muted)';
      h+='<div title="'+String(r.n)+' ones" style="flex:'+(Number(r.n*100000n/tot)+1)+' 1 0;min-width:7px;background:'+col+';border-radius:3px"></div>';});
    el.innerHTML=h;}

  /* ---------- rule viewer ---------- */
  var presets=M.spec.presets,sel=$('rule'),pin=$('p'),cin=$('c');
  presets.forEach(function(p,i){var o=document.createElement('option');o.value=i;o.textContent=p.label;sel.appendChild(o);});
  function setRanges(){var p=presets[+sel.value];
    $('prow').style.display=p.p?'':'none';
    if(p.p){pin.min=p.p[0];pin.max=p.p[1];pin.step=p.p[2];pin.value=p.p[3];$('plab').textContent=p.plab;}
    cin.min=p.c[0];cin.max=p.c[1];cin.value=p.c[2];}
  function drawRule(){
    var p=presets[+sel.value],pv=B(pin.value||0),cv=B(cin.value);
    $('pval').textContent=pv;$('cval').textContent=cv;
    var s=p.make(pv,cv),info={},t=M.event(s,info),msg=$('rmsg'),cv2=$('canvas');
    $('before').innerHTML=text(s);
    if(!t){$('after').innerHTML='(no rule for these numbers)';msg.textContent='';return;}
    $('after').innerHTML=text(t);
    var c=M.raw(s),pos=0,rows=[],want=M.key(t),ok=false,lo=-c.L.length,hi=c.R.length;
    function snap(){rows.push({pos:pos,L:c.L.slice(),R:c.R.slice()});lo=Math.min(lo,pos-c.L.length,pos);hi=Math.max(hi,pos+c.R.length,pos+1);}
    snap();
    while(c.n<30000){var x=c.R.length?c.R[c.R.length-1]:0,d=M.spec.table[c.q][x];if(!d)break;M.rawstep(c);pos+=d[1]==='R'?1:-1;snap();
      if(c.q===t.q&&M.rawkey(c)===want){ok=true;break;}}
    lo-=1;hi+=1;
    var cols=hi-lo,W=Math.min(cv2.parentNode.clientWidth||640,720),cw=Math.max(2,Math.min(12,Math.floor(W/cols))),rh=Math.max(1,Math.min(cw,Math.floor(1500/rows.length)));
    var dpr=window.devicePixelRatio||1;cv2.width=cols*cw*dpr;cv2.height=rows.length*rh*dpr;cv2.style.width=cols*cw+'px';cv2.style.height=rows.length*rh+'px';
    var g=cv2.getContext('2d');g.scale(dpr,dpr);g.fillStyle=css('--cell0');g.fillRect(0,0,cols*cw,rows.length*rh);
    var one=css('--ink'),head=css('--head');
    rows.forEach(function(r,y){g.fillStyle=one;var i,xx;
      for(i=0;i<r.L.length;i++)if(r.L[r.L.length-1-i]){xx=r.pos-1-i-lo;g.fillRect(xx*cw,y*rh,cw,rh);}
      for(i=0;i<r.R.length;i++)if(r.R[r.R.length-1-i]){xx=r.pos+i-lo;g.fillRect(xx*cw,y*rh,cw,rh);}
      g.fillStyle=head;g.fillRect((r.pos-lo)*cw,y*rh,cw,Math.max(rh,2));});
    msg.innerHTML=ok?'The real machine goes from the first line to the second in <b>'+c.n.toLocaleString('en')+' steps</b>. Each row of the picture is one step (time runs down); dark cells are 1s, the coloured cell is the head. Lean: <code>'+p.lean+'</code>.':'The run did not reach the predicted tape within 30,000 steps.';
    $('rwords').innerHTML=p.words;}
  sel.addEventListener('change',function(){setRanges();drawRule();});
  pin.addEventListener('input',drawRule);cin.addEventListener('input',drawRule);
  setRanges();drawRule();

  /* ---------- the run, event by event ---------- */
  var st,k,hist,tally,folds,timer=null,last;
  function reset(){st=M.first;k=0;hist=[[0,lg(total(st))]];tally={};folds=0;last=null;show();}
  function one(){var info={},b=M.anchor(st),t=M.event(st,info);if(!t)return false;
    last={name:info.name,passed:info.passed||0,carrier:info.carrier,b:b,before:st,after:t};
    st=t;k++;tally[info.name]=(tally[info.name]||0)+1;if(info.name==='fold')folds++;
    if(hist.length<400000)hist.push([k,lg(total(st))]);return true;}
  function words(e){var m=e.b.m,c=e.b.c,q=m/4n,n=e.name,z=G===2?'two 0s':'three 0s',car=e.carrier?' The head then runs right as the carrier <code>0 1</code>'+(e.passed?', passes '+e.passed+' block'+(e.passed>1?'s':''):'')+' and turns into three 1s at the first pair of 0s (or the end of the tape).':'';
    if(n==='split')return '<b>Split.</b> The left block, '+num(m)+' ones, is even and has '+z+' on its left. A quarter of it, '+num(q)+', goes to the far side of the gap; three quarters, '+num(3n*q)+', go to the right block; '+(m%4n)+' stay.';
    if(n==='odd')return '<b>Odd round.</b> The left block, '+num(m)+' ones, is odd. It loses 2, the 0 on its left becomes a 1, and the right block gains 3'+(e.b.Y.length&&e.b.Y[0][0]===1n?'. That closed the gap, so two blocks merged.':'.');
    if(n==='fold')return '<b>Fold.</b> The odd block of '+num(m)+' ones is the whole left part of the tape. It is used up two at a time, and every two become three on the right: the right block grows by '+num(3n*(m/2n))+'. This is where the tape grows by half.';
    if(n==='shift')return '<b>Shift.</b> The left block, '+num(m)+' ones, is even and too close to its neighbour to be split. The head steps over it: the block (minus one) is now on the right of the head, and the head faces the next block to the left.';
    if(n==='zero')return '<b>Empty left.</b> There is no block next to the head on the left. The right block passes one 1 across the gap and moves over.'+car;
    if(n==='two')return G===2?'<b>Two left.</b> Only two 1s remain of a split block. They are erased, one 1 crosses the gap, and the right block moves over.'+car:'<b>Two left.</b> Only two 1s remain of a split block. They cross the gap and join the block on the far side; the right block gains 1.';
    if(n==='one')return '<b>One left.</b> A single 1 is next to the head. It hops across the gap.'+car;
    if(n==='oneE'||n==='zeroE')return '<b>Remainder next to an even block.</b> The small remainder is absorbed into the even block behind it.'+car;
    if(n==='oneO'||n==='zeroO')return '<b>Remainder next to an odd block.</b> The head steps back over the odd block behind it, which is now on the right of the head.';
    return n;}
  function chart(){var cv=$('chart'),W=Math.min(cv.parentNode.clientWidth||640,720),H=150,dpr=window.devicePixelRatio||1;
    cv.width=W*dpr;cv.height=H*dpr;cv.style.width=W+'px';cv.style.height=H+'px';var g=cv.getContext('2d');g.scale(dpr,dpr);g.clearRect(0,0,W,H);
    var n=hist.length,ymax=Math.max(1,hist[n-1][1]),xmax=Math.max(1,hist[n-1][0]),stepi=Math.max(1,Math.floor(n/1500));
    g.strokeStyle=css('--line');g.beginPath();g.moveTo(34,6);g.lineTo(34,H-18);g.lineTo(W-4,H-18);g.stroke();
    g.fillStyle=css('--muted');g.font='11px sans-serif';g.fillText('10^'+ymax.toFixed(ymax<10?1:0),0,12);g.fillText('1',22,H-18);g.fillText('event '+xmax.toLocaleString('en'),W-90,H-4);g.fillText('0',34,H-4);
    g.strokeStyle=css('--accent');g.lineWidth=1.5;g.beginPath();
    for(var i=0;i<n;i+=stepi){var x=34+(W-40)*hist[i][0]/xmax,y=H-18-(H-26)*hist[i][1]/ymax;if(i)g.lineTo(x,y);else g.moveTo(x,y);}
    g.lineTo(34+(W-40),H-18-(H-26)*hist[n-1][1]/ymax);g.stroke();}
  function show(){strip($('strip'),st);$('tape').innerHTML=text(st);
    $('count').innerHTML='Event <b>'+k.toLocaleString('en')+'</b> &middot; '+num(total(st))+' ones on the tape &middot; '+folds.toLocaleString('en')+(folds===1?' fold':' folds')+' so far';
    $('what').innerHTML=last?words(last):'This is the first anchor, reached '+M.spec.firstSteps+' steps after the start on a blank tape. Press <b>Next event</b>.';
    var names=Object.keys(tally).sort(function(a,b){return tally[b]-tally[a];});
    $('tally').innerHTML=names.map(function(n){return '<span style="display:inline-block;margin:2px 6px 2px 0;padding:1px 8px;border:1px solid var(--line);border-radius:10px">'+n+' <b>'+tally[n].toLocaleString('en')+'</b></span>';}).join('');
    chart();}
  function go(n){for(var i=0;i<n;i++)if(!one()){$('what').innerHTML='No event rule applies here.';break;}show();}
  function stop(){if(timer){clearInterval(timer);timer=null;$('play').textContent='Play';}}
  $('next').addEventListener('click',function(){stop();go(1);});
  $('n10').addEventListener('click',function(){stop();go(10);});
  $('n1000').addEventListener('click',function(){stop();go(1000);});
  $('n30000').addEventListener('click',function(){stop();go(30000);});
  $('fold').addEventListener('click',function(){stop();for(var i=0;i<100000;i++){if(!one())break;if(last.name==='fold')break;}show();});
  $('reset').addEventListener('click',function(){stop();reset();});
  $('play').addEventListener('click',function(){if(timer){stop();return;}$('play').textContent='Pause';timer=setInterval(function(){go(1);},600);});
  reset();
}
