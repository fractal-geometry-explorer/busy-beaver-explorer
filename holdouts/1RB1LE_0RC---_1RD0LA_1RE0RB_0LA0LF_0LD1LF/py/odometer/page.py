"""Write the odometer sections and results into ../../status.json (then: python3 holdouts/build_pages.py MACHINE).

    python3 page.py

Reads ../../data/odometer/summary.json and visits_sample.json (from far.py and sample.py)."""
import json, os
HERE = os.path.dirname(os.path.abspath(__file__))
MD = os.path.join(HERE, '..', '..')
SP = os.path.join(MD, 'status.json')
spec = json.load(open(SP))
summ = json.load(open(os.path.join(MD, 'data', 'odometer', 'summary.json')))
samp = json.load(open(os.path.join(MD, 'data', 'odometer', 'visits_sample.json')))
D = summ['digits'] - 1
RUNS = samp['runouts']

RULES = '''<div style="overflow-x:auto"><table class="tbl"><thead><tr><th>wall</th><th>digit</th><th>a carry makes it</th>
<th>block on its left</th><th>block on its right</th><th>steps (+8 per word crossed)</th></tr></thead><tbody>
<tr><td><code>1010</code></td><td>0</td><td><code>0</code></td><td>+1</td><td>+1</td><td>19</td></tr>
<tr><td><code>0</code></td><td>1</td><td><code>1110</code></td><td>&minus;2</td><td>+2</td><td>31</td></tr>
<tr><td><code>1110</code></td><td>2</td><td><code>1</code></td><td>0</td><td>+2</td><td>19</td></tr>
<tr><td><code>1</code></td><td>3</td><td><code>1010</code>, and the carry goes on left</td><td>&minus;2</td><td>+1</td><td>4</td></tr>
</tbody></table></div>'''

SEC1 = [
    '<p>Look at the tape each time the head arrives back at the right end. It is always '
    '<code>L a<sup>n<sub>1</sub></sup> w<sub>1</sub> a<sup>n<sub>2</sub></sup> w<sub>2</sub> &hellip; w<sub>k</sub> '
    'a<sup>n<sub>k+1</sub></sup> 1 D&gt;1 0</code>: blocks of the word <code>a = 100</code> separated by <em>walls</em>, '
    'and every wall has one of four shapes. The shapes are the digits of a base-4 counter. One <em>trip</em> of the head '
    '(from the right end and back) adds 1 to that counter: the head runs left over every wall showing digit 3, turning '
    'it into digit 0 (a carry), changes the first wall that is not a 3 to its next shape, and comes back. The last wall '
    'is the least significant digit.</p>',
    RULES,
    '<p>Each change moves words between the two blocks beside the wall. Over a full cycle of four changes a wall takes 3 '
    'words from the block on its left and adds 6 to the block on its right. The left end <code>10</code> is one more '
    'digit, a binary one: a carry turns it into <code>00</code>, and the next carry makes the head run to the left end '
    '(the visit of the left end) and back, after which every wall shows 0 again. So one period from one visit to the '
    'next is 2&middot;4<sup>k</sup> trips, and over a period the first block loses 4 words, block j loses '
    '12&middot;4<sup>j&minus;2</sup> and the last block gains 12&middot;4<sup>k&minus;1</sup>: the countdown seen in the '
    'table above, now derived.</p>',
    '<p>When a block between two walls runs out, the two walls become one wall <code>(1010)<sup>r</sup></code> made of '
    'r walls with nothing between them. That wall is again a base-4 digit (its four shapes change only at its two ends) '
    'with the same totals &minus;3 and +6, so the blocks to its right move one level down and drain four times slower. '
    'After every second visit of the left end the right end grows a new wall <code>1010</code> with a block of 5 words. '
    'All of these rules are proved in Lean for every block length (and every r), in <code>lean/Odometer.lean</code>.</p>',
    '<p><b>Try it.</b> The panel below runs the counter itself, from the real tape at step 2,973,727, one trip at a '
    'time, with the step count of each trip (19, 31, 19 or 4 for each wall that changes, plus 8 steps for each word '
    'of every block the head crosses). Running it to the left end gives step 3,477,317 and the tape '
    '<code>00 a<sup>45</sup> 1 a<sup>186</sup> 1 a<sup>685</sup> 1 a<sup>407</sup> 110</code>, which is exactly what the '
    'plain simulation of the machine shows at that step.</p>',
    '''<div class="panel"><div class="controls"><button id="odTrip" type="button">1 trip</button><button id="od16" type="button">16 trips</button><button id="odLeft" class="primary" type="button">To the left end</button><button id="odReset" type="button">Reset</button></div>
<div class="readout" style="margin-top:10px"><span>step <b id="odStep"></b></span><span>trips <b id="odTrips"></b></span><span>counter <b id="odCtr" style="font-family:var(--mono)"></b></span></div>
<div id="odTape" style="margin-top:10px"></div><div class="cap" id="odCap"></div></div>
<script>
(function(){
  var DL=[1,-2,0,-2], DR=[1,2,2,1], KA=[19,31,19,4], SH=['1010','0','1110','1'];
  var S;
  function reset(){ S={pre:'10', b:[48,197,733,217], d:[0,0,1], step:2973727, trips:0, done:false, last:''}; draw(); }
  function trip(){
    if (S.done) return false;
    var k=S.d.length, j=k-1, b0=S.b.slice(), cost=8*b0[k], ch=[];
    while (j>=0 && S.d[j]===3) j--;
    if (j<0 && S.pre==='00'){ S.done=true; S.last='the next carry reaches the left end 00: the head visits the left end'; return false; }
    for (var t=k-1; t>j; t--){ S.b[t]+=DL[3]; S.b[t+1]+=DR[3]; S.d[t]=0; cost+=KA[3]+8*b0[t]; ch.push('w'+(t+1)+' 1&rarr;1010'); }
    if (j>=0){ var x=S.d[j]; S.b[j]+=DL[x]; S.b[j+1]+=DR[x]; cost+=KA[x]; S.d[j]=x+1; ch.push('w'+(j+1)+' '+SH[x]+'&rarr;'+SH[x+1]); }
    else { S.b[0]+=1; S.pre='00'; cost+=19; ch.push('left end 10&rarr;00'); }
    S.step+=cost; S.trips++; S.last='last trip: '+ch.join(', ')+'; '+cost.toLocaleString('en-US')+' steps';
    return true;
  }
  function draw(){
    var mx=Math.max.apply(null,S.b), h=['<div style="display:flex;align-items:flex-end;gap:3px;flex-wrap:wrap;font:12px var(--mono)">'];
    function chip(t,c){ return '<span style="padding:2px 5px;border-radius:5px;background:'+c+';color:var(--fg)">'+t+'</span>'; }
    h.push(chip(S.pre,'var(--sunk)'));
    for (var i=0;i<S.b.length;i++){
      var w=Math.max(18,Math.round(260*S.b[i]/mx));
      h.push('<span style="display:inline-flex;flex-direction:column;align-items:center"><span style="color:var(--muted)">a<sup>'+S.b[i]+'</sup></span><span style="display:block;width:'+w+'px;height:12px;background:var(--accent);border-radius:3px"></span></span>');
      if (i<S.d.length) h.push(chip(SH[S.d[i]]+' <b>'+S.d[i]+'</b>', ['var(--kernel-bg)','var(--native-bg)','var(--computed-bg)','var(--open-bg)'][S.d[i]]));
    }
    h.push(chip('110','var(--sunk)')); h.push('</div>');
    document.getElementById('odTape').innerHTML=h.join('');
    document.getElementById('odStep').textContent=S.step.toLocaleString('en-US');
    document.getElementById('odTrips').textContent=S.trips;
    document.getElementById('odCtr').textContent=(S.pre==='00'?'1':'0')+' '+S.d.join('');
    document.getElementById('odCap').innerHTML=S.last+(S.done?' (step '+S.step.toLocaleString('en-US')+', as in the direct simulation)':'');
  }
  document.getElementById('odTrip').onclick=function(){ trip(); draw(); };
  document.getElementById('od16').onclick=function(){ for (var i=0;i<16;i++) if(!trip()) break; draw(); };
  document.getElementById('odLeft').onclick=function(){ while(trip()){} draw(); };
  document.getElementById('odReset').onclick=reset;
  reset();
})();
</script>''']

SEC2 = [
    f'<p>Because these rules apply many trips at once in closed form (all walls are digits; a jump stops only where a '
    f'block gets short, a wall has a shape whose rule is not yet known, or the left end overflows), the run can be '
    f'followed exactly far beyond any simulation: the macro in <code>py/odometer/</code> reached step '
    f'10<sup>{D}</sup> ({summ["digits"]} digits, given exactly in <code>data/odometer/summary.json</code>) after '
    f'{summ["visits"]:,} visits of the left end, with {summ["walls"]} walls on the tape, and no halt. Every trip that is '
    f'not a plain digit change (a visit of the left end, a new wall, a block running out, walls merging) is run cell '
    f'by cell on a copy of the tape whose long blocks are cut down to the same length modulo 12, and its step count is '
    f'corrected by the measured 8 or 19 steps per word. The macro agrees with the plain simulation at every visit of the '
    f'left end up to 5&middot;10<sup>10</sup> steps, step count included.</p>',
    '<p><b>The run-outs of the first block.</b> The first block counts down by 4 per visit. When it runs out, it and the '
    'walls next to it fold into the left end, which shrinks back to <code>10</code> over a few visits, and the next '
    'block becomes the first one, counting down by 4 again. The slider shows the tape at visits of the left end (the '
    'first 60 blocks, bar length on a logarithmic scale; the thin dark lines are the walls, taller for a wall made of more merged walls). '
    + ('Past the start-up, the first block ran out at visits ' + ', '.join(f'{v:,} (step about 10<sup>{d - 1}</sup>)' for v, d in RUNS if d > 8)
       + '.' if RUNS else '') + f' Each run-out so far folded the same way, and the run went on without a halt. At the end of the run the first block has {summ["first_block"]:,} words left, so the next run-out comes about {summ["first_block"]//4:,} visits later.</p>',
    '''<div class="panel"><div class="controls"><button id="lvPrev" type="button">&larr;</button><input id="lvSlider" type="range" min="0" max="1" value="0" step="1" style="flex:1;min-width:160px" aria-label="visit of the left end"><button id="lvNext" type="button">&rarr;</button><button id="lvPlay" class="primary" type="button">Play</button></div><div class="cap" id="lvCap"></div><div id="lvBars" style="margin-top:8px;display:flex;align-items:flex-end;gap:1px;height:160px;overflow:hidden"></div></div>
<script type="application/json" id="lvData">''' + json.dumps(samp, separators=(',', ':')) + '''</script>
<script>
(function(){
  var D=JSON.parse(document.getElementById('lvData').textContent), V=D.visits;
  var sl=document.getElementById('lvSlider'), box=document.getElementById('lvBars'), cap=document.getElementById('lvCap'), timer=null;
  sl.max=V.length-1;
  function lg(x){ return typeof x==='number' ? Math.log10(Math.max(1,x)) : +x.slice(1)+0.5; }
  function txt(x){ return typeof x==='number' ? x.toLocaleString('en-US') : 'a '+(+x.slice(1)+1)+'-digit number'; }
  function draw(){
    var v=V[+sl.value], b=v[6], w=v[7], h=[];
    var mx=1; b.forEach(function(x){ mx=Math.max(mx,lg(x)); });
    for (var i=0;i<b.length;i++){
      var hh=Math.max(2,Math.round(150*lg(b[i])/mx));
      h.push('<span title="block '+(i+1)+': '+txt(b[i])+'" style="flex:1 1 0;min-width:2px;height:'+hh+'px;background:'+(i===0?'var(--head)':'var(--accent)')+'"></span>');
      if (i<w.length && w[i]>0) h.push('<span title="wall of '+w[i]+' merged wall'+(w[i]>1?'s':'')+'" style="flex:0 0 2px;height:'+Math.min(150,6+10*w[i])+'px;background:var(--fg2)"></span>');
    }
    box.innerHTML=h.join('');
    cap.innerHTML='visit '+v[0].toLocaleString('en-US')+' of '+D.total.toLocaleString('en-US')+' · step '+v[1][0]+'.'+v[1].slice(1,3)+'·10<sup>'+(v[2]-1)+'</sup> · '+v[4]+' walls · first block '+txt(b[0]||0)+(v[5].length>2?' · left end still folding: '+v[5].length+' cells':'');
  }
  sl.addEventListener('input',draw);
  document.getElementById('lvPrev').onclick=function(){ sl.value=Math.max(0,+sl.value-1); draw(); };
  document.getElementById('lvNext').onclick=function(){ sl.value=Math.min(V.length-1,+sl.value+1); draw(); };
  document.getElementById('lvPlay').onclick=function(){
    if (timer){ clearInterval(timer); timer=null; this.textContent='Play'; return; }
    this.textContent='Pause'; var me=this;
    timer=setInterval(function(){ if(+sl.value>=V.length-1){ clearInterval(timer); timer=null; me.textContent='Play'; return; } sl.value=+sl.value+1; draw(); },250);
  };
  draw();
})();
</script>''',
    '<p><b>Halting.</b> The machine halts only when A reads 0 followed by 1 or D reads 1 followed by 1. No digit '
    'change, carry, visit of the left end or new wall does that, and every wall shape met so far, '
    '<code>(1010)<sup>r</sup></code> for r up to 13 and their four phases, is a digit whose rule is known. A halt would '
    'need a new local shape: for instance a block running out in a way not seen yet, or two short blocks next to each '
    'other. Whether that can ever happen is the remaining question; it is now a question about the list of block '
    'lengths and the order in which they run out, not about the machine.</p>']

secs = [s for s in spec['explainer']['sections'] if s['id'] not in ('odometer', 'longrun')]
i = [s['id'] for s in secs].index('blocks') + 1
secs[i:i] = [{'id': 'odometer', 'eyebrow': 'How it works', 'heading': 'A base-4 odometer of walls', 'html': SEC1},
             {'id': 'longrun', 'eyebrow': 'Far out', 'heading': 'The countdown, followed exactly far out', 'html': SEC2}]
spec['explainer']['sections'] = secs
spec['explainer']['lede'] = ('Nobody knows. Started on a blank tape, this machine builds blocks of the word 100 separated by '
    'walls, and the walls are the digits of a base-4 odometer that the head counts up one trip at a time; the blocks '
    'drain at rates 4, 12, 48, &hellip; per visit of the left end. This page runs the real machine, the odometer, and '
    f'the exact countdown to 10<sup>{D}</sup> steps.')
spec['explainer']['facts'] = [
    {'level': 'trusted', 'value': f'10<sup>{D}</sup> steps', 'text': 'No halt (exact odometer macro).'},
    {'level': 'kernel', 'value': '24 rules', 'text': 'The digit changes of the odometer, in Lean for every block length.'},
    {'level': 'trusted', 'value': '&times;4', 'text': "The blocks' drain rates, level by level, now derived."}]
spec['summary'] = ('A base-4 odometer: the walls between blocks of 100 are digits (1010, 0, 1110, 1), a trip of the head '
    'adds one; per visit of the left end block j loses 12·4^(j−2) words; merged walls are digits too. Exact macro run '
    f'to 10^{D} steps, no halt; digit rules in Lean.')
spec['asof'] = 'Status as of 24 November 2026.'
spec['verdict'] = [('<b>The question is open.</b> The run is decoded as a base-4 odometer of walls (rules proved in Lean '
    f'for every block length) and followed exactly to 10<sup>{D}</sup> steps with no halt; what is left is whether the '
    'order in which blocks run out can ever produce a wall shape that halts.')]
cl = [c for c in spec['claims'] if not c.get('odometer')]
new = [
    {'odometer': True, 'level': 'kernel', 'title': 'The odometer rules, for every block length',
     'text': 'The four digit changes of a last wall (1010 &rarr; 0 &rarr; 1110 &rarr; 1), a carry through a wall 1 or a '
             'double wall into each digit, the four phases of a wall (1010)<sup>r+2</sup> of r+2 merged walls for every r, '
             'the left end 10 &rarr; 00, and the new wall at the right end after an arrival in C: each a theorem '
             '<code>steps n c = some c\'</code> for all block lengths and any tape to the left, with the exact step count '
             '(8 per word crossed plus a constant).',
     'where': '<code>lean/Odometer.lean</code> (generated by <code>py/odometer_lean.py</code> with <code>tools/py/bbtools/symtm.py</code>)'},
    {'odometer': True, 'level': 'trusted', 'title': f'No halt in the first 10<sup>{D}</sup> steps (odometer macro)',
     'text': f'The exact macro of <code>py/odometer/</code> (closed-form jumps over many trips when every wall is a known '
             f'digit, otherwise one trip run cell by cell on a copy of the tape with long blocks cut down modulo 12, '
             f'step count corrected per word) ran from blank tape to step {summ["step"][:6]}&hellip; '
             f'({summ["digits"]} digits) through {summ["visits"]:,} visits of the left end without a halt. Checked '
             f'against the direct simulator <code>c/rtrips.c</code>: all trips of the cut-down runner to 3&middot;10<sup>9</sup> '
             f'steps, and the macro at every visit of the left end to 5&middot;10<sup>10</sup> steps, step counts included. '
             f'This is a bounded run.',
     'where': '<code>python3 py/odometer/far.py SECONDS</code>, <code>python3 py/odometer/validate.py 5e10</code>; '
              '<code>data/odometer/summary.json</code>'},
    {'odometer': True, 'level': 'heuristic', 'title': 'The countdown, derived',
     'text': 'If no block runs out during a period, a period is 2&middot;4<sup>k</sup> trips and the blocks change by '
             '&minus;4, &minus;12, &minus;48, &hellip;, &minus;12&middot;4<sup>k&minus;2</sup>, +12&middot;4<sup>k&minus;1</sup> '
             '(from the digit totals &minus;3, +6 per cycle). A wall of r merged walls is again a digit with the same totals.',
     'where': 'README, <code>py/odometer/macro.py</code> (<code>learn</code>)'}]
j = next(i for i, c in enumerate(cl) if c['level'] == 'open')
cl[j:j] = new
for c in cl:
    if c['level'] == 'open':
        c['text'] = ('Not known. It halts exactly at A&gt;0 1 or D&gt;1 1; no rule of the odometer does that, so a halt '
                     'needs a wall shape or a run-out not met yet.')
spec['claims'] = cl
json.dump(spec, open(SP, 'w'), indent=1, ensure_ascii=False)
print('status.json updated')
