"""Write the "ca" section of the explainer (status.json, explainer.sections): the round trip as an XOR rule, with
the letter words of 120 consecutive round trips of the real run embedded for the interactive check.

usage (from the repository root):  python3 holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/py/ca_page.py
then rebuild the pages:  python3 tools/pages/build_explainer.py holdouts/M/status.json pages/holdouts/M/explainer.html
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ca_check  # noqa: E402

MACHINE = '1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---'
STEPS = 12_000_000
ROWS = 120


def rows():
    rs = []
    for k, w in ca_check.snapshots(MACHINE, STEPS):
        z, first = ca_check.letters(w)
        rs.append((k, first, z, len(w)))
    rs = rs[-ROWS:]
    base = min(r[1] for r in rs)
    out = []
    for k, first, z, n in rs:
        assert (first - base) % 4 == 0
        bits = ''.join(map(str, z))
        bits += '0' * (-len(bits) % 4)
        out.append([k, (first - base) // 4, len(z), (n - base) // 4, '%x' % int('1' + bits, 2)])
    return out


HTML = r"""
<p>Cut the tape into letters of 4 cells, counted from the left end. Just after a rightward sweep every letter is one of two: <b>s</b> = <code>0111</code> (a block of ones starts here) or <b>c</b> = <code>1111</code> (the block goes on). A block of 4k+3 ones, with the 0 in front of it, is the word s c<sup>k</sup>, so the list of numbers is a word of s and c letters. In these letters a round trip has a short exact description, proved in Lean for every word:</p>
<ul>
<li><b>Leftward sweep.</b> Each block s c<sup>k</sup> becomes the group <code>1 (01)<sup>2k</sup> 000</code> of 2k+1 single 1s, shifted one cell to the right (<code>block_B</code>, <code>left_sweep</code>).</li>
<li><b>Rightward sweep.</b> The head reads the groups in state E and A in turn, E, A, E, A, ..., with no exception. A group read in E is written back as s<sup>k+1</sup>. A group read in A is written back as c<sup>k+1</sup>, and the head also turns the s just behind it into c (<code>group_E</code>, <code>group_A</code>, <code>right_sweep</code>).</li>
</ul>
<p>Put together, the letter the rightward sweep writes at each place is the parity of the number of block starts it has read so far: <b>the new word is the running XOR of the old one</b> (<code>outL_eq_pxor</code>). Read the other way, each letter before a round trip is the XOR of the same letter after the round trip and its left neighbour. Backwards in time the list evolves by the XOR cellular automaton (elementary rule 102, the rule that draws Pascal's triangle mod 2), and forwards by its inverse. In the list of numbers: the numbers are read in pairs (a, b), and each pair becomes a zeros followed by the number b + 1.</p>
<div class="panel">
<div class="controls"><button id="ca-plain" class="primary">Letters</button><button id="ca-check">Check each row against the next</button><span class="small" id="ca-read"></span></div>
<canvas id="ca-cv" width="1000" height="360" style="width:100%;image-rendering:pixelated;margin-top:10px"></canvas>
<p class="cap">120 consecutive round trips of the real run, steps 9.3&middot;10<sup>6</sup> to 1.2&middot;10<sup>7</sup>, one row per round trip, time downwards, one pixel per letter, the left end of the tape on the left. Letters: dark is s, light is c, grey is the layer at the right end that is not yet in letters. Check: each letter of a row is recomputed from the row below it as the XOR of the letter below and its left neighbour; green where that gives the letter of the run, red where it does not.</p>
</div>
<div class="panel">
<div class="controls"><label class="small" for="ca-in">A list of numbers k (the first read in E):</label><input id="ca-in" value="1 0 3 1 2 2 6 1 1 0" style="flex:1;min-width:12em;font-family:var(--mono)"><button id="ca-go" class="primary">One round trip</button></div>
<pre id="ca-out" class="small" style="white-space:pre-wrap;margin:10px 0 0"></pre>
<p class="cap">The rule on the list: pairs (a, b) become a zeros and then b + 1. Away from the two ends of the tape this is exactly what the machine does to its list of blocks. The default list is a stretch of the real tape after about a million steps; one round trip of the run turned it into 0 1 0 0 0 2 0 0 3 0 0 0 0 0 0 2 0 1, as the rule says.</p>
</div>
<p>What follows from it:</p>
<ul>
<li><b>Information only moves right.</b> A letter after a round trip depends only on the letters at its left. Nothing at the right end can change the bulk of the list.</li>
<li><b>The left end.</b> The tape grows by exactly one cell at the left end each round trip and the letter grid moves with it, so the left end is a fixed boundary for the rule. The running XOR repeats itself on the first 2<sup>j</sup> letters after 2<sup>j+1</sup> round trips: this is the short cycle of the first numbers of the list.</li>
<li><b>The right end.</b> A layer of the last few groups (13 cells on average, at most about 100 in the first 10<sup>9</sup> steps) is not yet in letter form; there the rightward sweep sometimes turns back early, and new letters join the word. This layer is not decoded.</li>
<li><b>Where a halt could come from.</b> The sweep rules above take a fixed number of steps for every word, so no halt happens in the bulk: a halt (B on two adjacent 1s) can only come from the two ends of the tape, and the left end has been periodic in every run so far. The halting question is now a question about the layer at the right end, fed by the running XOR arriving from the left.</li>
</ul>
<p>Checked on the run (<code>py/ca_check.py</code>): every letter that two consecutive round trips have in common, up to the right-end layer, obeys the rule, for this machine and the five other machines with the same tapes, to 2&middot;10<sup>8</sup> steps each (for this machine 4,159 round trips and 8,492,322 letters, no exception).</p>
<script>
(function(){
var R=__ROWS__;
var cv=document.getElementById('ca-cv'),cx=cv.getContext('2d'),mode='plain';
var W=0;R.forEach(function(r){W=Math.max(W,r[3]);});
function bits(r){var h=r[4],b=[];for(var i=1;i<h.length;i++){var v=parseInt(h[i],16);b.push(v>>3&1,v>>2&1,v>>1&1,v&1);}
  // the leading hex digit carries a marker 1 bit
  var v0=parseInt(h[0],16),lead=[];for(var j=3;j>=0;j--)lead.push(v0>>j&1);
  var all=lead.concat(b);var k=all.indexOf(1);all=all.slice(k+1);return all.slice(0,r[2]);}
var Z=R.map(bits);
function draw(){
  cv.width=W;cv.height=R.length*3;var id=cx.createImageData(W,R.length*3),d=id.data;
  var cs=mode=='plain';
  var ok=0,bad=0;
  for(var t=0;t<R.length;t++){var r=R[t],z=Z[t],o=r[1],nx=t+1<R.length?Z[t+1]:null,no=nx?R[t+1][1]:0;
    for(var x=0;x<W;x++){var n=x-o,c;
      if(x<o||x>=r[3]) c=null; else if(n>=z.length) c=[150,150,150];
      else if(cs||!nx) c=z[n]?[40,45,60]:[225,225,215];
      else {var m=x-no; if(m>=1&&m<nx.length){var p=nx[m]^nx[m-1]; if(p==z[n]){ok++;c=z[n]?[30,120,70]:[170,215,180];}else{bad++;c=[210,40,40];}} else c=z[n]?[40,45,60]:[225,225,215];}
      if(!c)continue;for(var yy=0;yy<3;yy++){var i=((t*3+yy)*W+x)*4;d[i]=c[0];d[i+1]=c[1];d[i+2]=c[2];d[i+3]=255;}}}
  cx.putImageData(id,0,0);
  document.getElementById('ca-read').textContent=cs?'':(ok.toLocaleString()+' letters checked, '+bad+' wrong');
}
var bc=document.getElementById('ca-check'),bp=document.getElementById('ca-plain');
bc.onclick=function(){mode='check';bc.className='primary';bp.className='';draw();};
bp.onclick=function(){mode='plain';bp.className='primary';bc.className='';draw();};
function step(){var xs=document.getElementById('ca-in').value.trim().split(/[\s,]+/).filter(function(s){return s!=='';}).map(Number),out=[],note='';
  if(xs.some(function(v){return !(v>=0&&v%1===0);})){document.getElementById('ca-out').textContent='Give whole numbers 0, 1, 2, ...';return;}
  for(var i=0;i+1<xs.length;i+=2){for(var j=0;j<xs[i];j++)out.push(0);out.push(xs[i+1]+1);}
  if(xs.length%2) note='\n(the last number has no partner: it belongs to the layer at the right end)';
  var z=[];xs.forEach(function(k){z.push('s');for(var j=0;j<k;j++)z.push('c');});
  var p=0,zo=[];z.forEach(function(l){if(l=='s')p^=1;zo.push(p?'s':'c');});
  document.getElementById('ca-out').textContent='list   '+xs.join(' ')+'\nafter  '+out.join(' ')+note+'\n\nletters  '+z.join('')+'\nrunning XOR  '+zo.join('');
  document.getElementById('ca-in').value=out.join(' ');}
document.getElementById('ca-go').onclick=step;
draw();
})();
</script>
"""


def main():
    path = os.path.join(HERE, '..', 'status.json')
    d = json.load(open(path))
    sec = {'id': 'ca', 'eyebrow': 'The rewrite decoded', 'heading': 'A round trip is a running XOR',
           'html': HTML.replace('__ROWS__', json.dumps(rows(), separators=(',', ':'))).strip()}
    ss = [s for s in d['explainer']['sections'] if s['id'] != 'ca']
    i = next(i for i, s in enumerate(ss) if s['id'] == 'what') + 1
    ss.insert(i, sec)
    d['explainer']['sections'] = ss
    with open(path, 'w') as f:
        json.dump(d, f, indent=1, ensure_ascii=False)
        f.write('\n')


if __name__ == '__main__':
    main()
