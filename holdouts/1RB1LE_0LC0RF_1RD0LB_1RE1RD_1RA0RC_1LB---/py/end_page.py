"""Write the "end" section of the explainer (status.json, explainer.sections): the right-end layer, with the right end
of the tape at 200 consecutive round trips of the real run embedded, and a one-round-trip calculator for end forms.

usage (from the repository root):  python3 holdouts/1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---/py/end_page.py
then rebuild the pages:  python3 holdouts/build_pages.py 1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---
Needs a C compiler (py/endlayer.py builds c/endtails.c).
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import endlayer as E  # noqa: E402

MACHINE = E.MACHINES[0]
STEPS = 200_000_000
ROWS = 200
WIDTH = 160


def cls(tok):
    m, s = tok
    if s == E.END:
        return 'z'
    if s == 0:
        return 't'
    if s == 2:
        return 'g'
    if s != 3:
        return 'x'
    return 'o' if m % 2 else 'e'


def front_rule(tail):
    t = list(tail)
    if not t:
        return 'none'
    a = t[0]
    if a[1] == E.END:
        return 'end'
    if a[1] == 3 and a[0] % 2 == 0:
        return 'halt' if len(t) > 1 and t[1] == (1, 0) else 'even'
    if a == (3, 0):
        return 'touch'
    if a == (3, 2):
        return 'gap'
    if a[1] == 3 and len(t) > 1:
        b = t[1]
        if b[1] == E.END:
            return 'end'
        if b == (3, 2):
            return 'gap2'
        if b == (3, 0):
            return 'touch2'
    return 'other'


def rows():
    M = E.Model(MACHINE)
    a, b = E.SLOTS[MACHINE]
    out = []
    for k, st, cells in [r for r in E.endtails(MACHINE, STEPS) if len(r) == 3][-ROWS - 1:-1]:
        t = E.toks(cells)
        i = 0 if st == a else 1
        if i == 1 and not E.regular(t[0]):
            i = 0
        _, i = E.bulk_image(t, i)
        tail = t[i:]
        # cell classes, right-aligned
        s = ''
        for j, tok in enumerate(t):
            c = cls(tok)
            m, sep = tok
            g = '1' + '01' * (m - 1)
            s += ''.join(c if ch == '1' else '.' for ch in g) + ('.' * sep if sep > 0 else '')
            if j == i - 1:
                cut = len(s)
        tail_cells = len(s) - cut if i > 0 else len(s)
        s = s[-WIDTH:]
        out.append([int(k), s, tail_cells, E.fmt(tail), E.fmt(M.G(tail)), front_rule(tail)])
    return out


HTML = r"""
<p>The running XOR of the previous section holds for every pair of groups away from the ends. At the right end it meets a thin layer that is not made of such pairs. Write the tape there as a list of <em>tokens</em>: <code>m</code> is a group of m single 1s followed by <code>000</code>, <code>m_2</code> a group followed by only <code>00</code>, <code>m_0</code> a group that touches the next one (<code>... 1 1 ...</code>), and <code>m$</code> the last group of the tape. In the bulk every m is odd and every gap is <code>000</code>, and a pair (a, b) becomes a&minus;1 over 2 single groups <code>1</code>, then the group b+2. The <b>tail</b> is what follows the last such pair.</p>
<p><b>The tail evolves on its own.</b> One round trip turns the tail into a new token list that depends only on the tail: the pairs on its left are swept as usual and never looked at. The only thing the rest of the tape decides is whether the first token of the new list is the first or the second member of a pair at the next round trip, which is the parity of the running XOR at that place. So the right end is a machine of its own, fed one bit per round trip by the bulk. Checked on the runs of all six machines with these tapes, 10<sup>10</sup> steps each (about 29,000 round trips each, some 400 different tails), with no exception, and the six machines give the same image of every tail tried (<code>py/endlayer.py</code>).</p>
<div class="panel">
<canvas id="end-cv" width="640" height="400" style="width:100%;image-rendering:pixelated;cursor:crosshair"></canvas>
<p class="cap">The last 160 cells of the tape at 200 consecutive round trips of the real run, near step 2&middot;10<sup>8</sup>, one row per round trip, time downwards, the right end on the right. Grey: groups of the bulk pairs and odd groups; orange: even groups; red: a group touching the next one; blue: a group followed by only <code>00</code>; green: the last group; the dark tick marks where the tail starts. Click a row.</p>
<pre id="end-info" class="small" style="white-space:pre-wrap;margin:8px 0 0">&nbsp;</pre>
</div>
<p>The rules at the front of the tail. Each is checked on thousands of tails (<code>py/endlayer.py rules</code>); the sweep step behind each is proved in Lean for every size of group (<code>lean/EndRules.lean</code>, table below):</p>
<ul>
<li><b>Even group in the first slot</b> (<code>2j b ...</code>): the rightward sweep turns back at it (<code>even_E</code>). It becomes j single groups <code>1</code>, then <code>3_0 b&minus;1</code>, and everything after it is left as it was: the tape right of it skips this round trip. An even group in the second slot is simply the b of a pair and grows by 2 (<code>even_A</code>): even groups are counters that grow while they sit in second slots and are paid out as single 1s when the parity puts them in a first slot.</li>
<li><b>Touching group</b> (<code>3_0 c ...</code>, c &ge; 2): the sweep turns back (<code>touch_E</code>); it becomes <code>1 1 c&minus;1</code> and the rest is left as it was.</li>
<li><b>Short gap</b> (<code>3_2 ...</code>): the sweep goes on one cell off the grid (<code>gap2_E</code>) and leaves a block <code>11</code>; on the way back the leftward sweep turns right again at that block (<code>even_block_B</code>), so the tape right of it gets a second round trip in the same visit.</li>
<li><b>The end</b>: <code>2$</code> becomes <code>1 2$</code>, <code>1$</code> becomes <code>2 2$</code>, <code>3_0 1$</code> becomes <code>1 1$</code>; a pair (a, <code>2$</code>) becomes the pair's image followed by a new <code>2$</code>.</li>
</ul>
__TABLE__
<p><b>What a halt needs.</b> The machine halts exactly when an even group in a first slot is followed by a single 1 that touches the next group: <code>2j 1_0</code> (<code>halt_even_touch</code>, every j). Among all 1,205 tails of at most three tokens with groups up to 5, these are the only ones that halt. Following the tail from <code>2$</code> with both parities allowed at every round trip, so for any bulk at all, 100,000 different tails (groups up to 60) are reached and none of them halts. Proving that no reachable tail ever contains <code>2j 1_0</code> in a first slot, for every parity sequence, would show that the right end never halts.</p>
<div class="panel">
<div class="controls"><label class="small" for="end-in">A tail (tokens as above):</label><input id="end-in" value="4 1 2$" style="flex:1;min-width:12em;font-family:var(--mono)"><button id="end-go" class="primary">One round trip</button><button id="end-y0">Next: first slot</button><button id="end-y1">Next: second slot</button></div>
<pre id="end-out" class="small" style="white-space:pre-wrap;margin:10px 0 0"></pre>
<p class="cap">Runs the machine itself on 16 bulk pairs followed by the tail, the head arriving in E, until it is back on the bulk, and reads the tokens it left. The two other buttons split the result for the next round trip as the bulk would, with the first token in a first or in a second slot. Try <code>4 1_0 2$</code>.</p>
</div>
<script>
(function(){
var R=__ROWS__,W=__W__;
var cv=document.getElementById('end-cv'),cx=cv.getContext('2d'),S=4,H=2;
var COL={o:[110,110,120],e:[230,140,20],t:[210,40,40],g:[40,110,210],z:[40,150,70],x:[150,60,160]};
function draw(sel){cv.width=W*S;cv.height=R.length*H;cx.fillStyle='#fff';cx.fillRect(0,0,cv.width,cv.height);
  for(var t=0;t<R.length;t++){var s=R[t][1],off=W-s.length;
    for(var i=0;i<s.length;i++){var c=COL[s[i]];if(!c)continue;cx.fillStyle='rgb('+c+')';cx.fillRect((off+i)*S,t*H,S,H);}
    var tc=W-R[t][2];cx.fillStyle='#111';cx.fillRect(tc*S-1,t*H,2,H);
    if(t===sel){cx.strokeStyle='#000';cx.strokeRect(0.5,t*H-0.5,W*S-1,H+1);}}}
var NAMES={pair:'a pair',even:'even group in a first slot: the sweep turns back, the rest skips this round trip',touch:'touching group: the sweep turns back',gap:'short gap: the rest gets a second round trip',gap2:'short gap in a second slot',touch2:'touching group in a second slot',end:'the end of the tape',other:'other',none:'(empty)',halt:'HALT pattern'};
function show(t){var r=R[t];document.getElementById('end-info').textContent='step '+r[0].toLocaleString()+'\ntail   '+r[3]+'\nimage  '+r[4]+'\nfront of the tail: '+(NAMES[r[5]]||r[5]);draw(t);}
cv.onclick=function(e){var b=cv.getBoundingClientRect(),t=Math.floor((e.clientY-b.top)/b.height*R.length);if(t>=0&&t<R.length)show(t);};
// one round trip of 1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB--- on 16 bulk pairs and a tail
var TB='1RB1LE_0LC0RF_1RD0LB_1RE1RD_1RA0RC_1LB---'.split('_').map(function(p){return [p.slice(0,3),p.slice(3,6)].map(function(x){return x[2]=='-'?null:[+x[0],x[1]=='R'?1:-1,x.charCodeAt(2)-65];});});
function parse(txt){var out=[];txt.trim().split(/\s+/).forEach(function(x){if(!x)return;var m,s;if(/\$$/.test(x)){m=+x.slice(0,-1);s=-1;}else if(x.indexOf('_')>=0){var p=x.split('_');m=+p[0];s=+p[1];}else{m=+x;s=3;}if(!(m>=1&&m%1===0&&(s===-1||s>=0)))throw 'bad token '+x;out.push([m,s]);});if(!out.length)throw 'empty';out[out.length-1][1]=-1;return out;}
function cells(tl){var s='';tl.forEach(function(t){s+='1';for(var i=1;i<t[0];i++)s+='01';if(t[1]>0)s+='0'.repeat(t[1]);});return s;}
function fmt(tl){return tl.map(function(t){return t[1]==3?''+t[0]:(t[1]<0?t[0]+'$':t[0]+'_'+t[1]);}).join(' ');}
function toks(s){s=s.replace(/0+$/,'');if(!s.length)return [];if(s[0]!='1')return null;var out=[],re=/(1(?:01)*)(0*)/g,m;while((m=re.exec(s))&&m[0].length){out.push([(m[1].length+1)/2,m[2].length]);}if(cells(out)!==s)return null;out[out.length-1][1]=-1;return out;}
function trip(tl){var pre=[];for(var i=0;i<32;i++)pre.push([1,3]);var pc=cells(pre),c=pc+cells(tl),n=c.length+4000,tape=new Uint8Array(n),base=20;
  for(var i=0;i<c.length;i++)tape[base+i]=+c[i];var p=base,st=4,off=base+pc.length,went=false;
  for(var k=0;k<1000000;k++){var tr=TB[st][tape[p]];if(!tr)return {halt:k+1};tape[p]=tr[0];p+=tr[1];st=tr[2];if(p>off)went=true;if(went&&p<base+40)break;if(p>=n-5)return {err:'the head ran away'};}
  var s='';for(var i=off-1;i<n;i++)s+=tape[i];var t=toks(s);return t?{out:t}:{err:'not a list of groups: '+s.replace(/0+$/,'').slice(0,60)};}
function reg(t){return t[1]==3&&t[0]%2==1;}
function split(U,y){U=U.slice();var i=0;if(y==1){if(U.length>1&&reg(U[0]))i=1;else U.unshift([1,3]);}while(i+1<U.length&&reg(U[i])&&reg(U[i+1]))i+=2;return U.slice(i);}
var last=null;
function go(){var o=document.getElementById('end-out');try{var tl=parse(document.getElementById('end-in').value);var r=trip(tl);
  if(r.halt){o.textContent='tail   '+fmt(tl)+'\nHALTS, '+r.halt+' steps after the head reaches the bulk pairs';last=null;return;}
  if(r.err){o.textContent=r.err;last=null;return;}last=r.out;o.textContent='tail   '+fmt(tl)+'\nimage  '+fmt(r.out);}catch(e){o.textContent=''+e;last=null;}}
function nxt(y){if(!last)return;var t=split(last,y);document.getElementById('end-in').value=fmt(t);go();}
document.getElementById('end-go').onclick=go;
document.getElementById('end-y0').onclick=function(){nxt(0);};
document.getElementById('end-y1').onclick=function(){nxt(1);};
draw(-1);show(R.length-1);go();
})();
</script>
"""


def rule_table():
    import html
    import endrules
    rows = []
    for name, start, text in endrules.RULES:
        end = endrules.run_to_edge(endrules.MACHINE, start)
        rows.append(f'<tr><td><code>{name}</code></td><td><code>{html.escape(start)}</code></td>'
                    f'<td><code>{html.escape(str(end))}</code></td><td>{html.escape(text).replace("`", "")}</td></tr>')
    return ('<div style="overflow-x:auto"><table class="tbl"><thead><tr><th>rule</th><th>from</th><th>to</th><th>what it says'
            '</th></tr></thead><tbody>' + ''.join(rows) + '</tbody></table></div>')


def main():
    path = os.path.join(HERE, '..', 'status.json')
    d = json.load(open(path))
    html = HTML.replace('__ROWS__', json.dumps(rows(), separators=(',', ':'))).replace('__W__', str(WIDTH)).replace('__TABLE__', rule_table()).strip()
    sec = {'id': 'end', 'eyebrow': 'The right end', 'heading': 'The right-end layer runs on its own', 'html': html}
    ss = [s for s in d['explainer']['sections'] if s['id'] != 'end']
    i = next(i for i, s in enumerate(ss) if s['id'] == 'ca') + 1
    ss.insert(i, sec)
    d['explainer']['sections'] = ss
    with open(path, 'w') as f:
        json.dump(d, f, indent=1, ensure_ascii=False)
        f.write('\n')


if __name__ == '__main__':
    main()
