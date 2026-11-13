"""Write Visit.lean: the token-level visit laws mined by laws.py, each as a kernel-checked conditional theorem.
usage: gen_visit.py MACHINE NAMESPACE LAWS.json > Visit.lean"""
import sys, json
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from laws_parse import parse
m,ns,lf=sys.argv[1:4]
tr=parse(m); S="ABCDEF"
rows=json.load(open(lf))
B=lambda v:"true" if v else "false"
def cons(cells,tail):
    for c in reversed(cells): tail="cons %s (%s)"%(c,tail) if ' ' in tail else "cons %s %s"%(c,tail)
    return tail
out=[]
out.append(f'''import Machine

/-! # Visit laws of {m}

`Vis q x r x'`: the head enters the stream `x` from the left in state `q` (on its first cell) and the first time it
leaves `x` to the left it is in state `r` and the stream is `x'`; the cell it lands on and everything left of it are
untouched.  Every theorem below is one row of the token-level law (tokens of {{W}} cells, mined from the run by
`py/laws.py`, written by `py/gen_visit.py`): what one visit does to a stream that starts with the token, given what
the nested visits of the rest of the stream do.  The rows are exact for every stream (the hypotheses are about the
rest of the stream only), so they can be composed by induction into laws for whole counters. -/

namespace {ns}

open TM

/-- One visit of the stream `x` in state `q`: back out on the left in state `r`, leaving `x'`. -/
def Vis (q : St) (x : Tape) (r : St) (x' : Tape) : Prop :=
  ∀ (a : Bool) (L : Tape), ∃ t, steps t ⟨cons a L, x, q⟩ = some ⟨L, cons a x', r⟩
''')
names=set()
for q,tok,calls,r,tok2,cnt,first in rows:
    W=len(tok); cells=[int(c) for c in tok]; cl=[(calls[i],calls[i+1].upper()) for i in range(0,len(calls),2)]
    st=S.index(q); pos=0; k=0; segs=[]; j=0; ok=True
    start=(list(cells),st)
    while True:
        if pos==W:
            if j>=len(cl) or S[st]!=cl[j][0]: ok=False; break
            segs.append((start,k,list(cells),st,cl[j][1])); st=S.index(cl[j][1]); pos=W-1; j+=1; k=0; start=(list(cells),st); continue
        if pos==-1:
            ok = (S[st]==r and "".join(map(str,cells))==tok2 and j==len(cl)); break
        key=(st,cells[pos])
        if key not in tr: ok=False; break
        w,d,st=tr[key]; cells[pos]=w; pos+=d; k+=1
    assert ok,(q,tok,calls,r,tok2)
    name=f"v_{q}_{tok}_{calls or 'none'}"
    xs=["x"]+[f"x{i+1}" for i in range(len(cl))]
    hyps=" ".join(f"(h{i+1} : Vis .{cl[i][0]} {xs[i]} .{cl[i][1]} {xs[i+1]})" for i in range(len(cl)))
    L=[]
    L.append(f"/-- `{q}> {tok} x`"+(f", nested visits {' '.join(a+'→'+b for a,b in cl)}" if cl else ", no nested visit")+f": out in state {r}, leaving `{tok2} x'`.  (In the run: {cnt} times in 3·10^7 steps, first at step {first}.) -/")
    L.append(f"theorem {name} {{{' '.join(xs)} : Tape}} {hyps} :\n    Vis .{q} ({cons([B(c) for c in tok.replace('1','x').replace('0','o').replace('x','1').replace('o','0').encode() and [int(c) for c in tok]],'x')}) .{r} ({cons([B(int(c)) for c in tok2],xs[-1])}) := by")
    L.append("  intro a L")
    def left(c): # left stream when head is at the call (all W cells to the left), nearest first
        return cons([B(v) for v in reversed(c)],"cons a L")
    chain=[]
    for i,(stt,kk,cend,qcall,ret) in enumerate(segs):
        c0,s0=stt
        if i==0: src=f"⟨cons a L, {cons([B(v) for v in c0],'x')}, .{S[s0]}⟩"
        else: src=f"⟨{cons([B(v) for v in reversed(c0[:-1])],'cons a L')}, {cons([B(c0[-1])],xs[i])}, .{S[s0]}⟩"
        L.append(f"  have s{i} : steps {kk} {src} = some ⟨{left(cend)}, {xs[i]}, .{S[qcall]}⟩ := rfl")
        L.append(f"  obtain ⟨t{i+1}, c{i+1}⟩ := h{i+1} {B(cend[-1])} ({cons([B(v) for v in reversed(cend[:-1])],'cons a L')})")
        chain+= [f"s{i}",f"c{i+1}"]
    c0,s0=start; i=len(segs)
    if i==0: src=f"⟨cons a L, {cons([B(v) for v in c0],'x')}, .{S[s0]}⟩"
    else: src=f"⟨{cons([B(v) for v in reversed(c0[:-1])],'cons a L')}, {cons([B(c0[-1])],xs[i])}, .{S[s0]}⟩"
    L.append(f"  have s{i} : steps {k} {src} = some ⟨L, cons a ({cons([B(int(c)) for c in tok2],xs[-1])}), .{r}⟩ := rfl")
    chain.append(f"s{i}")
    e=chain[-1]
    for c in reversed(chain[:-1]): e=f"steps_seq trans {c} ({e})"
    L.append(f"  exact ⟨_, {e}⟩\n")
    out.append("\n".join(L))
out.append(f"end {ns}")
print("\n".join(out).replace("{W}",str(len(rows[0][1]))))
