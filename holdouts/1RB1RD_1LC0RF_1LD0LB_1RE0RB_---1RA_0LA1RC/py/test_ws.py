"""test_ws.py MACHINE STEPS: the run-word simulator ws.Sim (shift rules, no cycle jumps) against a cell-by-cell
run: tape, head and state compared at every macro configuration up to STEPS steps."""
import sys
from ws import *
def direct(M,N,check_at):
    T=parse(M); tape={};pos=0;st=0;out={}
    lo=hi=0
    for n in range(N+1):
        if n in check_at:
            out[n]=(''.join(str(tape.get(i,0)) for i in range(lo,hi+1)),pos-lo,st)
        tr=T[(st,tape.get(pos,0))]
        if tr is None: out['halt']=n; break
        tape[pos]=tr[0];pos+=tr[1];st=tr[2];lo=min(lo,pos);hi=max(hi,pos)
    return out
def norm(tape,pos):
    # strip zeros keeping head index
    l=tape[:pos].lstrip('0'); r=tape[pos:].rstrip('0')
    return l,r
M=sys.argv[1]; N=int(float(sys.argv[2]))
s=Sim(M); pts={}
while s.steps<N and s.step():
    pts[s.steps]=None
    l,r=tape_bits(s)
    # head reads nearest cell of faced side: express as (left part, right part from head cell)
    if s.d==1: pts[s.steps]=(l.lstrip('0'), r.rstrip('0'), s.st)
    else:
        # head cell is last of l
        pts[s.steps]=(l[:-1].lstrip('0') if l else '', ((l[-1] if l else '0')+r).rstrip('0'), s.st)
ks=[k for k in pts if k<=N]
dr=direct(M,N,set(ks))
bad=0
for k in ks:
    t,p,st=dr[k]; l,r=norm(t,p)
    if (l,r,st)!=pts[k]:
        bad+=1
        if bad<4: print("MISMATCH at",k,(l[-30:],r[:30],st),(pts[k][0][-30:],pts[k][1][:30],pts[k][2]))
print(M,"checked",len(ks),"macro configs up to step",max(ks),"bad",bad,"macro steps",s.nmacro,s.stats)
