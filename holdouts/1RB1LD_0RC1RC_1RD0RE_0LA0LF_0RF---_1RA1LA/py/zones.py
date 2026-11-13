"""usage: python3 zones.py STEPS OUT: the accelerated run (fastsim), writing each change of the defect list of the first
60 cells at the right-end turns (state A: growth, D: stall) with the step count and length.  Unproved jumps."""
import sys
from fastsim import run
M='1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA'
ZW=60
state={'last':None,'n':0}
def info(r):
    lw, rw = r.runs()
    runs=lw+rw
    while runs and set(runs[0][0])=={'0'}: runs=runs[1:]
    while runs and set(runs[-1][0])=={'0'}: runs=runs[:-1]
    s=''
    for w,c in runs:
        if len(s)>ZW+10: break
        s+=w*min(c,40)
    s=s.lstrip('0')
    tot=sum(len(w)*c for w,c in runs)
    lead=len(runs[0][0])-len(runs[0][0].lstrip('0')); trail=len(runs[-1][0])-len(runs[-1][0].rstrip('0'))
    d=tuple(i for i in range(3,min(len(s),ZW)) if s[i]!=s[i-3])
    return tot-lead-trail, d
out=open(sys.argv[2],'w')
def on_end(r):
    if r.dir==1 and len(r.right)<=3:
        L,d=info(r)
        if r.state not in (0,3): return
        key=(d,r.state)
        if key!=state['last']:
            out.write('%d %d %s %s\n'%(r.steps,L,'ABCDEF'[r.state],' '.join(map(str,d)))); out.flush()
            state['last']=key
run(M,3,float(sys.argv[1]),on_end,NF=3)
