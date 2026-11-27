import sys
def parse(m,mirror=False):
    t={}
    for i,p in enumerate(m.split('_')):
        for b in (0,1):
            x=p[3*b:3*b+3]
            if x[0]=='-': t[(i,b)]=None
            else:
                d=1 if x[1]=='R' else -1
                if mirror:d=-d
                t[(i,b)]=(int(x[0]),d,ord(x[2])-65)
    return t
m=sys.argv[1]; mirror=sys.argv[2]=='R'; N=int(float(sys.argv[3])); start=int(float(sys.argv[4])); W=int(sys.argv[5]); ctx=int(sys.argv[6])
t=parse(m,mirror)
from collections import defaultdict
tape=defaultdict(int); p=0; s=0; lo=None; hi=None
intrip=False
def win(a,b): return ''.join(str(tape[q]) for q in range(a,b))
for i in range(N):
    b=tape[p]; r=t[(s,b)]
    if r is None: print("HALT",i); break
    tape[p]=r[0]
    if r[0]:
        if lo is None or p<lo: lo=p
        if hi is None or p>hi: hi=p
    elif b and p==lo:
        while not tape[lo] and lo<hi: lo+=1
    op=p; p+=r[1]; s=r[2]
    if lo is None or i<start: continue
    if not intrip:
        if r[1]>0 and op==lo+W:
            intrip=True; base=lo; mx=p; t0=i; ks=s; kw=win(lo,lo+W+1); kp=win(lo+W+1,lo+W+1+ctx)
    else:
        if p>mx: mx=p
        if r[1]<0 and p==base+W:
            intrip=False
            print(f"{t0:>10} {'ABCDEF'[ks]}> {kw}|{kp}  depth={mx-base-W:<6} dur={i-t0:<8} ret {win(lo,lo+W+1)}<{'ABCDEF'[s]}|{win(lo+W+1,lo+W+1+ctx)} tapelen={hi-lo}")
