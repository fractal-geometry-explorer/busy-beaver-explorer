import sys,time
from fs import *
Vbits=(1,0,1,1,1,0,1,1,1,0)
def rots(w): return [tuple(w[i:]+w[:i]) for i in range(len(w))]
VW=set(rots(Vbits))|set(tuple(1-z for z in q) for q in rots(Vbits))
def absorb_list(seq):
    """seq in tape order; merge literal copies adjacent to Reps, and adjacent equal-word Reps"""
    changed=True
    while changed:
        changed=False
        for i,t in enumerate(seq):
            if isinstance(t,Rep):
                Lw=len(t.w); w=list(t.w)
                if i>=Lw and all(isinstance(z,int) for z in seq[i-Lw:i]) and seq[i-Lw:i]==w:
                    seq[i-Lw:i+1]=[Rep(t.w,t.n+1)]; changed=True; break
                if i+1+Lw<=len(seq) and all(isinstance(z,int) for z in seq[i+1:i+1+Lw]) and seq[i+1:i+1+Lw]==w:
                    seq[i:i+1+Lw]=[Rep(t.w,t.n+1)]; changed=True; break
                if i+1<len(seq) and isinstance(seq[i+1],Rep) and seq[i+1].w==t.w:
                    seq[i:i+2]=[Rep(t.w,t.n+seq[i+1].n)]; changed=True; break
                # rotation: x (y x)^n -> (x y)^n x : literal before rep equal to last cell
                if Lw>1 and i>=1 and isinstance(seq[i-1],int) and seq[i-1]==t.w[-1] and False:
                    pass
    return seq
def normalize(c):
    L=absorb_list(list(c.L)); R=absorb_list(list(reversed(c.R)))
    c.L=L; c.R=list(reversed(R))
def roundtrip(c,maxmoves=10**7,isck=None):
    for _ in range(maxmoves):
        x=move(c)
        if x and x!='rot' and x[0]=='l' and x[2] in VW: return x
    raise RuntimeError('no checkpoint')
def show(seq):
    out=[];lit=''
    for t in seq:
        if isinstance(t,int): lit+=str(t)
        else:
            if lit: out.append(lit); lit=''
            out.append('0^inf' if t is BL else repr(t))
    if lit: out.append(lit)
    return ' '.join(out)
def load_dump(fn,uoff=0,voff=0):
    d=open(fn).read().split()
    st,p,us,ue,ve=map(int,d[1:6]); b=[int(ch) for ch in d[6]]
    U=b[us:us+20]; Vw=b[ve:ve+10]; K=(ue-us)//20
    L=[BL]+b[:us]+[Rep(U,V(0,K+uoff))]+b[ue:ve]+[Rep(Vw,V(1,4+voff))]+b[ve+40:p]
    R=list(reversed(b[p:]))+[]
    R=[BL]+R
    return Cfg(L,st,R)
if __name__=="__main__":
    c=load_dump(sys.argv[1],110)
    t0=time.time()
    for r in range(int(sys.argv[2])):
        roundtrip(c); normalize(c)
        if r<4 or r%100==0: print(r,round(time.time()-t0,2),c.conc,'L:',show(c.L)[:100],'..',show(c.L)[-80:],c.st,'R:',show(list(reversed(c.R)))[:120])
