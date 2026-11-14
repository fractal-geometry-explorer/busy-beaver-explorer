import sys
sys.setrecursionlimit(1000000)
from fractions import Fraction as Fr
import tokz
from tokz import T,stats
def val(T):
    n=len(T)
    V=[None]*(n+3); F=[None]*(n+3); G=[None]*(n+3)
    V[n]=V[n+1]=V[n+2]=Fr(0); F[n]=F[n+1]=Fr(1); G[n]=G[n+1]=Fr(1)
    for i in range(n-1,-1,-1):
        t=T[i]
        # V
        if t=='L': V[i]=V[i+1]/2 if V[i+1] is not None else None
        elif t=='O': V[i]=2*V[i+1] if V[i+1] is not None else None
        elif t=='I': V[i]=1+2*V[i+1] if V[i+1] is not None else None
        elif t=='z': V[i]=G[i+1]-1 if G[i+1] is not None else None
        elif t=='x': V[i]=F[i+1]
        elif t=='1': V[i]=G[i+1]
        # F,G need token at i
        if t=='O':
            F[i]=2*F[i+1]-1 if F[i+1] is not None else None
            G[i]=2*G[i+1]-1 if G[i+1] is not None else None
        elif t=='L':
            F[i]=F[i+1]/2 if F[i+1] is not None else None
            G[i]=(G[i+1]-1)/2 if G[i+1] is not None else None
        elif t=='I':
            F[i]=(G[i+1]-1)/2 if G[i+1] is not None else None
            u=T[i+1] if i+1<n else 'O'
            if u=='O': G[i]=V[i+2]-1 if V[i+2] is not None else None
            elif u=='I': G[i]=4*G[i+2]-1 if G[i+2] is not None else None
            elif u=='L': G[i]=4*F[i+2]+3 if F[i+2] is not None else None
            else: G[i]=None
        else: F[i]=G[i]=None
    return V[0]
if __name__=='__main__':
    R=int(sys.argv[1])
    T[:]=list('LLLzLLOLOI'); bad=0
    for k in range(6,R+1):
        a=val(T); tokz.An(1,0); b=val(T)
        if b-a!=1: bad+=1; print('VIOL',k,a,b)
        T.insert(0,'x'); tokz.norm()
        while T and T[-1]=='O': T.pop()
        c=val(T)
        if k%25==0 or k<12: print(k,'v before',float(a),'after A',float(b),'next round start',float(c))
    print('violations',bad)
