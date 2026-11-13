import sys,time
from decide import *
def load_real(fn):
    d=open(fn).read().split()
    st,p,us,ue,ve,mV=map(int,d[1:7]); b=[int(ch) for ch in d[7]]
    U=b[us:us+20]; K=(ue-us)//20
    assert b[us:ue]==U*K
    Vw=b[ve:ve+10]; k=0
    while b[ve+10*k:ve+10*k+10]==Vw and ve+10*k+10<=p: k+=1
    L=[BL]+b[:us]+[Rep(U,C(K))]+b[ue:ve]+[Rep(Vw,C(k))]+b[ve+10*k:p]
    R=[BL]+list(reversed(b[p:]))
    return Cfg(L,st,R),K,k
if __name__=="__main__":
    c,K,k=load_real(sys.argv[1]); print('U',K,'V',k)
    for _ in range(10**7):
        x=move2(c)
        if is_ck(x,c): break
    s=decompose(c)
    print('P',len(s[0]),'st',s[1],'prefix',s[2],'uc',s[4],'X',show(s[5])[:200])
    t0=time.time()
    for r in range(int(sys.argv[2])):
        s2=rt_EX(s)
        if s2 is None: print('stack end at',r,s[4]); break
        s=s2
        if r%500==0: print(r,round(time.time()-t0,1),s[4],show(s[5])[:120],STATS,flush=True)
