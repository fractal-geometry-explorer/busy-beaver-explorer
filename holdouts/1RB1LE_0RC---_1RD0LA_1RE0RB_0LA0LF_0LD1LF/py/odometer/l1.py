"""Level 1: one trip (R-instant to next R-instant) of 1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF on a token
configuration, exactly, by substituting each long block a^n (a = 100) by a^n' with n' = n mod 12 in [SB, SB+12),
and correcting the step count by the per-word cost measured inside each block."""
import re
TT={0:((1,1,1),(1,-1,4)),1:((0,1,2),None),2:((1,1,3),(0,-1,0)),3:((1,1,4),(0,1,1)),4:((0,-1,0),(0,-1,5)),5:((0,-1,3),(1,-1,5))}
FOLD=16; SB=48; BIG=32; MARG=12
_TO01=bytes.maketrans(b'01',b'\x00\x01'); _TOCH=bytes.maketrans(b'\x00\x01',b'01')
def fold(toks):
    out=[toks[0]]
    for i in range(1,len(toks),2):
        n,g=toks[i],toks[i+1]
        if n<FOLD: out[-1]=out[-1]+'100'*n+g
        else: out+= [n,g]
    return out
def parse(cells, thr):
    toks=['']; i=0
    for m in re.finditer(r'(?:100){%d,}'%thr, cells):
        toks[-1]+=cells[i:m.start()]; toks+=[ (m.end()-m.start())//3, '']; i=m.end()
    toks[-1]+=cells[i:]
    return toks
def trip(state, toks, maxsteps=10**8, nosub=False):
    """Returns (state, toks, steps, leftvisits) or ('HALT', steps, toks)."""
    big=[toks[i] for i in range(1,len(toks),2)]
    syn=list(big) if nosub else [SB+((n-SB)%12) for n in big]
    pad=64
    cells='0'*pad+toks[0]; regs=[]
    for n,i in zip(syn,range(1,len(toks),2)):
        a=len(cells); cells+='100'*n; regs.append([a+MARG, a+3*n-MARG]); cells+=toks[i+1]
    tape=bytearray(cells.encode().translate(_TO01))
    h=len(tape)-2; hi=len(tape)-1; lo=tape.index(1) if 1 in tape else h; minh=h; s=state; d=-1; st=0; lv=0; off=0
    inside=[0]*len(regs)
    # region lookup: since regions are sorted, use a dict cell->region index for interior cells
    rid=[-1]*len(tape)
    for j,(a,b) in enumerate(regs):
        rid[a:b]=[j]*(b-a)
    while True:
        if h<8:
            tape[0:0]=bytearray(pad); rid[0:0]=[-1]*pad; h+=pad; hi+=pad; lo+=pad; minh+=pad; off+=pad
        c=tape[h]
        r=TT[s][c]
        if r is None: return ('HALT',st,toks)
        j=rid[h] if h<len(rid) else -1
        if j>=0: inside[j]+=1
        tape[h]=r[0]; h+=r[1]; s=r[2]; st+=1
        if h>=len(tape): tape.append(0); rid.append(-1)
        if h<minh: minh=h
        if h>hi: hi=h
        if h>=hi-1 and d==1: break
        if h<hi-30: d=1
        if st>maxsteps: raise Exception('long trip')
    lv=max(0,lo-minh)
    cells=bytes(tape[:hi+1]).translate(_TOCH).decode()
    thr=min(big)-8 if nosub else BIG
    res=['']; i0=0; runs=[]
    for m in re.finditer(r'(?:100){%d,}'%thr, cells):
        res[-1]+=cells[i0:m.start()]; res+=[(m.end()-m.start())//3,'']; i0=m.end(); runs.append((m.start(),m.end()))
    res[-1]+=cells[i0:]
    # map original blocks (by interior midpoint, shifted by the left padding added) to new runs
    owner=[None]*len(big)
    for j,(a_,b_) in enumerate(regs):
        mid=(a_+b_)//2+off
        for q,(x,y) in enumerate(runs):
            if x<=mid<y: owner[j]=q; break
        if owner[j] is None: raise Exception('block %d lost'%j)
    real=st
    for j in range(len(big)):
        w=(regs[j][1]-regs[j][0])//3
        rate=round(inside[j]/w)
        if abs(inside[j]-rate*w)>16: raise Exception('non-uniform crossing in block %d: %d steps over %d words'%(j,inside[j],w))
        real+=rate*(big[j]-syn[j])
    new=[res[0]]
    for q,i in enumerate(range(1,len(res),2)):
        cov=[j for j in range(len(big)) if owner[j]==q]
        if not cov: raise Exception('new big run without origin')
        new+=[res[i]+sum(big[j]-syn[j] for j in cov), res[i+1]]
    out=[]
    for i,x in enumerate(new):
        if i%2==0:
            p=parse(x,FOLD)
            if out and isinstance(out[-1],str): out[-1]+=p[0]; out+=p[1:]
            else: out+=p
        else: out.append(x)
    out=fold(out); out[0]=out[0].lstrip('0')
    return (s,out,real,lv)
