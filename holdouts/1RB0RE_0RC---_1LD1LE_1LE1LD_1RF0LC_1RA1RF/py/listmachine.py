"""The list machine of lean/End.lean (`astep`), in Python, run in lockstep with the real machine.

States at right turns: ('T', w, p, s, r) is Turn w p s with the tape ending in one 1 if r; ('T2', N, O, p, s, r) the
same during a crossing (near part N, a lone 1, far part O); ('EO', W, Z) E on the last 1.  ('V', state) marks a turn
handed back by the right end, which the machine reaches by a left move, so it is not compared with a right turn.
`Danger` is raised in the two cases the list machine does not cover (`astep = none` in Lean).

  python3 listmachine.py [N]   compare with every right turn of the first N steps (default 2*10^6)
"""
import sys
from collections import Counter
from turnshape import rswL, sx, par, T, tok_left, tok_right
F,Tr=False,True
class Danger(Exception): pass
# states: ('T',w,p,s,r)  ('T2',N,O,p,s,r)  ('EO',W,Z)  Z=('pre',p) | ('o',O,p)
def canon(st):
    if st[0]=='V': return st
    if st[0]=='T2':
        _,N,O,p,s,r=st
        N=list(N);O=list(O)
        while O and not O[0]: N.append(F); O.pop(0)
        if not O:
            # o next to prefix
            if not p: return ('T',tuple(N),1,s,r)
            return ('T',tuple(N+[F]),0,s,r)
        return ('T2',tuple(N),tuple(O),p,s,r)
    if st[0]=='EO' and st[2][0]=='o':
        W,(_,O,p)=st[1],st[2]
        W=list(W);O=list(O)
        while O and not O[0]: W.append(F); O.pop(0)
        if not O:
            return ('EO',tuple(W),('pre',1)) if not p else ('EO',tuple(W+[F]),('pre',0))
        return ('EO',tuple(W),('o',tuple(O),p))
    return st
def end(W,e,r,Z):
    W=tuple(W)
    if not e and not r:
        if Z[0]=='pre': return ('V',('T2',(),W,Z[1],(),1))
        raise Danger('A: F reaches blank end inside a crossing')
    if e and r: return ('EO',W,Z)
    if Z[0]=='pre': return ('V',('T',(F,)+W,Z[1],(),1))
    return ('V',('T2',(F,)+W,Z[1],Z[2],(),1))
def bounce_plain(w,p,tail,r):
    # zone w with prefix p, left sweep from C, then right sweep over (sx true w).reverse ++ tail
    W,e,rest=rswL(0,[0],list(reversed(sx(1,list(w))))+list(tail))
    p2=p^par(1,list(w))
    if rest is not None: return ('T',tuple(W),p2,tuple(rest),r)
    return end(W,e,r,('pre',p2))
def bounce_o(N,O,p,tail,r):
    q=par(1,list(N))
    if q:
        assert O[0]
        O2=(F,)+tuple(O[1:]); Z=('o',O2,p)
    else:
        W1,e1,r1=rswL(0,[0],list(reversed(sx(0,list(O)))))
        if r1 is not None or e1: raise Danger('even bounce blocked by far part')
        p=p^par(0,list(O)); O2=tuple(W1); Z=('o',O2,p)
    W2,e2,rest=rswL(0,[],list(reversed(sx(1,list(N))))+list(tail))
    if rest is not None: return ('T2',tuple(W2),O2,p,tuple(rest),r)
    return end(W2,e2,r,Z)
def step(st):
    while True:
        st=step1(st)
        if st[0]!='V': return st
        st=st[1]
def step1(st):
    st=canon(st)
    k=st[0]
    if k=='T':
        _,w,p,s,r=st; return canon(bounce_plain(w,p,(Tr,)+tuple(s),r))
    if k=='T2':
        _,N,O,p,s,r=st; return canon(bounce_o(N,O,p,(Tr,)+tuple(s),r))
    _,W,Z=st
    if Z[0]=='pre': return canon(bounce_plain(W,Z[1],(),0))
    return canon(bounce_o(W,Z[1],Z[2],(),0))
def cells(st):
    """far-to-near left cells | head-and-right cells (trailing zeros stripped)"""
    st=canon(st)
    lt=lambda x:'01' if x else '11'   # far-to-near order of a letter's two cells: b = (near 0, far 1) -> '10' far-first
    lt=lambda x:'10' if x else '11'
    rt=lambda x:'01' if x else '11'
    pre=lambda p:'1' if p else ''
    k=st[0]
    if k=='T':
        _,w,p,s,r=st
        L=pre(p)+''.join(lt(x) for x in reversed(w)); R='11'+''.join(rt(x) for x in s)+('1' if r else '')
    elif k=='T2':
        _,N,O,p,s,r=st
        L=pre(p)+''.join(lt(x) for x in reversed(O))+'1'+''.join(lt(x) for x in reversed(N)); R='11'+''.join(rt(x) for x in s)+('1' if r else '')
    else:
        _,W,Z=st
        if Z[0]=='pre': L=pre(Z[1])+''.join(lt(x) for x in reversed(W))
        else: L=pre(Z[2])+''.join(lt(x) for x in reversed(Z[1]))+'1'+''.join(lt(x) for x in reversed(W))
        R='1'
    return L.lstrip('0')+'|'+R.rstrip('0')

def lockstep(N):
    tape,h,st,lo,hi,mv={},0,'A',0,0,0
    abs_=None;ok=0;kinds=Counter()
    for t in range(N):
        a=T[(st,tape.get(h,0))]
        if st=='E' and mv==1 and a[1]==-1:
            real=''.join(str(tape.get(j,0)) for j in range(lo,h)).lstrip('0')+'|'+''.join(str(tape.get(j,0)) for j in range(h,hi+2)).rstrip('0')
            if abs_ is None:
                # first turn: decode as plain Turn by brute: try build from real
                Ls,Rs=real.split('|')
                print('first right turn at',t,real); 
                # seed: parse
                L=tok_left(tape,h,lo);R=tok_right(tape,h,hi)
                p=1 if L.startswith('o') else 0
                body=L[1:] if p else L
                if 'o' in body:
                    Of,Nf=body.rsplit('o',1); O=tuple(x=='b' for x in reversed(Of))
                else: Of,Nf,O=None,body,None
                w=tuple(x=='b' for x in reversed(Nf))
                if R=='o': abs_=('EO',w,('pre',p) if O is None else ('o',O,p))
                else:
                    s_=tuple(x=='c' for x in R[1:].rstrip('o')); r=1 if R.endswith('o') else 0
                    abs_=('T',w,p,s_,r) if O is None else ('T2',w,O,p,s_,r)
            else:
                try: abs_=step(abs_)
                except Danger as d: print('DANGER',t,d); break
            if cells(abs_)!=real:
                print('MISMATCH at',t,abs_[0]); print(' abs ',cells(abs_)[-80:]); print(' real',real[-80:]); break
            ok+=1; kinds[canon(abs_)[0]]+=1
        tape[h]=a[0];h+=a[1];mv=a[1];st=a[2];lo=min(lo,h);hi=max(hi,h)
    print('matched',ok,'right turns',dict(kinds))


if __name__ == '__main__':

    lockstep(int(float(sys.argv[1])) if len(sys.argv) > 1 else 2 * 10 ** 6)
