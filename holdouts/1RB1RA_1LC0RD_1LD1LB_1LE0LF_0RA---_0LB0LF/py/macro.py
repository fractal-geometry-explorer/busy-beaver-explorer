"""Macro simulator of W = 1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB0LF (PR 93's T3 with F1 := 0LF) on PR 93's 21 rules.
Tape: two stacks, top = next to the head.  L[-1] = cell left of head, R[-1] = head cell (raw mode) or the first cell
after the mode prefix (macro modes).  Macro modes: 'R' = A on 0100, 'L' = B on 1, 'J' = C on 100 (prefix implicit)."""
import sys, collections
W='1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB0LF'
def parse(m):
    T={}
    for qi,part in enumerate(m.split('_')):
        for b in (0,1):
            tr=part[3*b:3*b+3]
            T[(qi,b)]=None if tr[0] in '-H' else (int(tr[0]),1 if tr[1]=='R' else -1,qi if False else 'ABCDEF'.index(tr[2]))
    return T
TW=parse(W)
WALL=True
PRE={'R':[0,1,0,0],'L':[1],'J':[1,0,0]}
STATE={'R':0,'L':1,'J':2}
def g(S,i):  # i-th cell outward (0 = top)
    return S[-1-i] if i<len(S) else 0
def ones(S,i):
    n=0
    while g(S,i+n)==1: n+=1
    return n
def matchD(S,i):
    """D_n at outward offset i on the RIGHT stack (outward = tape order): 1(11)^n 00 -> (n, length)"""
    c=ones(S,i)
    if c%2==1 and g(S,i+c)==0 and g(S,i+c+1)==0: return (c-1)//2, c+2
    return None
def matchS(S,i):
    """S_n = 1(01)^(n+1), outward (busycoq's l <* xs puts hd xs next to the head) -> (n, length)"""
    if g(S,i)!=1: return None
    k=0
    while g(S,i+1+2*k)==0 and g(S,i+2+2*k)==1: k+=1
    if k>=1: return k-1, 2*k+1
    return None
def pop(S,n):
    for _ in range(n):
        if S: S.pop()
def push_out(S,cells):
    """push cells given in OUTWARD order (first = next to head)"""
    for x in reversed(cells): S.append(x)
def Dw(n): return [1]+[1,1]*n+[0,0]
def Sw_out(n): return [1]+[0,1]*(n+1)
def O(*ws):
    """l <* w1 <* ... <* wk : outward order is wk ++ ... ++ w1"""
    out=[]
    for w in reversed(ws): out+=w
    return out  # a word written in tape order on the left, outward order
def blank(S,i): return all(x==0 for x in S[:len(S)-i])
class Mac:
    def __init__(s):
        s.L=[]; s.R=[]; s.mode=('raw',0); s.rule=collections.Counter(); s.rawsteps=0; s.halt=None; s.D0=[]
    # ---------- raw ----------
    def rawstep(s):
        q=s.mode[1]; b=g(s.R,0); w,d,q2=TW[(q,b)]
        if q==3 and b==0:   # D reads 0: M halts iff left cell is 1
            s.D0.append(g(s.L,0))
            if g(s.L,0)==1: s.halt='D0 with left 1'; return
        pop(s.R,1)
        if d==1: s.L.append(w)
        else:
            y=s.L.pop() if s.L else 0
            s.R.append(w); s.R.append(y)
        s.mode=('raw',q2); s.rawsteps+=1
    def tomacro(s):
        """in raw mode: if the configuration is a macro mode in which a rule applies, switch to it"""
        q=s.mode[1]
        for md in 'RLJ':
            if STATE[md]!=q: continue
            off=0 if md=='R' else 1      # R: prefix starts at the head cell; L/J: head cell is on top of l, prefix after it
            if all(g(s.R,off+i)==x for i,x in enumerate(PRE[md])):
                savedR=s.R[:]; savedL=s.L[:]
                if md!='R': s.L.append(s.R.pop() if s.R else 0)
                pop(s.R,len(PRE[md])); s.mode=('mac',md)
                if s.applicable(): return True
                s.R=savedR; s.L=savedL; s.mode=('raw',q)
        return False
    def toraw(s):
        md=s.mode[1]; push_out(s.R,PRE[md])
        if md!='R': s.R.append(s.L.pop() if s.L else 0)
        s.mode=('raw',STATE[md])
    # ---------- rules ----------
    def applicable(s):
        return s.find() is not None
    def find(s):
        L,R=s.L,s.R; md=s.mode[1]
        if md=='R':
            if blank(R,0): return ('emptyR',)
            if g(R,0)==0 and g(R,1)==0 and g(R,2)==0: return ('blank',)
            d=matchD(R,0)
            if d: return ('right',d)
            c=ones(R,0)
            if c>=2 and c%2==0 and g(R,c)==0 and g(R,c+1)==0: return ('even',c//2-1,c+2)
            if g(R,0)==1 and g(R,1)==0:
                k=0
                while g(R,2*k)==1 and g(R,2*k+1)==0 and not (g(R,2*k+2)==0): k+=1
                # k = number of leading "10" not followed by 0 (i.e. not D0)
                if k>=2 and k%2==0:
                    d=matchD(R,2*k)
                    if d: return ('paired',k//2,d)
                d1=matchD(R,2)
                if d1:
                    n,ln=d1; i=2+ln
                    d2=matchD(R,i)
                    if n==0 and d2 and d2[0]==0: return ('collide',)
                    if n>=2 and d2 and d2[0]==n: return ('pairR',n-2)
                    c=ones(R,i)
                    if c%2==1 and g(R,i+c)==0:
                        m=(c-1)//2
                        if n==0: return ('defect0',m,i+c+1)
                        if n==1: return ('defect1',m,i+c+1)
                        return ('defect2',n-2,m,i+c+1)
                    if c==0 and g(R,i)==0 and g(R,i+1)==0:
                        if n==0: return ('defect_blank0',i+2)
                        return ('defect_blankS',n-1,i+2)
            return None
        if md=='L':
            sm=matchS(L,0)
            if sm: return ('left',sm)
            k=0
            while g(L,2*k)==1 and g(L,2*k+1)==0: k+=1
            if k>=1:
                if g(L,2*k)==1 and g(L,2*k+1)==1 and g(L,2*k+2)==1: return ('restart',k-1)
                if g(L,2*k)==1 and g(L,2*k+1)==1 and blank(L,2*k+2): return ('overflow2',k-1)
                if g(L,2*k)==1 and blank(L,2*k+1):
                    d=matchD(R,0)
                    if d: return ('overflow1',k-1,d)
                if [g(L,2*k+i) for i in range(5)]==[0,1,1,0,1]: return ('finishP',k-1)
            if [g(L,i) for i in range(6)]==[0,0,1,1,0,1]: return ('collision',)
            if g(L,0)==1 and g(L,1)==1:
                d=matchD(R,0)
                if d: return ('turnB',d)
            if WALL and blank(L,0):
                d=matchD(R,0)
                if d:
                    a,ln=d; c=ones(R,ln)
                    if c%2==1 and g(R,ln+c)==0: return ('wall0',a,(c-1)//2,ln+c+1)
            if WALL and g(L,0)==1 and blank(L,1):
                d=matchD(R,0)
                if d: return ('wall1',d)
            return None
        if md=='J':
            sm=matchS(L,0)
            if sm: return ('leftJ',sm)
            k=0
            while g(L,2*k)==1 and g(L,2*k+1)==0: k+=1
            if g(L,2*k)==1 and g(L,2*k+1)==1 and g(L,2*k+2)==1: return ('turnJ',k)
            return None
    def apply(s,r):
        L,R=s.L,s.R; nm=r[0]; s.rule[nm]+=1
        if nm=='emptyR' or nm=='blank':
            if nm=='blank': pop(R,3)
            push_out(R,Dw(0)+Dw(0)); s.mode=('mac','L')
        elif nm=='right':
            n,ln=r[1]; pop(R,ln); push_out(L,Sw_out(n))
        elif nm=='even':
            n,ln=r[1],r[2]; pop(R,ln); push_out(R,Dw(1+n)+[1,0]); s.mode=('mac','L')
        elif nm=='paired':
            k,(n,ln)=r[1],r[2]; pop(R,4*k+ln)
            push_out(L,O(Sw_out(0),[1,1,0,1]*k,[1,0]*n))
        elif nm=='collide':
            pop(R,2+3+3); push_out(R,Dw(2)+[1,0]); s.mode=('mac','J')
        elif nm=='pairR':
            n=r[1]; pop(R,2+2*(2*(n+2)+3)); PL=[1,0]*(n+4)+[1,1]*n+Sw_out(0)+Sw_out(0)
            push_out(L,PL); push_out(R,[1,0])
        elif nm=='defect0':
            m,ln=r[1],r[2]; pop(R,ln); push_out(R,[1,1,1,1]+Dw(m)+[1]); s.mode=('mac','J')
        elif nm=='defect1':
            m,ln=r[1],r[2]; pop(R,ln); push_out(R,Dw(0)+Dw(0)+Dw(1+m)+[1]); s.mode=('mac','L')
        elif nm=='defect2':
            n,m,ln=r[1],r[2],r[3]; pop(R,ln)
            push_out(L,O(Sw_out(0),Sw_out(0),[1,1]*n,[1,0]*(2+m))); push_out(R,[1])
        elif nm=='defect_blank0':
            pop(R,r[1]); push_out(L,O(Sw_out(0),[1,0,0,1]))
        elif nm=='defect_blankS':
            n,ln=r[1],r[2]; pop(R,ln); push_out(L,O(Sw_out(0),Sw_out(0),[1],[1,1]*n,[1,0]))
        elif nm=='left':
            n,ln=r[1]; pop(L,ln); push_out(R,Dw(n))
        elif nm=='restart':
            b=r[1]; pop(L,2*(b+1)+3); push_out(L,[1,0]*(1+b)); s.mode=('mac','R')
        elif nm=='overflow2':
            b=r[1]; L.clear(); push_out(L,O([1,1]*(1+b),[1,0]*2)); push_out(R,[1]); s.mode=('mac','R')
        elif nm=='overflow1':
            b,(n,ln)=r[1],r[2]; L.clear(); pop(R,ln); push_out(L,O([1,1]*b,[1,0]*(n+2))); push_out(R,[1,0]); s.mode=('mac','R')
        elif nm=='finishP':
            b=r[1]; pop(L,2*(b+1)+2+3); push_out(R,Dw(1+b)); s.mode=('mac','J')
        elif nm=='collision':
            pop(L,6); push_out(R,[1,1,1,1]); s.mode=('mac','J')
        elif nm=='turnB':
            n,ln=r[1]; pop(L,2); pop(R,ln); push_out(L,[1,0]*(1+n)); s.mode=('mac','R')
        elif nm=='leftJ':
            n,ln=r[1]; pop(L,ln); push_out(R,Dw(1+n)); s.mode=('mac','L')
        elif nm=='wall0':
            a,b,ln=r[1],r[2],r[3]; L.clear(); pop(R,ln); push_out(L,O([1,0],[1]*(2*a+2),[1,0]*(b+2))); push_out(R,[1])
        elif nm=='wall1':
            a,ln=r[1]; L.clear(); pop(R,ln); push_out(L,[1,0]*(a+3)); push_out(R,[1,0])
        elif nm=='turnJ':
            b=r[1]; pop(L,2*b+3); push_out(L,[1,0]*(1+b)); s.mode=('mac','R')
        while L and L[0]==0 and not getattr(L,'open',False): L.pop(0)
        while R and R[0]==0 and not getattr(R,'open',False): R.pop(0)
    def step(s):
        if s.mode[0]=='mac':
            r=s.find()
            if r is None: s.toraw(); s.rule['->raw']+=1; return
            s.apply(r)
        else:
            if s.tomacro(): return
            s.rawstep()
    def tape(s):
        """(state, left tape order, right from head) in raw terms"""
        R=s.R[:]; L=s.L[:]
        if s.mode[0]=='mac':
            md=s.mode[1]; push_out(R,PRE[md]); q=STATE[md]
            if md!='R': R.append(L.pop() if L else 0)
        else: q=s.mode[1]
        return q, L, list(reversed(R))
