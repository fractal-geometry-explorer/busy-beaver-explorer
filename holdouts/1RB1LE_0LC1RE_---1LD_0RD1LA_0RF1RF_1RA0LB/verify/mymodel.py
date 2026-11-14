# Independent re-implementation of the level odometer (own cell simulator, own bookkeeping).
# Table (separator, kind) per position taken from the README (the claim under test); it is checked separately
# against my direct simulation (structure.py).  Step constants are passed in (measured by measure.py with my sim).
import sys, json
from lib import digits, from_digits, fmt
MACH="1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB"
TR={}
for s,row in enumerate(MACH.split('_')):
    for r in range(2):
        q=row[3*r:3*r+3]
        TR[s,r]=None if q[0]=='-' else (int(q[0]),1 if q[1]=='R' else -1,ord(q[2])-65)
SEP=[(0,1,0,1),(0,3,1),(7,1),(5,3),(0,6),(0,1,0,1),(5,0,1),(7,1),(0,1,3),(0,6),(10,),(5,0,1),(0,3,1),(0,1,3),(5,3),(10,)]
KIND="HVHVHVHVHVHVHVHV"
PASSK={2:'H',4:'V',7:'H',10:'V',12:'H',15:'V'}
GROW={3,7,11,15}
POSOF={(SEP[i],KIND[i]):i for i in range(16)}
FRONTD={'H':[2,1],'V':[5]}
REG={'H':"<C>E<E>F<B>E<C>A<D>E",'V':"<C>E"}

def one_visit(cells, bnd):
    """cells: list, head on blank right of it in A. returns (halted, steps, sig, cells, headpos_rel_left_edge)"""
    t=cells; off=0; p=len(t); s=0; n=0; top=p-1; sig=[]
    while True:
        if p-off>=len(t): t.append(0)
        if p-off<0: t[0:0]=[0]*64; off-=64   # index = p-off
        r=t[p-off]; tr=TR[s,r]
        if tr is None: return True,n,''.join(sig),t,p
        t[p-off]=tr[0]; q=p+tr[1]
        if bnd is not None:
            if p>=bnd>q: sig.append('<'+'ABCDEF'[tr[2]])
            if p<bnd<=q: sig.append('>'+'ABCDEF'[tr[2]])
        top=max(top,p); p=q; s=tr[2]; n+=1
        if s==0 and p>top: break
    out=t[:p-off]
    while out and out[0]==0: out.pop(0)
    return False,n,''.join(sig),out,None

def dist_to_pass(pos):
    d=0
    while (pos+d)%16 not in PASSK: d+=1
    return d
def advance(pos,n,y):
    q,r=divmod(y,16); n+=4*q
    for _ in range(r):
        if pos in GROW: n+=1
        pos=(pos+1)%16
    return pos,n
def hits_for_passes(pos,x):
    """hits needed (from pos) so that exactly x hits have been passed on, ending right after the x-th pass"""
    if x==0: return 0
    full,rem=divmod(x,6)
    if rem==0: full-=1; rem=6
    y=16*full
    while rem:
        if pos in PASSK: rem-=1
        pos=(pos+1)%16; y+=1
    return y

class Model:
    def __init__(self, tape, LA, LB, FC, keep=1):
        self.lv=[]          # peeled levels [pos,n], outermost first
        self.red=[int(c) for c in tape]   # reduced tape cells
        self.keep=keep; self.LA,self.LB,self.FC=LA,LB,FC
        self.visits=0; self.steps=0; self.nhits=0; self.unpeels=0; self.maxunpeel=0
    def cost(self,pos,n,y):
        """steps inside a level during its next y hits (bigint closed form over whole 16-cycles + remainder)"""
        LA,LB=self.LA,self.LB
        q,r=divmod(y,16); tot=0
        if q:
            # one cycle starting at (pos,n): sum LA[p]*(n+g_p)+LB[p]
            A=0;B=0;g=0;p=pos
            for _ in range(16):
                A+=LA[p]; B+=LA[p]*g+LB[p]
                if p in GROW: g+=1
                p=(p+1)%16
            # cycle j (0-based) starts with n+4j
            tot+=q*(A*n+B)+A*4*(q*(q-1)//2)
            n+=4*q
        p=pos
        for _ in range(r):
            tot+=LA[p]*n+LB[p]
            if p in GROW: n+=1
            p=(p+1)%16
        return tot
    def parse(self):
        d=digits(''.join(map(str,self.red)))
        if d[0]==5: k='V'; rest=d[1:]
        elif d[:2]==[2,1]: k='H'; rest=d[2:]
        else: raise RuntimeError('no front: '+fmt(d)[:80])
        return k,rest
    def split(self,k,rest):
        """greedy levels at the head side of rest. returns list of (pos,n), kind for remaining tail, tail digits"""
        out=[]
        while True:
            n=0
            while n<len(rest) and rest[n]==4: n+=1
            if n==0 or n==len(rest): break   # last digit is not X-terminated
            hit=None
            for s in set(SEP):
                if tuple(rest[n:n+len(s)])==s and n+len(s)<len(rest): hit=s
            # separators are prefix-free as digit strings? check uniqueness
            cands=[s for s in set(SEP) if tuple(rest[n:n+len(s)])==s and n+len(s)<len(rest)]
            assert len(cands)<=1
            if not cands: break
            s=cands[0]; pos=POSOF[(s,k)]
            out.append((pos,n)); rest=rest[n+len(s):]
            k=PASSK[(pos+dist_to_pass(pos))%16]
        return out,k,rest
    def repeel(self):
        k,rest=self.parse()
        lv,kt,tail=self.split(k,rest)
        m=len(lv)-self.keep
        if m<=0: return
        self.lv+=[list(x) for x in lv[:m]]
        kk=PASSK[(lv[m-1][0]+dist_to_pass(lv[m-1][0]))%16]
        d=FRONTD[kk][:]
        for pos,n in lv[m:]: d+=[4]*n+list(SEP[pos])
        d+=tail
        self.red=[int(c) for c in from_digits(d)]
    def ready(self):
        e=0
        for i in range(len(self.lv)-1,-1,-1):
            pos,n=self.lv[i]
            y=hits_for_passes(pos,e)
            p2,_=advance(pos,n,y)
            y+=dist_to_pass(p2)
            self.steps+=self.cost(pos,n,y)
            self.lv[i]=list(advance(pos,n,y))
            e=y
        if self.lv:
            # front: e hits alternating kinds starting with the kind the top level was waiting for
            k0=KIND[(self.lv[0][0]-e)%16]
            a=(e+1)//2; b=e//2
            self.steps+=self.FC[k0]*a+self.FC['V' if k0=='H' else 'H']*b
        self.visits+=2*e
    def full_digits(self):
        k,rest=self.parse()
        if self.lv: k=KIND[self.lv[0][0]]
        d=FRONTD[k][:]
        for pos,n in self.lv:
            assert n<10**6; d+=[4]*n+list(SEP[pos])
        return d+rest
    def all_levels(self):
        k,rest=self.parse(); lv,kt,tail=self.split(k,rest)
        return [tuple(x) for x in self.lv]+lv, tail
    def hit(self):
        """one hit reaching the reduced word. returns None or ('halt', info)"""
        self.repeel(); self.ready()
        depth=0
        while True:
            k,rest=self.parse()
            if self.lv: assert self.lv[-1][0] in PASSK and PASSK[self.lv[-1][0]]==k
            bnd=len(self.red)-2*(sum(FRONTD[k])+len(FRONTD[k]))
            halted,n1,sig,c1,hp=one_visit(self.red[:],bnd)
            if halted:
                return ('halt',n1,sig,hp,k)
            if sig==REG[k]:
                h2,n2,_,c2,_=one_visit(c1,None)
                assert not h2 and n2==8
                break
            if not self.lv: raise RuntimeError('irregular hit reaches the front (reset): sig %s at visit %d'%(sig,self.visits))
            pos,n=self.lv.pop(); depth+=1; self.unpeels+=1; self.maxunpeel=max(self.maxunpeel,depth)
            assert n<10**7
            d=FRONTD[KIND[pos]]+[4]*n+list(SEP[pos])+rest
            self.red=[int(c) for c in from_digits(d)]
        # bookkeeping: the hit travels through all peeled levels
        self.steps+=n1+n2-self.FC[k]+self.FC[KIND[self.lv[0][0]] if self.lv else k]
        for L in self.lv:
            self.steps+=self.LA[L[0]]*L[1]+self.LB[L[0]]
            L[0],L[1]=advance(L[0],L[1],1)
        self.visits+=2; self.nhits+=1; self.red=c2
        return None
