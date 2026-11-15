"""Exact accelerated simulation of 1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE, visit by visit.

A visit: the head, in state A, steps onto a never-visited cell at the right end.  Between visits the machine is run by
rl.RL (run-length tape, big counts; every macro step is one transition or a run of a word crossed by a rule that RL
derives from the table on the spot).  The jump: in canonical tokens (canon.py: every run written as a count of 011)
the tape at a visit ends in a zone

    ... n_k s_k n_(k-1) ... s_1 n_0 0 A>        n = (011)^n,  s = 11 (bit 0) or 01 (bit 1)

and one visit is a binary increment of the bits s_k..s_1: the trailing 1s become 0, the lowest 0 (s_i) becomes 1;
n_i loses 1, every s_m that went 1 -> 0 moves one unit from n_(m-1) to n_m, and n_0 gains 2.  It takes
6*(n_0+..+n_(i-1)) + 4i + 11 steps.  `jump` applies V visits at once (closed form), as long as the bits do not
overflow and every count stays above MARGIN; `jump_steps` is the exact number of machine steps of those V visits.

    python3 accel.py            run from blank tape to the halt (about 2.5 minutes), print the halting step count
    python3 accel.py N EVERY    compare with the plain run-length simulator for N visits

check.py validates the pieces (RL against the cell-level simulator, the visit rule against the cell-level simulator
on random zones, the closed forms against odo.py, the accelerated run against RL).
"""
import sys
from rl import RL, Halt
from canon import canon, show
M='1RB1RD_1RC1RB_1LD0RA_1RA0LE_1LF0LC_---1LE'
MARGIN=4

def zone(c):
    """c canonical tokens: ... n_k s_k ... s_1 n_0 '0' with s in {'11' (P, bit 0), '01' (Q, bit 1)}.
    returns (prefix_tokens, counts [n_k..n_0], bits [b_k..b_1]) or None"""
    if len(c)<4 or c[-1]!='0' or not isinstance(c[-2],int): return None
    counts=[c[-2]]; bits=[]; i=len(c)-3
    while i>=1 and c[i] in ('11','01') and isinstance(c[i-1],int) and c[i-1]>=MARGIN+3:
        bits.append(1 if c[i]=='01' else 0); counts.append(c[i-1]); i-=2
    if not bits or counts[0]<MARGIN+3: return None
    counts.reverse(); bits.reverse()
    return c[:i+1],counts,bits

def unzone(pre,counts,bits):
    c=list(pre)
    for n,b in zip(counts,bits): c.append(n); c.append('01' if b else '11')
    c.append(counts[-1]); c.append('0')
    return c

def jump(counts, bits, vmax=None):
    """largest safe number of visits V (binary increments of bits) and the zone after them"""
    k=len(bits)
    B=0
    for b in bits: B=2*B+b
    V=(1<<k)-1-B
    # sep j (1..k) is bits[k-j], at binary position j-1; counts[k-i] is n_i
    for j in range(2,k+1):          # n_{j-1} (j=2..k) loses n10_j <= n01_j+1, and 1 more from its own sep
        p=j-1; n=counts[k-(j-1)]
        F=(B+(1<<p))>>(p+1)
        v=((F+n-MARGIN-2+1)<<(p+1))-1-(1<<p)-B
        if v<V: V=v
    if vmax is not None and V>vmax: V=vmax
    if V<=0: return 0,counts,bits
    B2=B+V
    n01=[0]*(k+2); n10=[0]*(k+2); nb=[0]*(k+2); ob=[0]*(k+2)
    for j in range(1,k+1):
        p=j-1
        n01[j]=((B2+(1<<p))>>(p+1))-((B+(1<<p))>>(p+1))
        ob[j]=(B>>p)&1; nb[j]=(B2>>p)&1
        n10[j]=n01[j]+ob[j]-nb[j]
    newc=[]
    for i in range(k,-1,-1):
        n=counts[k-i]
        if i>=1: n+= -n01[i]+n10[i]
        if i<k: n-= n10[i+1]
        if i==0: n+=2*V
        newc.append(n)
    return V,newc,[nb[j] for j in range(k,0,-1)]

def jump_steps(counts, bits, V):
    """exact number of machine steps of V visits from a zone (the visit with the lowest 0 bit at separator i takes
    6*(n_0+..+n_{i-1}) + 4i + 11 steps); closed form, summed over the classes of x = B+t by trailing ones"""
    k=len(bits); B=0
    for b in bits: B=2*B+b
    n=lambda j: counts[k-j]          # n_j
    b=lambda j: bits[k-j]            # b_j, j=1..k
    total=0; C=n(0); D=0
    lo=B; hi=B+V-1
    for z in range(0,k):
        # C = C_{z+1} = sum_{j<=z} n_j - sum_{1<=j<=z}(1-b_j) ; D = D_{z+1} = sum_{m=1}^{z+1} floor(B/2^m)
        if z>=1: C+=n(z)-(1-b(z))
        D+=B>>(z+1)
        # x = y*2^(z+1) + 2^z - 1 in [lo,hi]
        r=(1<<z)-1; mod=1<<(z+1)
        ylo=(lo-r+mod-1)>>(z+1) if lo>r else 0
        yhi=(hi-r)>>(z+1) if hi>=r else -1
        if yhi<ylo: continue
        N=yhi-ylo+1; sy=(ylo+yhi)*N//2; sx=mod*sy+N*r
        total+=N*(4*z+15+6*(C+D+z-2*B))+6*(sx+sy)
    return total

def load(r, c):
    """set r's tape to canonical tokens c, head at the right end"""
    r.L=[]; r.R=[]
    w=(0,1,1)
    for it in c:
        if isinstance(it,int): r.L.append([w,it])
        else: r.L.extend(int(x) for x in it)

class Acc:
    def __init__(self, minjump=8):
        self.r=RL(M); self.visits=0; self.jumps=0; self.jumped=0; self.minjump=minjump; self.direct=0
    def advance(self, limit=None, step_limit=None):
        """one direct visit, or one jump (at most `limit` visits, ending at or before step `step_limit`)"""
        c=canon(self.r.segs())
        z=zone(c)
        if z:
            pre,counts,bits=z
            V,nc,nb=jump(counts,bits,limit)
            if step_limit is not None and V>=1 and self.r.steps+jump_steps(counts,bits,V)>step_limit:
                lo,hi=0,V
                while lo<hi:
                    mid=(lo+hi+1)//2
                    if self.r.steps+jump_steps(counts,bits,mid)<=step_limit: lo=mid
                    else: hi=mid-1
                V,nc,nb=jump(counts,bits,lo) if lo>=1 else (0,counts,bits)
            if V>=self.minjump:
                st=self.r.steps+jump_steps(counts,bits,V)
                load(self.r,unzone(pre,nc,nb)); self.r.state=0; self.r.steps=st
                self.visits+=V; self.jumps+=1; self.jumped+=V; return V
        self.r.next_visit(); self.visits+=1; self.direct+=1; return 1

def run_to_halt(progress=True, tlimit=None):
    """run from blank tape until the machine halts; returns the Acc (a.r.steps is the bbchallenge step count)"""
    import time
    a=Acc(); t0=time.time(); nxt=10
    try:
        while tlimit is None or time.time()-t0<tlimit:
            a.advance()
            if progress and a.visits>=nxt:
                c=canon(a.r.segs())
                print('visits ~1e%d steps ~1e%d jumps %d direct %d tokens %d t=%.0f | left end: %s'%(len(str(a.visits))-1,
                      len(str(a.r.steps))-1,a.jumps,a.direct,len(c),time.time()-t0,' '.join(map(str,c[:4])))); sys.stdout.flush()
                nxt=a.visits*10**6
        return a,False
    except Halt:
        return a,True

if __name__=='__main__':
    if len(sys.argv)==1:
        a,h=run_to_halt()
        print('HALT' if h else 'no halt')
        print('visits',a.visits); print('steps',a.r.steps); print('jumps',a.jumps,'direct visits',a.direct)
        print('final',a.r.show()[:400],'...')
        sys.exit(0)
    # check against the direct simulator
    N=int(sys.argv[1]); every=int(sys.argv[2])
    a=Acc(); d=RL(M); dv=0
    # align: first visit
    while a.visits<N:
        a.advance()
        while dv<a.visits: d.next_visit(); dv+=1
        if canon(d.segs())!=canon(a.r.segs()) or d.steps!=a.r.steps:
            print('MISMATCH at visit',a.visits); print(show(canon(d.segs()))[-300:]); print(show(canon(a.r.segs()))[-300:]); break
        if a.jumps%every==0: print(a.visits,a.jumps,a.direct,show(canon(a.r.segs()))[-150:])
    print('ok to visit',a.visits,'jumps',a.jumps,'jumped',a.jumped,'direct',a.direct)
