"""Generalized hybrid simulator for the family 1RB?RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_X---.

A regular Q event is the tape  W 0 1^m B>0 R  with
  W = [w1, w2, ..., wr] (r >= 2): blocks of 1s separated by single 0s, blank to the left, w2..wr odd;
  m = 3a;  R = 0^(3p2-1) 1 ... 0^(3ps-1) 1  (aligned parts)  then optionally 0^g 1 Rest with g % 3 != 2.
State: (W, k, q, g, Rest): k = a + p2 + ... + ps units, q the counter value (bits = part boundaries),
g = the first misaligned gap (None: blank), Rest the gaps after it.
Rules (checked against direct simulation): from one Q event to the next
  W -> phi(phi(W)),  phi([.., x, b]) = [.., x+2] + [1]*((b-1)/2), cost 4b+7 each,
  q -> q+1; at q = 2^(k-1): k -> k+1, q -> 0, and g -> g-3 (needs g >= 3 or blank),
  steps = cost + cost' + m + m' - 6.
Otherwise (W a single block before a phi, or an overflow with g < 3) the step is simulated directly (trans.c)
from the last Q event until the next regular Q event.
"""
import sys, subprocess, os, tempfile
HERE=os.path.dirname(os.path.abspath(__file__))
FAMILY=["1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---", "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0RB---",
        "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC---", "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RA---",
        "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RC---", "1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RE---"]
BIN=os.path.join(tempfile.gettempdir(), "g12_family1_bin")

def binary(name):
    """compile ../c/NAME.c once into a temporary directory"""
    os.makedirs(BIN, exist_ok=True)
    exe=os.path.join(BIN, name); src=os.path.join(HERE, "..", "c", name+".c")
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        subprocess.run(["gcc", "-O2", "-o", exe, src], check=True)
    return exe

def comp(k,q):
    parts=[]; last=0
    x=q; c=1
    while x:
        if x&1: parts.append(c-last); last=c
        x>>=1; c+=1
    parts.append(k-last)
    return parts[0], parts[1:]
def fromcomp(a,P):
    k=a+sum(P); q=0; c=a
    for p in P:
        q|=1<<(c-1); c+=p
    return k,q

class Anomaly(Exception): pass
def adv(W,j):
    cost=0
    while j>0:
        if len(W)<2: raise Anomaly(j)
        b=W[-1]; i=(b-1)//2
        if j>=(1<<i):
            W.pop(); W[-1]+=b+1; j-=1<<i; cost+=19*(1<<i)-8
        else:
            W.pop(); W[-1]+=2; W.extend([1]*i); j-=1; cost+=4*b+7
    return cost
def Nphi(W):
    tot=0; s=-1
    for b in reversed(W[1:]):
        s+=b+1
        tot+=1<<((s-1)//2)
    return tot
def popc(x): return bin(x).count('1')
def sumA(k,q0,q1):
    s=0
    if q0==0 and q1>0: s+=k; q0=1
    if q1<=q0: return s
    F=lambda Q: 2*Q-popc(Q)
    return s+F(q1-1)-F(q0-1)
def msum(k,q,J,g):
    s=0
    while J>0:
        rem=(1<<(k-1))-q
        t=min(J,rem)
        s+=3*sumA(k,q,q+t)
        J-=t; q+=t
        if q==(1<<(k-1)):
            k+=1; q=0
            if g is not None:
                g-=3; assert g>=0
    return s,k,q,g
def jcoll(k,q,g):
    """number of events that can be taken before an overflow with g<3 (None: unlimited)"""
    if g is None: return None
    J=0
    while True:
        J+=(1<<(k-1))-q
        if g<3: return J-1   # stop at the last Q event before the colliding overflow
        g-=3; k+=1; q=0
def jump(st,J):
    W,k,q,g,rest,n=st
    a0=comp(k,q)[0]
    c=adv(W,2*J)
    s1,k2,q2,g2=msum(k,q,J,g)
    a1=comp(k2,q2)[0]
    n+=c+s1+(s1-3*a0+3*a1)-6*J
    return (W,k2,q2,g2,rest,n)
def tape_of(W,k,q,g,rest):
    a,P=comp(k,q)
    s=[]
    for i,b in enumerate(W):
        if i: s.append('0')
        s.append('1'*b)
    s.append('0'); s.append('1'*(3*a)); head=sum(map(len,s))
    s.append('0')
    for p in P: s.append('0'*(3*p-1)+'1')
    if g is not None:
        s.append('0'*g+'1')
        for x in rest: s.append('0'*x+'1')
    return ''.join(s), head
def parse_q(W,m,R):
    a=m//3; P=[]; i=0
    while i<len(R) and R[i]%3==2: P.append((R[i]+1)//3); i+=1
    k,q=fromcomp(a,P)
    if i<len(R): g=R[i]; rest=R[i+1:]
    else: g=None; rest=[]
    return k,q,g,rest
def transient(machine,st,maxsteps):
    W,k,q,g,rest,n=st
    tape,head=tape_of(W,k,q,g,rest)
    inp=f"{machine} {maxsteps} {head} B {tape}"
    out=subprocess.run([binary('trans')],input=inp,capture_output=True,text=True).stdout
    lines=out.strip().split('\n')
    F=[(n+int(l.split()[1]),l.split()[-1][4:]) for l in lines if l.startswith('F ')]
    last=[l for l in lines if not l.startswith('F ')]
    if last and last[0].startswith('HALT'): return ('HALT',n+int(last[0].split()[1]),F)
    if not last or not last[0].startswith('Q'): return ('STOP',out,F)
    _,dn,fc,m=last[0].split(); dn=int(dn); m=int(m)
    W=[int(x) for x in last[1].split()[1:]]
    R=[int(x) for x in last[2].split()[1:]]
    k,q,g,rest=parse_q(W,m,R)
    return ('OK',(W,k,q,g,rest,n+dn),F,dn)

def from_blank(machine, maxsteps=10**8):
    """direct simulation from blank tape to the first regular Q event"""
    out=subprocess.run([binary('trans')],input=f"{machine} {maxsteps} 0 A ",capture_output=True,text=True).stdout
    lines=[l for l in out.strip().split('\n') if not l.startswith('F ')]
    assert lines[0].startswith('Q'), out
    _,dn,fc,m=lines[0].split()
    W=[int(x) for x in lines[1].split()[1:]]; R=[int(x) for x in lines[2].split()[1:]]
    k,q,g,rest=parse_q(W,int(m),R)
    return (W,k,q,g,rest,int(dn))

def run(machine, st, nevents, log=print, maxtrans=10**10, verbose=True):
    """run through nevents transients"""
    hist=[]
    for e in range(nevents):
        W,k,q,g,rest,n=st
        Ja=Nphi(W)//2; Jc=jcoll(k,q,g)
        J=Ja if Jc is None else min(Ja,Jc)
        kind='anomaly' if J==Ja else 'collision'
        st=jump(st,J)
        r=transient(machine,st,maxtrans)
        if r[0]!='OK':
            log(f"event {e}: {kind} at n={st[5]}: transient {r[0]} {r[1] if r[0]=='HALT' else ''}")
            return r, hist
        _,st2,F,dn=r
        W2,k2,q2,g2,rest2,n2=st2
        w=sum(W2)+len(W2)-1
        info=dict(e=e,kind=kind,n=st[5],dn=dn,F=len(F),width=w,len=len(W2),k=k2,g=g2,nrest=len(rest2))
        hist.append((info,F))
        if verbose: log(f"{e} {kind:9s} n={n2 if n2<10**30 else "~2^"+str(n2.bit_length()-1)} F at {[f[0] for f in F][:3] if n2<10**30 else "-"} dn={dn} F={len(F)} -> width={w} k={k2} g={g2} rest={len(rest2)}")
        st=st2
    return ('OK',st), hist

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser(description="accelerated run from blank tape, through N transients")
    ap.add_argument("machine"); ap.add_argument("n", type=int)
    a=ap.parse_args()
    st=from_blank(a.machine)
    print(f"first regular Q event at step {st[5]}: W={st[0]} k={st[1]} q={st[2]} g={st[3]} rest={st[4]}")
    r,hist=run(a.machine, st, a.n)
    print(r[0], "final step count has", (r[1][5].bit_length() if r[0]=='OK' else '?'), "bits")
