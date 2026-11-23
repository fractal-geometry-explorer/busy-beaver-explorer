"""Cycle-level walks with free residues of Z.

The counter run-downs are jumped with the Lean rules (lean/Counter.lean, CounterPhase.lean); every other phase is
run symbolically from the word D with Z = 4j+8+r, j = 2m+mbit, m symbolic, so the phase holds for every Z with that
residue mod 8. The residue of the next phase is then free again (Z' mod 8 depends on one more bit of m), so a walk
picks one bit per cycle-level step.

  python3 py/cycles.py explore 3000      breadth-first search over (word, Z mod 4); halting paths
  python3 py/cycles.py walk 400 2000     random walks (fair bits): halting step, prefix lengths every 100 steps
  python3 py/cycles.py realize           a concrete Z0 whose exact run from PS(D(2,0), Z0) follows a halting walk
"""
import sys, collections
import os, random
HERE=os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0,HERE)
sys.path.insert(0,os.path.join(HERE,'..','..','..','tools','py'))
from phaseiter import gaps, gap_text, compress, cnt
import phaseiter
def norm(g):
    out=[]
    for p,k in g:
        if k==0: continue
        if out and out[-1][0]==p: out[-1]=(p,out[-1][1]+k)
        else: out.append((p,k))
    return out
def g2t(g):
    toks=[1]
    for p,k in g:
        if k>1 and sum(p)+len(p)<=12:
            w=[]
            for x in p: w+=[0]*x+[1]
            toks.append(Rep(tuple(w),Lin(k))); continue
        assert k<=3 or sum(p)+len(p)<=12, (p,k)
        for _ in range(k):
            for x in p:
                if x>=4: toks+=[Rep((0,),Lin(x)),1]
                else: toks+=[0]*x+[1]
    return toks
from bbtools import symtm
from bbtools.symtm import Rep, Blank, Config, Lin
from bbtools.machine import Machine
MACH=Machine.parse("1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB---")

def is_ps(c):
    return c.state==4 and c.right==[Blank()] and c.left[-3:]==[1,0,0]

def phase_sym(g, r, mbit):
    """One phase from word gaps g with Z = 4j+8+r, j = 2m'+mbit (m' symbolic). Returns (g', Z' as Lin in m') or 'halt'."""
    # wall n = 2j+1 = 4m'+2mbit+1
    n = Lin(2*mbit+1, {'m':4})
    left=[Blank()]+g2t(g)+[0]*(4+r)+[1,0,0,0,Rep((1,0,0),n),0]
    c=Config(left,0,[Blank()])
    while True:
        try:
            c=symtm.run(MACH,c,is_ps,max_moves=200000,rotate=True)
        except symtm.Halted as e:
            return 'halt'
        body=c.left[1:-3]
        z=Lin(0); i=len(body)
        while i>0:
            t=body[i-1]
            if t==0: z=z+1
            elif isinstance(t,Rep) and set(t.word)=={0}: z=z+len(t.word)*t.n
            else: break
            i-=1
        d=body[:i]
        while d and (d[0]==0 or (isinstance(d[0],Rep) and set(d[0].word)=={0})): d=d[1:]
        if not z.is_const():
            # word must be concrete
            for t in d:
                if isinstance(t,Rep) and not t.n.is_const(): raise RuntimeError("symbolic word")
            return gaps(compress(d)), z
        symtm.step(MACH,c)

def shape_of(g):
    """C1/C3 counter with a>=1/a>=5 at the end? return (kind, pre, a, b) or None"""
    h=list(g); b=0
    if h and h[-1][0]==(2,): b=h[-1][1]; h=h[:-1]
    if not h: return None
    p,k=h[-1]
    if len(p)!=1: return None
    gsec=p[0]; h=h[:-1]+([(p,k-1)] if k>1 else [])
    if not h: return None
    p2,k2=h[-1]
    if len(p2)!=1: return None
    a=p2[0]; pre=h[:-1]+([(p2,k2-1)] if k2>1 else [])
    if gsec==1 and a>=1: return ('c1',pre,a,b)
    if gsec==3 and a>=5: return ('c3',pre,a,b)
    return None

def rundown(sh):
    kind,pre,a,b=sh
    if kind=='c1': return norm(pre+[((0,),1),((1,),1),((2,),b+a)])
    ae=(a-1)%4+1
    return norm(pre+[((ae,),1),((3,),1),((2,),b+(a-ae)//2)])

BIG=30
def key(g, zmod4):
    return (tuple((p if max(p)<BIG else tuple(('*',x%8) if x>=BIG else x for x in p), ('*',k%8) if k>=BIG else k) for p,k in g), zmod4)

def explore(g0, r0, maxstates=3000, verbose=False):
    seen={}; Q=collections.deque([(g0,r0,0,())]); halts=[]
    while Q and len(seen)<maxstates:
        g,r,d,path=Q.popleft()
        k=key(g,r)
        if k in seen: continue
        seen[k]=(d,path)
        sh=shape_of(g) if r%2==1 else None
        if sh:
            g=rundown(sh); r=3
        for mb in (0,1):
            try:
                res=phase_sym(g,r,mb)
            except Exception as e:
                print("ERR",gap_text(g,big=BIG),r,mb,e); continue
            step=(gap_text(g,big=BIG), r+4*mb)
            if res=='halt':
                halts.append(path+(step,)); continue
            g2,z2=res
            r2=z2.k%4
            Q.append((g2,r2,d+1,path+(step,)))
    return seen,halts

START=[((2,),1),((1,),1)]   # D(2,0) = 1 0 0 1 0 1, the word after the start; Z0 = 15

def walk(seed, depth):
    rnd=random.Random(seed); g=START; r=3; lens=[]; bits=[]
    for d in range(depth):
        sh=shape_of(g) if r%2==1 else None
        if sh: g=rundown(sh); r=3
        mb=rnd.randrange(2); bits.append(mb)
        res=phase_sym(g,r,mb)
        if res=='halt': return d, lens, bits
        g,z=res; r=z.k%4
        if d%100==99: lens.append(sum(len(p)*(1 if k<4 else 2) for p,k in g))
    return None, lens, bits

def free_phase(g, r):
    """Phases the walk jumps over: counter run-down (C1 a>=1 / C3 a>=5, Z odd) and the Z = 1 mod 4 keep phases."""
    if r%2==0: return False
    if shape_of(g): return True
    return r==1 and bool(g) and g[-1][0][-1]>=1

def run_exact(Z0, req, maxph=100000):
    """Exact phases (phaseiter.phase) from PS(D(2,0), Z0), checking the walk's bits on the way."""
    g=START; Z=Z0; k=0
    for t in range(maxph):
        if not free_phase(g, Z%4):
            if k>=len(req): return ('done',t)
            if (Z%8)//4!=req[k]: return ('mismatch',t,k)
            k+=1
        try:
            D2,Z2,_=phaseiter.phase(g2t(g),Z)
        except phaseiter.Halt as e:
            return ('halt',t,k,str(e))
        g,Z=gaps(D2),Z2
    return ('alive',)

def realize(depth=40, seeds=10000):
    req=None
    for seed in range(seeds):
        d,_,bits=walk(seed,depth)
        if d is not None: req=bits; break
    print("seed",seed,"halting walk of",len(req),"steps")
    x=15; M=random.Random(1).getrandbits(4000)|1
    for it in range(100000):
        Z0=x+(1<<3000)*M
        res=run_exact(Z0,req)
        if res[0]!='mismatch': break
        x+=1<<(res[1]+2)   # flips Z_t mod 8 by 4 and leaves the earlier phases alone
    print(res,"fixes:",it,"Z0 bits:",Z0.bit_length())
    return Z0, res

if __name__=='__main__':
    sys.set_int_max_str_digits(0)
    cmd=sys.argv[1] if len(sys.argv)>1 else 'explore'
    if cmd=='explore':
        seen,halts=explore(START,3,int(sys.argv[2]) if len(sys.argv)>2 else 3000)
        print(len(seen),"states;",len(halts),"halting paths")
        for h in halts[:5]:
            print("HALT via"," -> ".join(f"[{w} | Z%8={z}]" for w,z in h))
    elif cmd=='walk':
        N=int(sys.argv[2]); D=int(sys.argv[3])
        for s in range(N):
            d,l,_=walk(1000+s,D); print(s,d,l,flush=True)
    elif cmd=='realize':
        realize()
