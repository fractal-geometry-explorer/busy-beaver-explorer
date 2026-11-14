"""The simulator of lean/Sim.lean and lean/Run.lean, in Python, with step counts.

The same algorithm as the Lean definitions that `lean/Halt.lean` evaluates (`mstep`: one transition, a run crossed
when one or two copies of its word are crossed in the same state, or one copy unpacked; `fold`; `canonL`;
`parseZone`; `toN`; `chooseV`; `after`), written independently of rl.py and accel.py.  Lean proves that the run
halts but does not count steps; this twin counts them (a jump of V visits with accel.jump_steps, checked against
odo.py at every jump) and prints the number of rounds of each kind.

    python3 leansim.py        about 3 minutes; prints the halting step count
"""
import sys,time,os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from accel import jump_steps, M
import odo
from bbtools.machine import Machine
tab=Machine.parse(M).table
W=(1,1,0)
class Halt(Exception): pass
cache={}
def segrun(dirR, st, w):
    key=(dirR,st,w); r=cache.get(key)
    if r is not None: return r
    l=[]; rr=list(w); q=st; n=0; res=False
    for fuel in range(200):
        if not rr:
            res=(tuple(l),q,n); break     # l is nearest-first already (last written first)
        b=rr[0]; t=tab[q][b]
        if t is None: break
        x,mv,q2=t; fwd=(mv==1)==dirR
        if fwd: l.insert(0,x); rr.pop(0); q=q2
        else:
            if not l: break
            y=l.pop(0); rr[0:1]=[y,x]; q=q2
        n+=1
    cache[key]=res; return res
PARSE_MIN=7; MU=6
def toN(n0,lv):
    b1,n1=lv[0]; ps=[(b1,n0-int(b1))]; b,n=b1,n1
    for b2,n2 in lv[1:]:
        ps.append((b2,n+int(b)-int(b2))); b,n=b2,n2
    return ps,n+int(b)
def physP(ps,top):
    out=[]
    for j in range(len(ps)):
        b=ps[j][0]
        if j+1<len(ps): out.append((b,ps[j+1][1]+int(ps[j+1][0])-int(b)))
        else: out.append((b,top-int(b)))
    return out
def n0of(ps): return ps[0][1]+int(ps[0][0])
def addV(V,ps):
    out=[]
    for b,M in ps:
        b=int(b); out.append(((V+b)%2==1, max(0,M-(V+1-b)//2))); V=(V+b)//2
    return out
def ovf(V,ps):
    for b,M in ps: V=(V+int(b))//2
    return V
def after(V,ps): return addV(V,[(ps[0][0],ps[0][1]+2*V)]+ps[1:])
def goodN(ps,top): return len(ps)>=1 and all(M>=2 for _,M in ps[1:]) and top>=2
def chooseV(ps):
    pow_=1; blow=0; lim=None
    for j,(b,M) in enumerate(ps):
        b=int(b)
        if j>=1:
            if M<MU: return 0
            l=((2*(M-MU)+b+1)*pow_)-1-blow
            if lim is None or l<lim: lim=l
        blow+=b*pow_; pow_*=2
    v0=pow_-1-blow
    return v0 if lim is None or v0<lim else lim
class Sim:
    def __init__(self):
        self.dirR=True; self.front=[]; self.back=[]; self.st=0; self.steps=0
        self.nbit=self.ncross=self.nunpack=self.njump=self.nvisit=self.ndouble=0
    def pushBit(self,stk,b):
        stk.append(b)
        n=len(stk)
        if n>=4 and isinstance(stk[-4],list) and stk[-1].__class__ is int and stk[-2].__class__ is int and stk[-3].__class__ is int:
            if stk[-4][0]==(stk[-1],stk[-2],stk[-3]):
                del stk[-3:]; stk[-1][1]+=1; return
        if n>=6:
            for q in range(1,7):
                if stk[-q].__class__ is not int: return
            w=(stk[-1],stk[-2],stk[-3])
            if w==(stk[-4],stk[-5],stk[-6]) and not (w[0]==w[1]==w[2]):
                del stk[-6:]
                if stk and isinstance(stk[-1],list) and stk[-1][0]==w: stk[-1][1]+=2
                else: stk.append([w,2])
    def pushRun(self,stk,w,n):
        if stk and isinstance(stk[-1],list) and stk[-1][0]==w: stk[-1][1]+=n
        else: stk.append([w,n])
    def step(self):
        f=self.front
        if f and isinstance(f[-1],list):
            w,n=f[-1]
            r=segrun(self.dirR,self.st,w)
            if r and r[1]==self.st:
                f.pop(); self.pushRun(self.back,r[0],n); self.steps+=n*r[2]; self.ncross+=1; return
            if n>=2 and len(w)==3:
                r=segrun(self.dirR,self.st,w+w)
                if r and r[1]==self.st:
                    h=n//2
                    if n&1: f[-1][1]=1
                    else: f.pop()
                    v=r[0]
                    if v[:3]==v[3:]: self.pushRun(self.back,v[:3],2*h)
                    else: self.pushRun(self.back,v,h)
                    self.steps+=h*r[2]; self.ndouble+=1; return
            # unpack
            if n==1: f.pop()
            else: f[-1][1]=n-1
            f.extend(reversed(w)); self.nunpack+=1; return
        b=f.pop() if f else 0
        t=tab[self.st][b]; self.steps+=1; self.nbit+=1
        if t is None: raise Halt()
        x,mv,q2=t; fwd=(mv==1)==self.dirR; self.st=q2
        if fwd: self.pushBit(self.back,x)
        else:
            self.pushBit(f,x)
            self.front,self.back=self.back,f; self.dirR=not self.dirR
    # canonical form of the left side
    def canon(self):
        out=[]
        def cbit(b):
            out.append(b); n=len(out)
            if n>=4 and isinstance(out[-4],list) and out[-4][0]==W and out[-1]==1 and out[-2]==1 and out[-3]==0:
                del out[-3:]; out[-1][1]+=1; return
            if n>=6 and out[-6:]==[0,1,1,0,1,1]:
                del out[-6:]
                if out and isinstance(out[-1],list) and out[-1][0]==W: out[-1][1]+=2
                else: out.append([W,2])
        def crun(n):
            if n==0: return
            while len(out)>=3 and out[-1]==1 and out[-2]==1 and out[-3]==0: del out[-3:]; n+=1
            if out and isinstance(out[-1],list) and out[-1][0]==W: out[-1][1]+=n
            else: out.append([W,n])
        for it in self.back:
            if isinstance(it,list):
                w,n=it
                if w==W: crun(n)
                elif w==(0,1,1): cbit(1); cbit(1); crun(n-1); cbit(0)
                elif w==(1,0,1): cbit(1); crun(n-1); cbit(0); cbit(1)
                else: out.append([w,n])
            else: cbit(it)
        return out
    def try_jump(self):
        c=self.canon(); n=len(c)
        # parseZone on the canonical stack, nearest first
        if n<2 or c[-1]!=0 or not isinstance(c[-2],list) or c[-2][0]!=W: return False
        n0=c[-2][1]; i=n-3; lv=[]
        while i>=2 and c[i]==1 and c[i-1].__class__ is int and isinstance(c[i-2],list) and c[i-2][0]==W and c[i-2][1]>=PARSE_MIN:
            lv.append((c[i-1]==0,c[i-2][1])); i-=3
        if not lv: return False
        rest=c[:i+1]
        ps,top=toN(n0,lv)
        V=chooseV(ps)
        ps2=after(V,ps)
        if not (V>=8 and ovf(V,ps)==0 and goodN(ps2,top) and n0of(ps)==n0 and physP(ps,top)==lv): return False
        counts=[x[1] for x in reversed(lv)]+[n0]; bits=[1 if x[0] else 0 for x in reversed(lv)]
        self.steps+=jump_steps(counts,bits,V)
        n0b=n0of(ps2); lv2=physP(ps2,top)
        # cross-check with the Python accelerator's closed form
        nc,nb,st2=odo.run(counts,bits,V); assert st2==jump_steps(counts,bits,V) and nc==[x[1] for x in reversed(lv2)]+[n0b] and nb==[1 if x[0] else 0 for x in reversed(lv2)]
        for b,nn in reversed(lv2):
            rest.append([W,nn]); rest.append(0 if b else 1); rest.append(1)
        rest.append([W,n0b]); rest.append(0)
        self.back=rest; self.njump+=1
        return True
    def run(self,tlimit):
        t0=time.time(); k=0
        try:
            while True:
                if self.dirR and not self.front and self.st==0:
                    self.nvisit+=1
                    self.try_jump()
                    if self.nvisit%20000==0:
                        print('direct+jump events',self.nvisit,'jumps',self.njump,'steps ~1e%d'%(len(str(self.steps))-1),'ops',self.nbit,self.ncross,self.nunpack,'len',len(self.back),'t=%.0f'%(time.time()-t0)); sys.stdout.flush()
                        if time.time()-t0>tlimit: return False
                self.step()
        except Halt:
            return True
if __name__=='__main__':
    s=Sim(); h=s.run(float(sys.argv[1]) if len(sys.argv)>1 else 1e9)
    print('HALT' if h else 'no halt','steps',s.steps); print('visits handled',s.nvisit,'jumps',s.njump,'bit steps',s.nbit,'crossings',s.ncross,'unpacks',s.nunpack,'doubles',s.ndouble)
