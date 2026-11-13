"""Visit-accelerated simulator (prototype, Python ints).
visit: head in state SIN at q, cell q-1 == 0  ->  head in state SOUT at q-2, cell q-1 == 0, only cells >= q changed.
Rules are learned from raw simulation; cycles of rules at one position are count-compressed."""
import sys
from collections import defaultdict
sys.setrecursionlimit(1000000)
class Halt(Exception): pass
class Anom(Exception): pass
def parse(s):
    tm=[]
    for q in s.split('_'):
        row=[]
        for i in (0,3):
            t=q[i:i+3]
            row.append(None if t[0]=='-' else (int(t[0]), 1 if t[1]=='R' else -1, ord(t[2])-65))
        tm.append(row)
    return tm
class Sim:
    def __init__(s, tmstr, sin=2, sout=0, accel=True):
        s.tm=parse(tmstr); s.tape=defaultdict(int); s.sin=sin; s.sout=sout
        s.rules={}; s.ws=[]; s.accel=accel; s.steps=0; s.nsingle=0; s.halted=None
        s.cyc={}
    def win(s,p,w): return tuple(s.tape[p+i] for i in range(w))
    def raw(s,p,top=False,maxsteps=10**7):
        """one visit at p by raw simulation with interception; learns a rule when regular"""
        tape=s.tape; pos=p; st=s.sin if not top else 0
        tmax=(p-1 if top else p); subs=[]; init={}
        n=0
        while True:
            if st==s.sin and tape[pos-1]==0 and (top or pos>tmax):
                if top: s.on_round(pos)
                subs.append(pos); s.batch(pos,1); pos-=2; st=s.sout
                if not top and pos==p-2: raise Anom('sub returned outside')
                continue
            c=tape[pos]
            if pos not in init: init[pos]=c
            if pos>tmax: tmax=pos
            t=s.tm[st][c]
            if t is None:
                s.halted=(st,c,pos); raise Halt()
            tape[pos]=t[0]; pos+=t[1]; st=t[2]; n+=1; s.steps+=1
            if n>maxsteps and not top: raise Anom('raw visit too long')
            if not top and pos==p-2:
                if st!=s.sout or tape[p-1]!=0: raise Anom('bad return st=%d'%st)
                break
        if subs:
            q=subs[0]
            if any(x!=q for x in subs) or tmax>=q: return
            w=q-p
        else: w=tmax+1-p
        key=(w,tuple(init.get(p+i,None) for i in range(w)))
        if None in key[1]: return   # did not read all of window: skip (rare)
        s.rules[key]=(s.win(p,w),len(subs))
        if w not in s.ws: s.ws.append(w); s.ws.sort()
    def match(s,buf):
        for w in s.ws:
            r=s.rules.get((w,buf[:w]))
            if r: return w,r
        return None
    def findcycle(s,p):
        buf0=s.win(p,12)
        if buf0 in s.cyc: return s.cyc[buf0]
        buf=buf0; seq=[]; res=None
        for L in range(1,5):
            m=s.match(buf)
            if not m: break
            w,(out,k)=m
            buf=out+buf[w:]; seq.append((w,k,buf))
            sw=set(w for (w,k,b) in seq if k>0)
            if len(sw)>1: break
            W=max(w for (w,k,b) in seq)
            if sw and W>list(sw)[0]: continue
            if buf[:W]==buf0[:W]:
                res=(W,[(k,b[:W]) for (w,k,b) in seq]); break
        if res is not None: s.cyc[buf0]=res   # only cache positives (rules may be learned later)
        return res
    def batch(s,p,n):
        tape=s.tape
        while n>0:
            cy=s.findcycle(p) if s.accel else None
            if cy:
                W,seq=cy; L=len(seq); M=sum(k for k,b in seq)
                full,rem=divmod(n,L)
                tot=full*M+sum(k for k,b in seq[:rem])
                fin=seq[rem-1][1] if rem else seq[-1][1]
                for i in range(W): tape[p+i]=fin[i]
                p+=W; n=tot; continue
            s.nsingle+=1
            m=s.match(s.win(p,12)) if s.accel else None
            if m:
                w,(out,k)=m
                for i in range(w): tape[p+i]=out[i]
                if k: s.batch(p+w,k)
            else:
                s.raw(p)
            n-=1
    def on_round(s,pos): pass
    def run(s):
        try: s.raw(0,top=True)
        except Halt: pass
def direct(tmstr, nsteps):
    tm=parse(tmstr); tape=defaultdict(int); pos=0; st=0
    for i in range(nsteps):
        t=tm[st][tape[pos]]
        if t is None: return ('halt',i,tape,pos,st)
        tape[pos]=t[0]; pos+=t[1]; st=t[2]
    return ('run',nsteps,tape,pos,st)
if __name__=='__main__':
    tmstr=sys.argv[1]; R=int(sys.argv[2])
    class S(Sim):
        r=0
        def on_round(s,pos):
            s.r+=1
            if s.r>R: raise Halt()
    a=S(tmstr); a.run()
    print('rounds',a.r,'halted',a.halted,'rules',len(a.rules),'singles',a.nsingle)
    for k,v in sorted(a.rules.items()): print(k,v)
    lo=min(k for k,v in a.tape.items() if v) ; hi=max(k for k,v in a.tape.items() if v)
    print(lo,hi,''.join(str(a.tape[i]) for i in range(lo,min(hi,lo+300)+1)))
