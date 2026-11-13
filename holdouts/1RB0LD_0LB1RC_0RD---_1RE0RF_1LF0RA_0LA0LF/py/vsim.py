"""Visit-level exact simulator for the (0001)-background family.
Sample point: head at the leftmost cell in state Q.  The tape right of it is a list of items: ('W', g) a run of g
copies of 0001, or a literal string.  A visit (until the head is again at the leftmost cell in state Q) is run
concretely on a compressed copy: runs longer than CMAX keep CMAX copies, the rest are spliced back into the run that
holds the splice point afterwards.  The head crosses a splice point both ways or not at all; crossing costs 12 steps
per W removed (checked against the direct simulator)."""
import sys
from tm import parse
CMAX = 16
H = CMAX // 2
def tokenize(cells):
    out=[];i=0;n=len(cells);lit=[];w=0
    while i<n:
        if cells.startswith('0001',i):
            if lit: out.append(''.join(lit)); lit=[]
            w+=1;i+=4;continue
        if w: out.append(('W',w)); w=0
        lit.append(cells[i]); i+=1
    if w: out.append(('W',w))
    if lit: out.append(''.join(lit))
    return out
def cstr(items):
    return ' '.join('W%d'%it[1] if isinstance(it,tuple) else it for it in items)
class VSim:
    def __init__(s, M, Q, cells, steps=0, A=None):
        s.T=parse(M); s.Q=ord(Q)-65; s.items=tokenize(cells.rstrip('0')); s.steps=steps; s.memo={}; s.visits=0
        s.A=None if A is None else ord(A)-65
        s.events=[]
        s.wcost=12
        a=s.small(tuple(['00',('W',20),'0011',('W',5),'001']),True)[2]
        b=s.small(tuple(['00',('W',21),'0011',('W',5),'001']),True)[2]
        s.wcost=b-a
    def visit(s):
        n=len(s.items); j=1
        while True:
            while j<n and not isinstance(s.items[j-1],tuple): j+=1
            j=min(j,n); full=(j==n)
            key=tuple((('W',min(it[1],CMAX)) if isinstance(it,tuple) else it) for it in s.items[:j])
            r=s.memo.get((key,full))
            if r is None:
                r=s.small(key,full); s.memo[(key,full)]=r
            if r!='more': break
            j=j*2
        if r[0]=='halt':
            s.steps+=r[1]; return r
        _,out,nsteps,maxp,lo,ev=r
        out=list(out)
        # splice points (cell index in compressed tape) and the extra copies
        sp=[];pos=0
        for it in s.items[:j]:
            if isinstance(it,tuple):
                gc=min(it[1],CMAX)
                if it[1]>CMAX: sp.append((pos+4*H,it[1]-CMAX))
                pos+=4*gc
            else: pos+=len(it)
        extra=0
        if sp:
            # item start offsets in out (relative to compressed tape index: out starts at lo)
            starts=[];q=lo
            for it in out:
                ln=4*it[1] if isinstance(it,tuple) else len(it)
                starts.append((q,q+ln)); q+=ln
            add={}
            for (c,ex) in sp:
                k=next((k for k,(a,b) in enumerate(starts) if a<=c<b or (c==b and k==len(out)-1)),None)
                if k is None or not isinstance(out[k],tuple): raise RuntimeError('splice %s'%cstr(key))
                if c-starts[k][0] < 4 and c != starts[k][0]: pass
                add[k]=add.get(k,0)+ex
                if maxp>=c: extra+=s.wcost*ex
            for k,ex in add.items(): out[k]=('W',out[k][1]+ex)
        rest=s.items[j:]
        if rest and out and isinstance(out[-1],tuple) and isinstance(rest[0],tuple): raise RuntimeError('junction')
        s.items=out+list(rest)
        if ev: s.events.append((s.steps+ev[0],ev[1],ev[2],s.visits))
        s.steps+=nsteps+extra; s.visits+=1
        return 'ok'
    def small(s,key,full):
        cells=''.join('0001'*it[1] if isinstance(it,tuple) else it for it in key)
        n=len(cells); PAD=200
        tape=bytearray(PAD)+bytearray(int(c) for c in cells)+bytearray(PAD if full else 0)
        L=len(tape); p=PAD; st=s.Q; lo=p; steps=0; maxp=p; ev=None; T=s.T; A=s.A
        lim=L if full else L-4*H
        while True:
            if p>=lim: return 'more'
            b=tape[p]
            if A is not None and st==A and b==0 and tape[p+1]==1:
                ev=(steps,p-PAD,''.join(map(str,tape[p:p+4])))
            t=T[(st,b)]
            if t is None: return ('halt',steps+1,p-PAD)
            tape[p]=t[0]; p+=t[1]; st=t[2]; steps+=1
            if p<0: raise RuntimeError('left pad')
            if p>maxp: maxp=p
            if p<=lo:
                lo=p
                if st==s.Q: break
        if full:
            hi=L-1
            while hi>lo and tape[hi]==0: hi-=1
        else: hi=L-1
        newcells=''.join(map(str,tape[lo:hi+1]))
        return ('ok',tuple(tokenize(newcells)),steps,maxp-PAD,lo-PAD,ev)
def bootstrap(M,Q,minsteps=1000):
    T=parse(M); tape={}; p=0; st=0; n=0; lo=0; q=ord(Q)-65
    while True:
        if st==q and p==lo and n>minsteps: break
        b=tape.get(p,0); t=T[(st,b)]; tape[p]=t[0]; p+=t[1]; st=t[2]; n+=1; lo=min(lo,p)
    hi=max(tape); return ''.join(str(tape.get(i,0)) for i in range(lo,hi+1)),n
if __name__=='__main__':
    M=sys.argv[1]; Q=sys.argv[2]; N=float(sys.argv[3]); A=sys.argv[4] if len(sys.argv)>4 else None
    every=int(sys.argv[5]) if len(sys.argv)>5 else 0
    cells,n=bootstrap(M,Q)
    v=VSim(M,Q,cells,n,A)
    while v.steps<N:
        r=v.visit()
        if r!='ok': print('HALT',r,v.steps); break
        if every and v.visits%every==0: print(v.steps,'|'+cstr(v.items),flush=True)
    print('end',v.steps,v.visits,len(v.memo),cstr(v.items)[:3000])
    for e in v.events: print('event',e)
