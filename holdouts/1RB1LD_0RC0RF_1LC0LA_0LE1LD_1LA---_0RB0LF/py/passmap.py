"""Event map of 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF, and its checks against the machine.

States: ('L', blocks): the head, in state D, on the blank cell left of the blocks of 1s, single 0s between them;
        ('Ri', X, Q), ('Riii', X, Q): the head in state C past the right end; the blocks are X[0], X[1]-1, ..., then Q,
        separated by 00, with 00000 before Q in Riii.
step returns the next state, or None outside the checked domain (a small block in the wrong place; see the README).

usage: passmap.py check EVENTS_FILE   compare with the output of c/events.c
       passmap.py test ONESTEP [N]    compare with c/onestep.c on every list of 2 to 5 blocks below 10 and N random lists
       passmap.py off ONESTEP [N]     what the machine does from lists outside the domain
       passmap.py run EVENTS          iterate from L [7, 2]
       passmap.py lean [N]            compare `visit` with the definition proved in lean/EventMap.lean, same lists as test
"""
import itertools, random, subprocess, sys
BAD=(1,2,3,5)
def stepL(l):
    out=[]; i=0; cur=l[0]; n=len(l)
    if n==1: return None
    while True:
        j,r=divmod(cur,3)
        if i>0 and cur in BAD: return None
        if i==n-1:
            return ('Riii',out,cur-2) if cur-2 not in (0,1,2,3,5) else None
        if r==1:
            out.append(j+1); cur=l[i+1]+2*j; i+=1; continue
        if r==2:
            X=out+[j-1, l[i+1]+2*j+5]+l[i+2:]
            X[0]+=1
            if X[0]==0:
                return ('L',[X[1],X[2]+2]+X[3:]) if len(X)>=3 else ('L',[X[1],2])
            return ('L',X)
        if i+2<n:
            X=out+[j, l[i+1]+2*j, l[i+2]+2]+l[i+3:]
            X[0]+=1
            return ('L',X)
        return ('Ri',out+[j],l[i+1]+2*j+1)
def step(s):
    if s[0]=='L': return stepL(s[1])
    _,X,Q=s
    if s[0]=='Ri':
        return ('L',[X[0]+1]+X[1:]+[Q-1,2])
    if Q in (0,1,2,3,5): return None
    t,r=divmod(Q,3)
    if r==2: return ('Riii',X+[t+2],2*t)
    if r==1: return ('Ri',X+[t+1],2*t+3)
    return ('L',[X[0]+1]+X[1:]+[t-1,2*t+5])
def nextL(l):
    s=stepL(l)
    while s is not None and s[0]!='L': s=step(s)
    return s
def fromline(line):
    p=line.split(); k=p[1]; a=p[2:]
    if k=='L': return ('L',[int(x) for x in a[0::2]])
    if a[-1]!='g0': return ('R1',int(a[0]))
    blocks=[int(x) for x in a[0:-2:2]]; seps=a[1:-2:2]
    if len(blocks)==1: return ('R1',blocks[0])
    X=[blocks[0]]+[b+1 for b in blocks[1:-1]]
    return ('Riii' if seps[-1]=='z5' else 'Ri', X, blocks[-1])

def visit(l):
    """One left-end visit as a single rule: blocks past the end of the list count as 0 (inside the domain it equals nextL)."""
    out=[]; i=0; cur=l[0]
    get=lambda k: l[k] if k<len(l) else 0
    while True:
        j,r=divmod(cur,3)
        if r==1: out.append(j+1); cur=get(i+1)+2*j; i+=1; continue
        res=out+([j-1,get(i+1)+2*j+5]+l[i+2:] if r==2 else [j,get(i+1)+2*j,get(i+2)+2]+l[i+3:])
        break
    res[0]+=1
    if res[0]==0: res=[res[1],(res[2] if len(res)>2 else 0)+2]+res[3:]
    return res

def unstack(s,t):
    for a in s: t=[a+1]+t
    return t
def lean_later(s,cur,rest):
    """`later` of lean/EventMap.lean (without the fuel): s the finished blocks, nearest first."""
    hd=lambda l: l[0] if l else 0
    while True:
        j=cur//3
        if cur==4: s=[1]+s; cur=hd(rest)+2; rest=rest[1:]; continue
        if cur<6: return None
        if cur%3==1: s=[j]+s; cur=hd(rest)+2*j; rest=rest[1:]; continue
        if cur%3==2: return unstack(s,[j-1,hd(rest)+2*j+5]+rest[1:])
        return unstack([j-1]+s,[hd(rest)+2*j,hd(rest[1:])+2]+rest[2:])
def lean_visit(l):
    """`visit` of lean/EventMap.lean (without the fuel)."""
    hd=lambda l: l[0] if l else 0
    if not l or l[0]==0: return None
    l0,rest=l[0],l[1:]; j=l0//3
    if l0==1: return None if hd(rest)<2 else lean_later([1],hd(rest),rest[1:])
    if l0==2: return [hd(rest)+5,hd(rest[1:])+2]+rest[2:]
    if l0%3==1: return lean_later([j+1],hd(rest)+2*j,rest[1:])
    if l0%3==2: return [j,hd(rest)+2*j+5]+rest[1:]
    return unstack([j],[hd(rest)+2*j,hd(rest[1:])+2]+rest[2:])

def why(l):
    """Where the map leaves its domain from L(l): ('nested', value, is_last), ('Q', Q), ('single',) or None."""
    i=0; cur=l[0]; n=len(l)
    if n==1: return ('single',)
    while True:
        j,r=divmod(cur,3)
        if i>0 and cur in BAD: return ('nested',cur,i==n-1)
        if i==n-1: return ('Q',cur-2) if cur-2 in (0,1,2,3,5) else None
        if r==1: cur=l[i+1]+2*j; i+=1; continue
        return None

def lists(n,seed):
    random.seed(seed); t=[]
    for k in range(2,6):
        t+=[list(l) for l in itertools.product(range(1,10),repeat=k)]
    for _ in range(n):
        t.append([random.choice([random.randint(1,12),random.randint(1,80)]) for _ in range(random.randint(2,6))])
    return t

def simulate(onestep,tests,limit):
    inp=''.join(' '.join(map(str,l))+'\n' for l in tests)
    return subprocess.run([onestep,str(limit)],input=inp,capture_output=True,text=True).stdout.split('\n')

if __name__=='__main__':
    cmd=sys.argv[1]
    if cmd=='check':
        ev=[fromline(x) for x in open(sys.argv[2]) if ' L' in x or ' R' in x]
        ok=bad=unk=0
        for k,(a,b) in enumerate(zip(ev,ev[1:])):
            if a[0]=='R1': continue
            p=step(a)
            if b[0]=='R1': b=ev[k+2]          # a single block at the right end: the map goes straight to the next L
            if p is None: unk+=1; print('outside the domain',a,'->',b)
            elif p==b: ok+=1
            else: bad+=1; print('MISMATCH',a,'->',b,'map says',p)
        print(ok,'events agree,',bad,'disagree,',unk,'outside the domain')
    elif cmd=='test':
        tests=lists(int(sys.argv[3]) if len(sys.argv)>3 else 60000,5)
        ok=out=bad=0
        for l,o in zip(tests,simulate(sys.argv[2],tests,30000000)):
            p=nextL(l)
            if p is None: out+=1; continue
            a=o.split()
            if a[0]=='L' and all(x=='z1' for x in a[2:-1:2]) and a[-1]=='d0' and [int(x) for x in a[1:-1:2]]==p[1]==visit(l): ok+=1
            else: bad+=1; print('MISMATCH',l,o,p)
        print(len(tests),'lists:',ok,'agree,',bad,'disagree,',out,'outside the domain')
    elif cmd=='off':
        tests=[t for t in lists(int(sys.argv[3]) if len(sys.argv)>3 else 100000,11) if why(t)]
        tab={}
        for l,o in zip(tests,simulate(sys.argv[2],tests,300000000)):
            k=(why(l),o.split()[0]); tab[k]=tab.get(k,0)+1
        for k in sorted(tab,key=str): print(k,tab[k])
    elif cmd=='lean':
        tests=lists(int(sys.argv[2]) if len(sys.argv)>2 else 60000,5)
        ok=bad=out=more=0
        for l in tests:
            p=nextL(l); q=lean_visit(l)
            if p is None:
                out+=1; more+=q is not None
            elif q==p[1]==visit(l): ok+=1
            else: bad+=1; print('MISMATCH',l,p,q)
        print(len(tests),'lists:',ok,'agree,',bad,'disagree,',out,'outside the checked domain, of which the Lean map answers',more)
    elif cmd=='run':
        s=('L',[7,2]); n=int(float(sys.argv[2])); k=1
        while k<n:
            t=step(s)
            if t is None: print('left the domain at event',k,s); break
            s=t; k+=1
        print('event',k,s)
