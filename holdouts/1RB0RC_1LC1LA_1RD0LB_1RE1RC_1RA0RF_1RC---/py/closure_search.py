"""A closure search that FAILED, kept as a record: n-gram closure of the block-level law (py/law.py).

The abstract state is the exact neighbourhood of the head (state, open block, gap, the n-1 nearest blocks and gaps)
plus two global sets: the n-grams of consecutive blocks and of consecutive gaps seen so far.  A pop from a stack is
answered with every token the n-gram set allows.  Tokens carry their cumulative position modulo ML (blocks) and MG
(gaps), and optionally the parity of the absolute cell.  If the closure were finite and never reached state F on a
gap 0, the machine would be proved not to halt.  It reaches the halt for n = 2 and 3 with every labelling tried
(n = 4 exceeds 300,000 abstract states); the last lines printed are the abstract path to the halt.

usage: python3 holdouts/MACHINE/py/closure_search.py N K [MAXSTATES] [USE_PARITY] [ML] [MG]
  K = the start (1 for this machine, 2 and 0 for its twins)
"""
import sys
from collections import deque
INF=10**9; BOT=-1
N=int(sys.argv[1]); K=int(sys.argv[2]); MAXS=int(sys.argv[3]) if len(sys.argv)>3 else 2000000
USEPAR=int(sys.argv[4]) if len(sys.argv)>4 else 1
NL={}; NG={}   # (label, window(n-1)) -> set of next-deeper tokens
users={'L':{}, 'G':{}}  # key -> set of states that looked it up (to re-run when the set grows)
states=set(); work=deque()
class Fail(Exception): pass
def lab(x): return x%2 if USEPAR else 0
parent={}
cur=[None]
def add_state(s):
    if s not in states:
        parent[s]=cur[0]
        if len(states)>=MAXS: raise Fail("too many states")
        states.add(s); work.append(s)
def lookup(which,key,s):
    users[which].setdefault(key,set()).add(s)
    return list((NL if which=='L' else NG).get(key,()))
def addgram(which,label,gram):
    D=NL if which=='L' else NG
    key=(label,gram[:-1]); t=gram[-1]
    S=D.setdefault(key,set())
    if t not in S:
        S.add(t)
        for u in users[which].get(key,()): work.append(u)
# state: (q,o,x,p,wL,wG): p = head parity; x = g (R-mode) or z (B)
ML=int(sys.argv[5]) if len(sys.argv)>5 else 6
MG=int(sys.argv[6]) if len(sys.argv)>6 else 6
def cumL(top): return 0 if top==BOT else (top[1]+top[0]+1)%ML
def popL(s,wL,e0):
    if wL[0]==BOT: return [(0,wL)]
    return [(wL[0][0], wL[1:]+(t,)) for t in lookup('L',(lab(e0),wL),s)]
def pushL(wL,b,e):
    gram=((b,cumL(wL[0])),)+wL; addgram('L',lab(e),gram); return gram[:-1]
def dfa(top):
    if top==BOT: return 0
    g,st=top
    return (st+g+1)%MG
def popG(s,wG,s0):
    if wG[0]==BOT: return [(INF,wG)]
    return [(wG[0][0], wG[1:]+(t,)) for t in lookup('G',(lab(s0),wG),s)]
def pushG(wG,g,s0):
    if g>=INF: return wG
    gram=((g,dfa(wG[0])),)+wG; addgram('G',lab(s0),gram); return gram[:-1]
def succ(s):
    q,o,x,p,wL,wG=s; out=[]
    if o>80: raise Fail("o unbounded")
    if q=='B':
        z=x
        # geometry: o>=1: head p on last 1 of open block; e0 = p-o. o=0: head on separator of top closed block: e0=p.
        e0=p-o
        # G: zeros p+1..p+z, one at p+z+1, G[0] starts at p+z+2
        if o>=3:
            # cells p-2..p -> 0 1 0 ; new gap (z+1) starts at p (zeros p..p+z), the new 1 at p-1; then z=1: zero at p-2.. wait
            # after: head p-3; cell p-2 = 0, p-1 = 1, p = 0. gap pushed: zeros p..p+z -> starts at p, length z+1. new z = 1 (cell p-2)
            wG2=pushG(wG,z+1 if z<INF else INF,p)
            out.append(('B',o-3,1,p-3,wL,wG2))
        elif o==2:
            for b,wL2 in popL(s,wL,e0): out.append(('D',b+3,z,p+1,wL2,wG))
        elif o==1:
            for b,wL2 in popL(s,wL,e0):
                if b>=1:
                    wG2=pushG(wG,z+1 if z<INF else INF,p)
                    out.append(('B',b-1,1,p-3,wL2,wG2))
                else:
                    # popped 0-block: its separator at e0=p-1; next block's separator at p-2
                    for b2,wL3 in popL(s,wL2,p-2): out.append(('D',b2+3,z,p+1,wL3,wG))
        else:
            for b,wL2 in popL(s,wL,e0):
                if b>=1:
                    # head cell p becomes 1; gap pushed: zeros p+1..p+z : starts p+1, length z; new z=1 (cell p-1 = 0)
                    wG2=pushG(wG,z,p+1)
                    out.append(('B',b-1,1,p-2,wL2,wG2))
                else:
                    for b2,wL3 in popL(s,wL2,p-1): out.append(('C',b2+2,z,p+1,wL3,wG))
        return out
    g=x
    # R-mode: head p at start of current gap; G[0] starts at p+g+1. top closed separator at p-o-1.
    def turn(k):
        # wrote k ones at p..p+k-1; B at p+k
        if g==k:
            for g2,wG2 in popG(s,wG,p+g+1): out.append(('B',o+k+1,g2,p+k,wL,wG2))
        else:
            wL2=pushL(wL,o+k,p+k)
            out.append(('B',0,g-k-1 if g<INF else INF,p+k,wL2,wG))
    if q=='C':
        if g==0:
            for g2,wG2 in popG(s,wG,p+1): out.append(('B',o,1+g2 if g2<INF else INF,p-1,wL,wG2))
        elif g==1:
            for g2,wG2 in popG(s,wG,p+2): out.append(('C',o+2,g2,p+2,wL,wG2))
        elif g==2:
            wL2=pushL(wL,o+2,p+2)
            for g2,wG2 in popG(s,wG,p+3): out.append(('F',0,g2,p+3,wL2,wG2))
        elif g==3:
            wL2=pushL(wL,o+3,p+3)
            for g2,wG2 in popG(s,wG,p+4): out.append(('C',0,g2,p+4,wL2,wG2))
        else: turn(4)
    elif q=='F':
        if g==0: raise Fail("halt reachable in the abstraction")
        out.append(('C',o+1,g-1 if g<INF else INF,p+1,wL,wG))
    else:
        if g==0:
            for g2,wG2 in popG(s,wG,p+1): out.append(('C',o+1,g2,p+1,wL,wG2))
        elif g==1:
            wL2=pushL(wL,o+1,p+1)
            for g2,wG2 in popG(s,wG,p+2): out.append(('F',0,g2,p+2,wL2,wG2))
        elif g==2:
            wL2=pushL(wL,o+2,p+2)
            for g2,wG2 in popG(s,wG,p+3): out.append(('C',0,g2,p+3,wL2,wG2))
        else: turn(3)
    return out
def norm(s):
    q,o,x,p,wL,wG=s
    return (q,o,x,p%2 if USEPAR else 0,wL,wG)
bot=(BOT,)*(N-1)
if K: w0=pushL(bot,K,0)
else: w0=bot
add_state(('B',0,INF,0,w0,bot))
try:
    it=0
    while work:
        s=work.popleft(); it+=1; cur[0]=s
        for t in succ(s): add_state(norm(t))
        if it%200000==0: print("..",it,len(states),sum(map(len,NL.values())),sum(map(len,NG.values())),flush=True)
    print("CLOSED: states",len(states),"L-grams",sum(map(len,NL.values())),"G-grams",sum(map(len,NG.values())))
except Fail as e:
    x=cur[0]; path=[]
    while x is not None and len(path)<40: path.append(x); x=parent[x]
    for y in path[::-1]: print("   ",y)
    print("FAIL:",e,"states",len(states),"L-grams",sum(map(len,NL.values())),"G-grams",sum(map(len,NG.values())))
