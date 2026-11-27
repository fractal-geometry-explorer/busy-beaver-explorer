# sumdec: "call summary" decider. The tape right of any boundary is abstracted by its first K cells plus the
# promise that all its (K+1)-windows are in a set G. Every step to the right is a call; a call (s,u) has a
# summary: the set of (state, K-prefix) with which the head can come back. Top level is the left frontier
# (blank to the left). Least fixpoint; the machine is proved non-halting if no halting transition is reachable.
# With mirror=R the roles of left and right are exchanged.
import sys
from collections import defaultdict, deque
def parse(m,mirror=False):
    t={}
    for i,p in enumerate(m.split('_')):
        for b in (0,1):
            x=p[3*b:3*b+3]
            if x[0]=='-': t[(i,b)]=None
            else:
                d=1 if x[1]=='R' else -1
                if mirror:d=-d
                t[(i,b)]=(int(x[0]),d,ord(x[2])-65)
    return t
def decide(m,mirror,K,limit=2000000,verbose=False):
    t=parse(m,mirror); mask=(1<<K)-1
    G=set([0]); nxt=defaultdict(set); nxt[0].add(0)   # nxt[u] = set of x
    Sum=defaultdict(set); deps=defaultdict(set); gdeps=defaultdict(set)
    known=set(); work=deque(); inwork=set()
    halts=[]
    TOP=('T',)
    top=set([(0,0)])
    def push(c):
        if c not in inwork: inwork.add(c); work.append(c)
    def addG(win):
        if win not in G:
            G.add(win); u=win&mask; nxt[u].add(win>>K)
            for c in gdeps[u]: push(c)
    def need(c):
        if c not in known: known.add(c); push(c)
    def ev(c):
        s,u=c
        gdeps[u].add(c)
        seen=set(); st=[]
        for x in list(nxt[u]):
            mc=(s,u&1,(u>>1)|(x<<(K-1)))
            seen.add(mc); st.append(mc)
        res=Sum[c]; changed=False
        while st:
            q,c1,v=st.pop()
            tr=t[(q,c1)]
            if tr is None: halts.append((c,(q,c1,v))); continue
            w,d,q2=tr
            if d<0:
                win=w|(v<<1); addG(win)
                r=(q2,win&mask)
                if r not in res: res.add(r); changed=True
            else:
                cc=(q2,v); need(cc); deps[cc].add(c)
                for (q3,v3) in list(Sum[cc]):
                    mc=(q3,w,v3)
                    if mc not in seen: seen.add(mc); st.append(mc)
        if changed:
            for d_ in deps[c]: push(d_)
    def evtop():
        # top-level closure
        st=list(top)
        while st:
            q,u=st.pop()
            gdeps[u].add(TOP)
            tr=t[(q,u&1)]
            if tr is None: halts.append((TOP,(q,u))); continue
            w,d,q2=tr
            if d<0:
                for x in list(nxt[u]): addG(w|(u>>1<<1)|(x<<K))   # the rewritten tape from the old head cell on
                win=(w|(u>>1<<1))<<1   # cells: 0, w, u1..u_{K-1}
                addG(win&((1<<(K+1))-1))
                n=(q2,win&mask)
                if n not in top: top.add(n); st.append(n)
            else:
                for x in list(nxt[u]):
                    v=(u>>1)|(x<<(K-1)); cc=(q2,v); need(cc); deps[cc].add(TOP)
                    for (q3,v3) in list(Sum[cc]):
                        win=w|(v3<<1); addG(win)
                        n=(q3,win&mask)
                        if n not in top: top.add(n); st.append(n)
    push(TOP)
    it=0
    while work:
        c=work.popleft(); inwork.discard(c); it+=1
        if c==TOP: evtop()
        else: ev(c)
        if halts: return ('HALT-REACHABLE',K,len(known),len(G),len(top),halts[0])
        if len(known)>limit: return ('LIMIT',K,len(known),len(G),len(top))
    return ('NONHALT',K,len(known),len(G),len(top),sum(len(v) for v in Sum.values()))
if __name__=='__main__':
    m=sys.argv[1]; mirror=sys.argv[2]=='R'
    for K in map(int,sys.argv[3].split(',')):
        print(decide(m,mirror,K),flush=True)
