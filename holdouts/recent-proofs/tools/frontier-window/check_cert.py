#!/usr/bin/env python3
"""Independent checker for an endsplit certificate.
Lines:  T c q r   cell c in front of a half tape of class q gives class r (class 0 = blank)
        F s q s2 q2   entering a half tape of class q in state s can come back in state s2 leaving class q2
        P a i win q   top level: exact window `win` at the left frontier, head on cell i in state a, class q beyond
Meaning: Lang is the least family with blank in Lang(0) and c.t in Lang(r) whenever t in Lang(q) and T c q r.
Checked: (1) T 0 0 0; (2) every contract (s, r) that is used is closed under one-cell unfolding and never halts;
(3) the top-level graph contains the start, is closed, and has no halting node.
Optional: --run N replays N real steps and checks that every real configuration is covered."""
import sys
from collections import defaultdict
def main():
    path=sys.argv[1]; T={}; U=defaultdict(list); F=defaultdict(set); P=set(); mach=None; mirror=False
    for ln in open(path):
        x=ln.split()
        if x[0]=='machine': mach=x[1]; mirror=(x[2]=='R')
        elif x[0]=='T': c,q,r=int(x[1]),int(x[2]),int(x[3]); assert T.get((c,q),r)==r; T[(c,q)]=r; U[r].append((c,q))
        elif x[0]=='F': F[(int(x[1]),int(x[2]))].add((int(x[3]),int(x[4])))
        elif x[0]=='P': P.add((int(x[1]),int(x[2]),x[3],int(x[4])))
    tm=[]
    for st in mach.split('_'):
        row=[]
        for b in range(2):
            t=st[3*b:3*b+3]
            if t[0]=='-': row.append(None)
            else:
                d=1 if t[1]=='R' else -1
                row.append((int(t[0]), -d if mirror else d, ord(t[2])-65))
        tm.append(row)
    assert T.get((0,0))==0, "blank is not a fixed point"
    used=set(); bad=0
    TW=len(next(iter(P))[2])
    assert (0,0,'0'*TW,0) in P, "start missing"
    # top level
    for (a,i,win,q) in P:
        tr=tm[a][int(win[i])]
        assert tr is not None, f"top-level halt {a} {i} {win} {q}"
        w,d,a2=tr; win2=win[:i]+str(w)+win[i+1:]
        if d<0:
            if i>0: assert (a2,i-1,win2,q) in P
            else:
                r=T.get((int(win2[-1]),q)); assert r is not None, "fold transition missing"
                assert (a2,0,'0'+win2[:-1],r) in P
        elif i<TW-1: assert (a2,i+1,win2,q) in P
        else:
            used.add((a2,q))
            for (s2,q2) in F[(a2,q)]: assert (s2,TW-1,win2,q2) in P
    # contracts
    todo=list(used)
    while todo:
        s,r=todo.pop()
        res=F[(s,r)]
        for (c,q) in U[r]:
            seen={(s,c,q)}; st=[(s,c,q)]
            while st:
                a,c1,qi=st.pop(); tr=tm[a][c1]
                assert tr is not None, f"halt inside contract {s} {r}"
                w,d,a2=tr
                if d<0:
                    r2=T.get((w,qi)); assert r2 is not None and (a2,r2) in res, f"missing fact {s} {r} -> {a2} {r2}"
                else:
                    if (a2,qi) not in used: used.add((a2,qi)); todo.append((a2,qi))
                    for (s2,q2) in F[(a2,qi)]:
                        m=(s2,w,q2)
                        if m not in seen: seen.add(m); st.append(m)
    print(f"certificate OK: {mach} {'R' if mirror else 'L'}  classes={len(U)} transitions={len(T)} contracts={len(used)} facts={sum(len(F[k]) for k in used)} top nodes={len(P)} window={TW}")
    if '--run' in sys.argv:
        N=int(float(sys.argv[sys.argv.index('--run')+1])); S=1<<22; tape=bytearray(S); C=[0]*S; p=S//2; lo=p; a=0; calls=0
        for n in range(N):
            if p<lo+TW:
                win=''.join(map(str,tape[lo:lo+TW])); assert (a,p-lo,win,C[lo+TW-1]) in P, f"real configuration at step {n} not covered"
            tr=tm[a][tape[p]]; w,d,a2=tr; tape[p]=w
            if d<0:
                C[p-1]=T[(w,C[p])]; p-=1
                if p<lo: lo=p
            else:
                p+=1
            a=a2
        print(f"real run of {N} steps: every configuration inside the window is a top node")
main()
