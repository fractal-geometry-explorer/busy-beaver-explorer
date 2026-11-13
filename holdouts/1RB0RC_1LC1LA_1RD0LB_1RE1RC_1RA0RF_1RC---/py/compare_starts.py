"""Compare 156554, 92022 and 67840: find the state renaming (and mirror) between their tables, then run each from
blank tape and count configurations the runs share (up to renaming, mirroring and translation).

usage: python3 compare_starts.py STEPS      (200000 steps: no common configuration; about 5 minutes)
"""
import sys
def parse(s):
    t={}
    for i,row in enumerate(s.split('_')):
        for b in (0,1):
            x=row[3*b:3*b+3]
            t[('ABCDEF'[i],b)] = None if x=='---' else (int(x[0]),x[1],x[2])
    return t
R=parse('1RB0RC_1LC1LA_1RD0LB_1RE1RC_1RA0RF_1RC---')   # 156554
T2=parse('1RB0RF_1RC0RD_1LD1LB_1RE0LC_1RA1RD_1RD---')  # 92022
T3=parse('1RB1RE_1LC0RA_1LD1LB_1LE0LF_1LA0LB_1LB---')  # 67840
import itertools
def find(T,mirror):
    out=[]
    for p in itertools.permutations('ABCDEF'):
        ren=dict(zip('ABCDEF',p))  # state of T -> state of R
        ok=True
        for (s,b),v in T.items():
            w=R[(ren[s],b)]
            if v is None or w is None:
                ok = ok and v is None and w is None
            else:
                d=v[1] if not mirror else {'L':'R','R':'L'}[v[1]]
                ok = ok and (v[0],d,ren[v[2]])==w
            if not ok: break
        if ok: out.append(ren)
    return out
print('92022 -> 156554 plain', find(T2,False), 'mirror', find(T2,True))
print('67840 -> 156554 plain', find(T3,False), 'mirror', find(T3,True))
def run(T,n,ren,mirror):
    tape={};pos=0;st='A';seen=set()
    for i in range(n+1):
        if tape:
            lo=min(tape);hi=max(tape)
        else: lo=hi=pos
        lo=min(lo,pos);hi=max(hi,pos)
        cells=tuple(tape.get(j,0) for j in range(lo,hi+1)); h=pos-lo
        if mirror: cells=cells[::-1]; h=hi-pos
        # strip zeros keeping head
        a=0
        while a<h and cells[a]==0: a+=1
        b=len(cells)
        while b-1>h and cells[b-1]==0: b-=1
        seen.add((ren[st],cells[a:b],h-a))
        v=T[(st,tape.get(pos,0))]
        if v is None: print('HALT',i);break
        if v[0]: tape[pos]=1
        else: tape.pop(pos,None)
        pos+=1 if v[1]=='R' else -1; st=v[2]
    return seen
N=int(sys.argv[1])
idn={c:c for c in 'ABCDEF'}
s1=run(R,N,idn,False)
s2=run(T2,N,find(T2,False)[0],False)
m3=find(T3,True)
s3=run(T3,N,m3[0],True) if m3 else set()
print(len(s1),len(s2),len(s3),'common 1&2',len(s1&s2),'1&3',len(s1&s3),'2&3',len(s2&s3))
