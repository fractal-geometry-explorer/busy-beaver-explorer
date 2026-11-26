import sys
from collections import deque
T="1RB1RF_1RC1LC_1LD0LE_---1LE_1RF0LB_0RA1RE".split('_')
tab={}
for i,s in enumerate(T):
    for r in range(2):
        t=s[3*r:3*r+3]
        tab[(i,r)]=None if t[0]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
def f(q,w,a,maxsteps=100000):
    # cells: index 0 = p'-1 (the 0 before token), then 1^a at 1..a, then 0 at a+1, head at a+2 = p, w from a+2
    cells=[0]+[1]*a+[0]+list(w)
    p=a+2; pp=1  # p' = index 1
    for n in range(maxsteps):
        if p>=len(cells): return ('NEED',n)
        if p<pp: return ('LEFT',n)
        r=cells[p]; t=tab[(q,r)]
        if t is None: return ('HALT',n)
        cells[p]=t[0]; p+=t[1]; q=t[2]
        if p==pp: return (q,tuple(cells[pp:]),n)
    return ('LOOP',)
if __name__=="__main__":
    M=int(sys.argv[1]); A=int(sys.argv[2])
    seeds=[l.split() for l in open(sys.argv[3])]
    S=set(); dq=deque()
    for q,w in seeds:
        c=(ord(q)-65,tuple(int(x) for x in w[:M])); 
        if c not in S: S.add(c); dq.append(c)
    bad=[]
    while dq:
        q,w=dq.popleft()
        for a in range(1,A+1):
            r=f(q,w,a)
            if isinstance(r[0],str): bad.append((q,w,a,r)); continue
            c=(r[0],r[1][:M])
            if c not in S: S.add(c); dq.append(c)
        if len(S)>200000: print("too many"); break
    print("carries",len(S),"bad",len(bad))
    from collections import Counter
    print(Counter((b[3][0]) for b in bad))
    for b in bad[:10]: print('ABCDEF'[b[0]],''.join(map(str,b[1])),b[2],b[3])
