import sys, collections
def parse(tm):
    T={}
    for q,part in enumerate(tm.split('_')):
        for s in range(2):
            t=part[3*s:3*s+3]
            T[(q,s)]=None if t[2]=='-' or t[2]=='Z' else (int(t[0]), 1 if t[1]=='R' else -1, ord(t[2])-65)
    return T
def snapshots(tm, steps, nsnap=60):
    T=parse(tm); N=steps//2+10
    tape=bytearray(2*N+1); p=N; q=0; lo=hi=N; snaps=[]
    for i in range(steps):
        tr=T[(q,tape[p])]
        if tr is None: return snaps, True
        tape[p]=tr[0]; p+=tr[1]; q=tr[2]
        if p<lo or p>hi:
            lo=min(lo,p); hi=max(hi,p)
            if i>steps//3: snaps.append((i,bytes(tape[lo:hi+1])))
    if len(snaps)>nsnap:
        k=len(snaps)/nsnap; snaps=[snaps[int(j*k)] for j in range(nsnap)]
    return snaps, False
def runs(s, maxp=12, minrep=3):
    out=collections.Counter()
    n=len(s)
    for pd in range(1,maxp+1):
        i=0
        while i+pd<n:
            j=i
            while j+pd<n and s[j]==s[j+pd]: j+=1
            L=j-i+pd
            if L>=minrep*pd:
                w=s[i:i+pd]
                # primitive only
                if all(w!=w[:d]*(pd//d) for d in range(1,pd) if pd%d==0) and w!=bytes(pd):
                    out[w]+=L
                i=j+1
            else: i+=1
    return out
def cand(tm, steps=200000, top=6):
    snaps,h=snapshots(tm,steps)
    c=collections.Counter()
    for _,s in snaps: c.update(runs(s))
    return [w for w,_ in c.most_common(top)], h
def variants(ws):
    out=set()
    for w in ws:
        for v in (w, w[::-1]):
            for r in range(len(v)): out.add(v[r:]+v[:r])
    return sorted(out,key=lambda x:(len(x),x))
if __name__=='__main__':
    tm=sys.argv[1]; ws,h=cand(tm)
    print(' '.join(''.join(map(str,w)) for w in ws))
