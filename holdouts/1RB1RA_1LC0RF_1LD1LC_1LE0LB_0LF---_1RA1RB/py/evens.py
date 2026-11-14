import sys,collections
M="1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB"
T={}
for s in range(6):
    for b in range(2):
        p=M[s*7+b*3:s*7+b*3+3]
        if p[0]!='-': T[(s,b)]=(int(p[0]),1 if p[1]=='R' else -1,ord(p[2])-65)
N=1<<20
tape=bytearray(N);p=N//2;s=0;lo=p;hi=p
steps=int(float(sys.argv[1]));every=int(sys.argv[2])
def runs(a,b):
    seg=bytes(tape[a:b]);out=[];i=0;n=len(seg)
    while i<n:
        j=i
        while j<n and seg[j]==seg[i]: j+=1
        out.append((seg[i],j-i)); i=j
    return out
stat=collections.Counter();ex={}
def cls(l): return str(l) if l<=6 else ("o" if l%2 else "e")+"%d"%(l%4)
for step in range(1,steps+1):
    b=tape[p]
    w,d,ns=T[(s,b)]
    ev=None
    if s==2 and b==0: ev="C0"
    if s==0 and b==0: ev="A0"
    if ev and step%every==0:
        lr=runs(lo,p); rr=runs(p+1,hi+1)
        while lr and lr[0][0]==0: lr.pop(0)
        while rr and rr[-1][0]==0: rr.pop()
        lb=[l for bit,l in lr if bit]; rb=[l for bit,l in rr if bit]
        k=len(lb)
        for i,l in enumerate(lb):
            if l%2==0:
                j=i+1
                while j<k and lb[j]==1: j+=1
                ns_=j-i-1
                nxt=cls(lb[j]) if j<k else "H"
                key=(ev,"L","most" if i==0 else "", "headblk" if i==k-1 else "", cls(l), "singles%d"%(ns_ if ns_<4 else 4+ns_%2), "then",nxt)
                stat[key]+=1; ex.setdefault(key,step)
        for i,l in enumerate(rb):
            if l%2==0:
                key=(ev,"R","last" if i==len(rb)-1 else "", "headblk" if i==0 else "", cls(l), "prev", cls(rb[i-1]) if i>0 else "H")
                stat[key]+=1; ex.setdefault(key,step)
        if lb and rb is not None:
            hk=(ev,"HB", "L%d"%(lb[-1]%2) if ev=="A0" else "R%d"%(rb[0]%2 if rb else -1))
            stat[hk]+=1; ex.setdefault(hk,step)
    tape[p]=w;p+=d;s=ns
    if p<lo:lo=p
    if p>hi:hi=p
for k,v in sorted(stat.items(),key=lambda x:(x[0][0],x[0][1],-x[1])): print(v,ex[k]," ".join(k))
