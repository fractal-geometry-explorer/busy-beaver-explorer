import sys,collections
M="1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB"
T={}
for s in range(6):
    for b in range(2):
        p=M[s*7+b*3:s*7+b*3+3]
        if p[0]!='-': T[(s,b)]=(int(p[0]),1 if p[1]=='R' else -1,ord(p[2])-65)
N=1<<20
tape=bytearray(N);p=N//2;s=0;lo=p;hi=p
steps=int(float(sys.argv[1]));every=int(sys.argv[2]);cap=int(sys.argv[3]);K=int(sys.argv[4])
def blocks(a,b):
    return [len(x) for x in bytes(tape[a:b]).replace(b'\1',b'1').replace(b'\0',b' ').split()]
def cls(l): return str(l) if l<=cap else "m%d"%(l%4)
G={"L":collections.Counter(),"R":collections.Counter()}
hist=[]
for step in range(1,steps+1):
    b=tape[p]
    w,d,ns=T[(s,b)]
    if s==2 and b==0 and step%every==0:
        for side,bl in (("L",blocks(lo,p)),("R",blocks(p+1,hi+1))):
            c=["#"]+[cls(l) for l in bl]+["H"] if side=="L" else ["H"]+[cls(l) for l in bl]+["#"]
            for i in range(len(c)-K+1): G[side][tuple(c[i:i+K])]+=1
    if step in (steps//4,steps//2,3*steps//4): hist.append((len(G["L"]),len(G["R"])))
    tape[p]=w;p+=d;s=ns
    if p<lo:lo=p
    if p>hi:hi=p
print("distinct %d-grams L,R over time:"%K,hist,(len(G["L"]),len(G["R"])))
for side in "LR":
    print(side," | ".join("%s:%d"%(" ".join(k),v) for k,v in sorted(G[side].items(),key=lambda x:-x[1])[:int(sys.argv[5])]))
