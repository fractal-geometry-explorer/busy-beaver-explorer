import sys,random
M="1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB"
T={}
for s in range(6):
    for b in range(2):
        p=M[s*7+b*3:s*7+b*3+3]
        if p[0]!='-': T[(s,b)]=(int(p[0]),1 if p[1]=='R' else -1,ord(p[2])-65)
def run(tape,p,s,steps):
    for step in range(steps):
        k=(s,tape[p])
        if k not in T: return step
        w,d,s=T[k]; tape[p]=w; p+=d
    return None
def to_runs(cells):
    out=[];i=0
    while i<len(cells):
        j=i
        while j<len(cells) and cells[j]==cells[i]: j+=1
        out.append([cells[i],j-i]); i=j
    return out
random.seed(int(sys.argv[1])); t0=int(float(sys.argv[2])); mode=sys.argv[3]; trials=int(sys.argv[4]); after=int(float(sys.argv[5]))
N=1<<18
tape=bytearray(N);p=N//2;s=0
# run to a C0 event after t0
step=0
while True:
    if step>=t0 and s==2 and tape[p]==0: break
    w,d,s2=T[(s,tape[p])]; tape[p]=w; p+=d; s=s2; step+=1
left=bytes(tape[:p]).lstrip(b'\0'); right=bytes(tape[p:]).rstrip(b'\0')
lr=to_runs(list(left)); rr=to_runs(list(right))
print("step",step,"left runs",len(lr),"right runs",len(rr))
res={"halt":0,"ok":0}
for tr in range(trials):
    l=[r[:] for r in lr]; r_=[r[:] for r in rr]
    side=l if mode[0]=='L' else r_
    if mode[1]=='b':   # add 4*k to a random 1-block (not within 6 runs of the head, not the end ones)
        cand=[i for i in range(3,len(side)-8) if side[i][0]==1] if mode[0]=='L' else [i for i in range(8,len(side)-3) if side[i][0]==1]
        i=random.choice(cand); side[i][1]+=int(mode[2:])
        desc=(i,side[i][1])
    elif mode[1]=='s': # insert k singles "0 1" next to an existing single
        cand=[i for i in range(3,len(side)-8) if side[i]==[1,1]] if mode[0]=='L' else [i for i in range(8,len(side)-3) if side[i]==[1,1]]
        i=random.choice(cand); k=int(mode[2:])
        side[i:i]=[[1,1],[0,1]]*k
        desc=(i,)
    elif mode[1]=='d': # delete a block (and one zero): merge
        cand=[i for i in range(3,len(side)-8) if side[i][0]==1] if mode[0]=='L' else [i for i in range(8,len(side)-3) if side[i][0]==1]
        i=random.choice(cand); desc=(i,side[i][1]); del side[i:i+2]
    cells=[b for bit,n in l for b in [bit]*n]; rc=[b for bit,n in r_ for b in [bit]*n]
    tp=bytearray(N); base=N//2-len(cells)
    tp[base:base+len(cells)]=bytes(cells); tp[N//2:N//2+len(rc)]=bytes(rc)
    h=run(tp,N//2,2,after)
    res["halt" if h is not None else "ok"]+=1
    if mode[1]=='b':
        i=desc[0]; ctx=" ".join(str(side[j][1]) if side[j][0] else "_"*side[j][1] for j in range(max(0,i-8),min(len(side),i+9)) if True)
        print("  %s pert at run %d: %s" % ("HALT" if h is not None else "ok  ", i, ctx.replace(" _ "," ")))
print(mode,res)
