import sys
tm=sys.argv[1]; n=int(sys.argv[2]); T=int(sys.argv[3])
tr=[[None if p[i*3]=='-' else (int(p[i*3]),1 if p[i*3+1]=='R' else -1,ord(p[i*3+2])-65) for i in range(2)] for p in tm.split('_')]
tape={}; q=0; h=0
def side(s):
    nz=[i for i,v in tape.items() if v]
    c={}
    if not nz: return c
    if s==1:
        last=max(nz)
        for st in range(h+1,last+1):
            g=''.join(str(tape.get(st+j,0)) for j in range(n)); c[g]=c.get(g,0)+1
    else:
        first=min(nz)
        for en in range(first,h):
            g=''.join(str(tape.get(en-n+1+j,0)) for j in range(n)); c[g]=c.get(g,0)+1
    return c
for t in range(T):
    w=''.join(('[%d]' if o==0 else '%d')%tape.get(h+o,0) for o in range(-(n-1),n))
    print('ABCDEF'[q],w,' L:',' '.join('%s=%d'%kv for kv in sorted(side(0).items())),' R:',' '.join('%s=%d'%kv for kv in sorted(side(1).items())))
    x=tr[q][tape.get(h,0)]
    if x is None: print('HALT'); break
    tape[h]=x[0]; h+=x[1]; q=x[2]
