"""Step by step trace of 1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB--- around the head.  usage: python3 holdouts/1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---/py/micro.py FROM TO [WIDTH]"""
import sys
M="1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---"
T={}
for s,part in enumerate(M.split('_')):
    for r in range(2):
        t=part[3*r:3*r+3]
        T[(s,r)]=None if t[2]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
tab=[[T[(s,r)] for r in range(2)] for s in range(6)]
F,TO=int(float(sys.argv[1])),int(float(sys.argv[2]))
W=int(sys.argv[3]) if len(sys.argv)>3 else 40
tape=bytearray(1<<22);p=lo=hi=1<<21;st=0
for k in range(1,TO+1):
    w,m,ns=tab[st][tape[p]]
    tape[p]=w;p+=m;st=ns
    if p<lo: lo=p
    if p>hi: hi=p
    if k>=F:
        a=max(lo-2,p-W);b=min(hi+3,p+W)
        s=''.join('.1'[c] for c in tape[a:p])+'['+'ABCDEF'[st]+'.1'[tape[p]]+']'+''.join('.1'[c] for c in tape[p+1:b])
        print(k,hi-p,s)
