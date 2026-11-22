"""Left DFA: (position since the first 1, mod M; last k cells).  usage: dfa_window.py k [M] > dfa.txt"""
import sys
k=int(sys.argv[1]); M=int(sys.argv[2]) if len(sys.argv)>2 else 3
st={('z',):0}; q=[('z',)]; D=[]
def step(x,c):
    if x[0]=='z':
        if c==0: return x
        return (1%M, (0,)*(k-1)+(1,)) if k>0 else (1%M,())
    p,s=x
    return ((p+1)%M, (s+(c,))[-k:] if k>0 else ())
i=0
while i<len(q):
    x=q[i]; row=[]
    for c in (0,1):
        y=step(x,c)
        if y not in st: st[y]=len(q); q.append(y)
        row.append(st[y])
    D.append(row); i+=1
print(len(D))
for a,b in D: print(a,b)
