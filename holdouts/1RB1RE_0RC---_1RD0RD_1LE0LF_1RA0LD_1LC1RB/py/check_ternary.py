"""Check the ternary step of 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB on `tmrun M N at E L K` output (stdin):
E> (01)^(3^k) (10)^y 1 G  ->  E> (01)^(3^(k+1)) (10)^(y-2*3^k+1) 1 G  whenever y >= 2*3^k - 1."""
import sys,re
# parse tmrun "at E L" lines: expand to string
def cells(f):
    s=[]
    for t in f:
        t=re.sub(r'[A-F]>','',t); c,n=(t.split('^')+['1'])[:2]; s.append(c*int(n))
    return ''.join(s)
prev=None; ok=bad=0; over=[]
for line in sys.stdin:
    f=line.split()
    if not f[0].isdigit(): continue
    s=cells(f[1:])
    m=re.match(r'((?:01)+)((?:10)*)1(.*)$',s)
    if s.startswith("11"): continue
    if not m: prev=None; continue
    n01=len(m.group(1))//2; y=len(m.group(2))//2; G=m.group(3)
    k=0; t=n01
    while t%3==0 and t>1: t//=3; k+=1
    if t!=1: prev=None; continue
    cur=(int(f[0]),k,y,len(G),G[:50])
    if prev and prev[1]>=1:
        _,pk,py,pl,pg=prev
        if py>=2*3**pk-1:
            if (k,y,len(G))==(pk+1,py-2*3**pk+1,pl): ok+=1
            else: bad+=1; print('BAD',prev,cur)
    if k==1: over.append((int(f[0]),y,len(G)))
    prev=cur
print('ok',ok,'bad',bad)
print('k=1 starts (step,y,len rest):',over[:60])
