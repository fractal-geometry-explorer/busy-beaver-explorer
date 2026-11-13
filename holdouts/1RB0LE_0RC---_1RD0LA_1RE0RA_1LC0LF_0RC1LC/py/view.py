"""Print the tape of 1RB0LE_0RC---_1RD0LA_1RE0RA_1LC0LF_0RC1LC each time the head, in state C, reads a 0 on the
leftmost visited cell.  The part right of the head is cut into 4-cell words at the offset with the most `0011`s:
`.` is 0011, `o` is 0001, anything else is shown in brackets; before the first `|` is what precedes the words.
usage: view.py STEPS [FIRST]"""
import sys
m='1RB0LE_0RC---_1RD0LA_1RE0RA_1LC0LF_0RC1LC'
T={}
for i,g in enumerate(m.split('_')):
    for r in (0,1):
        t=g[3*r:3*r+3]
        T[(chr(65+i),r)]=None if t[0]=='-' else (int(t[0]),1 if t[1]=='R' else -1,t[2])
N=int(float(sys.argv[1])); N0=int(float(sys.argv[2])) if len(sys.argv)>2 else 0
tape=bytearray(1<<21); p=1<<20; s='A'; lo=hi=p
def words(x):
    best=None
    for off in range(4):
        ws=[x[off+4*i:off+4*i+4] for i in range((len(x)-off)//4)]
        c=sum(w=='0011' for w in ws)
        if best is None or c>best[0]: best=(c,off,ws,x[off+4*len(ws):])
    c,off,ws,rest=best
    m={'0011':'.','0001':'o'}
    return x[:off]+'|'+''.join(m.get(w,'['+w+']') for w in ws)+'|'+rest
for n in range(N):
    r=tape[p]
    if n>=N0 and p==lo and s=='C' and r==0 and n>0:
        x=bytes(tape[p+1:hi+1]).decode('latin1').translate({0:'0',1:'1'})
        print(n, words(x))
    t=T[(s,r)]
    if t is None: print('halt',n); break
    tape[p]=t[0]; p+=t[1]; s=t[2]; lo=min(lo,p); hi=max(hi,p)
