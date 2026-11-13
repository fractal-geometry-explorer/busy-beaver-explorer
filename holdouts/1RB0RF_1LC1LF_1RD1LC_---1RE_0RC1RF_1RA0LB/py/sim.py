"""Reference simulator (bytearray tape, run-length printing) used by counter_check.py."""
import sys
def parse(s):
    T={}
    for i,g in enumerate(s.split('_')):
        for b in range(2):
            t=g[3*b:3*b+3]
            T[(i,b)]=None if t[2]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
    return T
def rle(cells):
    out=[];i=0
    while i<len(cells):
        j=i
        while j<len(cells) and cells[j]==cells[i]: j+=1
        out.append(cells[i] if j-i==1 else f"{cells[i]}^{j-i}"); i=j
    return ' '.join(out)
class TM:
    def __init__(s,m,N=1<<20):
        s.T=parse(m); s.tape=bytearray(N); s.p=N//2; s.st=0; s.k=0; s.lo=s.hi=s.p
    def step(s):
        t=s.T[(s.st,s.tape[s.p])]
        if t is None: return False
        w,d,n=t; s.tape[s.p]=w; s.p+=d; s.st=n; s.k+=1
        if s.p<s.lo: s.lo=s.p
        if s.p>s.hi: s.hi=s.p
        return True
    def show(s,pad=0):
        lo,hi=s.lo-pad,s.hi+pad
        L=rle([str(x) for x in s.tape[lo:s.p]]); R=rle([str(x) for x in s.tape[s.p+1:hi+1]])
        return f"{L} {'ABCDEF'[s.st]}>{s.tape[s.p]} {R}"
