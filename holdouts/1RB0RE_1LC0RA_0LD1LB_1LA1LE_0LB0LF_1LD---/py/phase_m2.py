"""S(m) -> next clean phase start S(m'), by direct simulation (used for the m = 2 mod 3 case).
usage: python3 phase_m2.py MAXSTEPS m1 m2 ...   (e.g. 30000000 2 5 8 11)
S(m) is 0^inf A> 1 1 1 0 1 0 1^m 0^inf; prints (S, m', steps), (HALT, steps) or (?, MAXSTEPS)."""
import sys
def parse(M):
    T = {}
    for i, g in enumerate(M.split("_")):
        for b in range(2):
            t = g[3 * b:3 * b + 3]
            T[(i, b)] = None if t[2] == "-" else (int(t[0]), 1 if t[1] == "R" else -1, ord(t[2]) - 65)
    return T

M='1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---'
T=parse(M)
def nextS(m,maxsteps):
    pad=1<<21
    tape=bytearray(2*pad); tape[pad:pad+6]=bytes([1,1,1,0,1,0]); tape[pad+6:pad+6+m]=b'\x01'*m
    p=pad; s=0; n=0; lo=p
    while n<maxsteps:
        t=T[(s,tape[p])]
        if t is None: return ('HALT',n+1)
        tape[p]=t[0]; p+=t[1]; s=t[2]; n+=1
        if p<lo: lo=p
        if s==0 and p==lo and tape[p:p+6]==b'\x01\x01\x01\x00\x01\x00':
            k=p+6
            while tape[k]==1: k+=1
            if not any(tape[k:k+200]) and n>0: return ('S',k-p-6,n)
    return ('?',n)
for m in map(int,sys.argv[2:]): print(m, nextS(m,int(sys.argv[1])), flush=True)
