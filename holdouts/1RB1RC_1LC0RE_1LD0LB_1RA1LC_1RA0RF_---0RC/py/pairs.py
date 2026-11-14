"""The pair macro machine of a six-state machine: what each state does to an aligned pair of cells.

The tapes of the family 1RB1RC_1LC0RE_1LD0LB_1RA1LC_* are read in pairs a = 01, b = 11, c = 10, z = 00, aligned to
the block of 1s.  For every state and side of entry this prints the pair left behind, the side the head leaves on,
the new state and the number of steps (or HALT / LOOP).

usage: python3 pairs.py MACHINE
"""
import sys
def parse(m):
    T={}
    for i,row in enumerate(m.split('_')):
        for b in range(2):
            t=row[3*b:3*b+3]
            T[(i,b)]=None if t[0]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
    return T
NM={(0,1):'a',(1,1):'b',(1,0):'c',(0,0):'z'}
INV={v:k for k,v in NM.items()}
def macro(T,s,side,p):
    c=list(INV[p]); h=0 if side=='L' else 1
    for k in range(1,100):
        t=T[(s,c[h])]
        if t is None: return ('HALT',k)
        c[h]=t[0]; h+=t[1]; s=t[2]
        if h<0: return (NM[tuple(c)],'<','ABCDEF'[s],k)
        if h>1: return (NM[tuple(c)],'>','ABCDEF'[s],k)
    return ('LOOP',)
if __name__=="__main__":
    T=parse(sys.argv[1])
    for s in range(6):
        for side in 'LR':
            print('ABCDEF'[s]+('>' if side=='L' else '<'),'  '.join(p+':'+' '.join(map(str,macro(T,s,side,p))) for p in 'abcz'))
