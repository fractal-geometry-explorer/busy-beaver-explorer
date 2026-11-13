# compare macro output file with erec output (steps + configs)
import sys
from ev import parse
A={}
for line in open(sys.argv[1]):
    p=line.split()
    if len(p)==2 and p[0].isdigit():
        c=parse(p[1])
        while len(c)>2 and c[0]==0 and c[1]=='0': c=c[2:]
        A[int(p[0])]=c
n=0;bad=0
for line in open(sys.argv[2]):
    p=line.split(); st=int(p[0]); c=[int(x) if i%2==0 else x for i,x in enumerate(p[1:])]
    if st in A:
        n+=1
        if A[st]!=c: bad+=1; print('DIFF',st) if bad<5 else None
    elif st<=max(A): bad+=1; print('NOSTEP',st) if bad<5 else None
print('compared',n,'bad',bad)
