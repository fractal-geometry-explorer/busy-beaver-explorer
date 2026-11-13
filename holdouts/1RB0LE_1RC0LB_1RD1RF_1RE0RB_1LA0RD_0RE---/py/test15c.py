from mac15c import rule, flat, from_flat
from ev import parse
A={}
for line in open(__import__('sys').argv[1]):
    p=line.split()
    if len(p)==2 and p[0].isdigit():
        c=parse(p[1])
        while len(c)>2 and c[0]==0 and c[1]=='0': c=c[2:]
        A[int(p[0])]=c
cfg=from_flat([10,'S',14,'S',6,'S',12]); steps=3513; n=bad=0
while steps<1.9e8:
    cfg,s,r=rule(cfg); steps+=s
    if steps in A:
        n+=1
        if flat(*cfg)!=A[steps]:
            bad+=1
            if bad<3: print('BAD',steps,flat(*cfg)[-12:],A[steps][-12:])
    else: bad+=1; print('nostep',steps); break
print('checked',n,'bad',bad)
