"""Tape of 1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC--- at the left-end events with repeated words bracketed.\nusage: gcc -O2 -o dump holdouts/1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC---/c/dump.c && ./dump 1e8 > d.txt ; python3 holdouts/1RB0RF_1RC0LE_1LD0LC_1RE0RD_1LB0RA_1RC---/py/words.py d.txt [EVERY]"""
import sys
def comp(s,maxw=24,minrep=3):
    out=[];i=0;n=len(s)
    while i<n:
        best=None
        for w in range(1,maxw+1):
            if i+2*w>n:break
            k=1
            while s[i+k*w:i+(k+1)*w]==s[i:i+w]:k+=1
            if k>=minrep and (best is None or k*w>best[0]*best[1]): best=(k,w)
        if best:
            k,w=best; out.append('(%s)^%d'%(s[i:i+w],k)); i+=k*w
        else: out.append(s[i]); i+=1
    r='';
    for t in out: r+= t if len(t)==1 else ' '+t+' '
    return r
for line in open(sys.argv[1]):
    f=line.split()
    if len(sys.argv)>2 and int(f[0])%int(sys.argv[2]): continue
    print(f[0],f[1],f[2],f[3],f[4],'|',comp(f[5]))
