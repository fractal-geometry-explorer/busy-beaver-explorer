#!/usr/bin/env python3
"""Compare two tape descriptions exactly (state, head position relative to first non-blank cell, all cells).
Each side is one of
   sim:FILE     dump written by sim3   (run-length words, head between the two stacks)
   plain:FILE   last line of ./plain   ("steps S pos=.. lo=.. : 0101[1]0")
   C:r          the configuration C(r) of the claim
   desc:STATE:HEADINDEX:w^n,w^n,...
Counts may be huge; comparison never expands runs."""
import sys
from math import gcd
def parse_sim(fn):
    ls=open(fn).read().split('\n')
    hdr=ls[0].split(); steps=int(hdr[1]); halted=int(hdr[hdr.index('halted')+1]); haltpos=int(hdr[hdr.index('haltpos')+1])
    def segs(l): return [(t.split('^')[0],int(t.split('^')[1])) for t in l.split()]
    L=segs(ls[1]); R=segs(ls[3]); d=ls[2][0]; st=ls[2][1]
    if d=='<':
        if not L: L=[('0',1)]
        w,c=L[-1]; off=(haltpos if halted else len(w)-1)
        head=sum(len(a)*b for a,b in L)-len(w)+off
    else:
        if not R: R=[('0',1)]
        head=sum(len(a)*b for a,b in L)+(haltpos if halted else 0)
    return st,head,L+R,steps
def parse_plain(fn):
    l=[x for x in open(fn).read().split('\n') if ':' in x][-1]
    h,t=l.rsplit(':',1); t=t.strip(); head=t.index('['); t=t.replace('[','').replace(']','')
    return h.split()[1],head,[(t,1)],int(h.split()[0])
def C(r): return 'E',0,[('0',1),('1011001',59),('1011',1),('00000',1),('1101100110110',1),('011',16),('001101100110',1),('011',r)],None
def parse(a):
    k,v=a.split(':',1)
    if k=='sim': return parse_sim(v)
    if k=='plain': return parse_plain(v)
    if k=='C': return C(int(v))
    if k=='desc':
        st,h,d=v.split(':'); return st,int(h),[(t.split('^')[0],int(t.split('^')[1]) if '^' in t else 1) for t in d.split(',')],None
def norm(st,head,segs):
    segs=[(w,c) for w,c in segs if c>0]
    # strip blanks on the left
    pos=0; out=list(segs)
    while out and '1' not in out[0][0]: pos+=len(out[0][0])*out[0][1]; out.pop(0)
    if out:
        w,c=out[0]; z=w.index('1'); pos+=z; out[0:1]=[(w[z:],1)]+([(w,c-1)] if c>1 else [])
    while out and '1' not in out[-1][0]: out.pop()
    if out:
        w,c=out[-1]; z=w.rindex('1'); out[-1:]=([(w,c-1)] if c>1 else [])+[(w[:z+1],1)]
    return st,head-pos,out
def same(A,B):
    ia=ib=0; ra=rb=None; oa=ob=0  # remaining cells in current seg, offset within word
    A=list(A);B=list(B); pos=0
    ra=len(A[0][0])*A[0][1] if A else 0; rb=len(B[0][0])*B[0][1] if B else 0
    while True:
        if ia>=len(A) or ib>=len(B):
            return (ia>=len(A) and ib>=len(B)), pos
        wa=A[ia][0]; wb=B[ib][0]; n=min(ra,rb); l=len(wa)*len(wb)//gcd(len(wa),len(wb))
        m=n if n<=4*l else l
        for i in range(m):
            if wa[(oa+i)%len(wa)]!=wb[(ob+i)%len(wb)]: return False,pos+i
        adv=n if n<=4*l else (n//l)*l
        pos+=adv; oa=(oa+adv)%len(wa); ob=(ob+adv)%len(wb); ra-=adv; rb-=adv
        if ra==0:
            ia+=1; oa=0
            if ia<len(A): ra=len(A[ia][0])*A[ia][1]
        if rb==0:
            ib+=1; ob=0
            if ib<len(B): rb=len(B[ib][0])*B[ib][1]
a=parse(sys.argv[1]); b=parse(sys.argv[2])
na=norm(*a[:3]); nb=norm(*b[:3])
ok,pos=same(na[2],nb[2])
tot=lambda s: sum(len(w)*c for w,c in s)
print("A: state %s head_offset %d nonblank_span %d steps %s"%(na[0],na[1],tot(na[2]),a[3]))
print("B: state %s head_offset %d nonblank_span %d steps %s"%(nb[0],nb[1],tot(nb[2]),b[3]))
if na[0]==nb[0] and na[1]==nb[1] and ok: print("IDENTICAL configurations"); sys.exit(0)
print("DIFFERENT: state %s, head %s, tape %s (first differing cell index %s from first non-blank)"%(na[0]==nb[0],na[1]==nb[1],ok,pos)); sys.exit(1)
