"""Compare a c/snap.c snapshot with a c/bacc.cpp -dump file (same format): tape (blank ends trimmed), head and state.
usage: python3 py/tapecmp.py SNAPFILE DUMPFILE   -> MATCH or DIFF"""
import sys
def norm_snap(p):
    f=open(p);L,P,c=f.readline().split();t=f.readline().strip();return norm(t,int(P)-int(L),c)
def norm_dump(p):
    f=open(p);h,c=f.readline().split();t=f.readline().strip();return norm(t,int(h),c)
def norm(t,h,c):
    a=len(t)-len(t.lstrip('0')); a=min(a,h); t=t[a:]; h-=a
    b=len(t.rstrip('0')); b=max(b,h+1); return t[:b],h,c
x=norm_snap(sys.argv[1]); y=norm_snap(sys.argv[2])
print("MATCH" if x==y else "DIFF", len(x[0]),x[1],x[2],"|",len(y[0]),y[1],y[2])
