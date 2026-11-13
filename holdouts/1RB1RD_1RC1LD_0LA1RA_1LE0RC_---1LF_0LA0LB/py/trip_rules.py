"""Trip-level rewriting rules: each round trip of the head rewrites a prefix of the run list after a^N.
usage (in this directory, after  gcc -O2 -o trips ../c/trips.c):  python3 trip_rules.py   (real run, 3e8 steps)"""
import subprocess,sys,collections,json,random
M='1RB1RD_1RC1LD_0LA1RA_1LE0RC_---1LF_0LA0LB'; a='111110'
def trips(tape,steps):
    p=subprocess.Popen(['./trips',M,tape,str(steps),'F'],stdout=subprocess.PIPE,text=True)
    prev=None
    for l in p.stdout:
        if l.startswith('HALT'): yield ('HALT',); return
        f=l.split()
        if len(f)<5: continue
        s,st,lo,mx,t=f
        if st!='F': continue
        lo=int(lo); mx=int(mx)
        if prev is not None: yield (prev,(lo,t),mx)
        prev=(lo,t)
def nlead(t):
    n=0
    while t.startswith(a,n*6): n+=1
    return n
rules={}; conf=0; stats=collections.Counter()
def feed(tape,steps,modN=2):
    global conf
    for rec in trips(tape,steps):
        if rec[0]=='HALT': print('HALT in',tape[:80]); return
        (lo1,before),(lo2,after),mx=rec
        r=mx-lo1                       # before-cells read: before[0..r-1] (cell lo1+1+i), head reached absolute mx
        reach=mx-lo2
        N1=nlead(before)
        if 6*N1>=r: stats['inside-a']+=1; continue
        U=before[6*N1:r]; rest=before[r:]
        assert after[reach:].rstrip('0')==rest.rstrip('0'), (before[:80],after[:80],reach)
        stats['shift%d'%(lo1-lo2)]+=1
        A=after[:reach]; N2=nlead(A)
        if N2<N1: 
            key=('conv',N1%modN,U); val=('conv',)
            stats['conv']+=1; continue
        V=A[6*N2:]; key=(N1%modN,U); val=(N2-N1,V)
        if N1<4: stats['smallN']+=1; continue
        if key in rules and rules[key]!=val: conf+=1; print('CONFLICT',key,rules[key],val)
        rules[key]=val; stats['ok']+=1
if __name__=='__main__':
    feed('',300000000)
    print(len(rules),conf,stats)
    L=collections.Counter(len(k[1]) for k in rules); print(sorted(L.items())[-10:])
    json.dump([[k[0],k[1],v[0],v[1]] for k,v in rules.items()],open('rulesA.json','w'))
