"""Macro simulator for 1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE--- at E-records, rules derived by symbolic simulation
(bbtools.symtm) on abstracted windows and cached. Exact: tape and steps."""
import sys
from symrec import record, Lin, show
from bbtools.symtm import TouchContext, Halted, NeedSplit
T=12            # block values >= T are abstracted to a variable
CACHE={}
class Unknown(Exception): pass
def active(c):
    for i in range(len(c)-2,0,-2):
        if c[i]!='S': return i
    return None
def abstract(c, start, edge):
    """window c[start:], middle of the zone collapsed; returns key, template, env, extra-steps function"""
    j=active(c); last=len(c)-1
    win=list(c[start:])
    # collapse middle zone blocks beyond the first two/ last one: zone = y ... z
    zs = (j+1 if j is not None else 0)-start   # index of y in win (or 0 when no defect: whole tape is zone)
    extra=0
    zone=win[zs:]
    mids=zone[2:-4]          # w1 S w2 S ... (blocks between y and the last middle block), alternating
    midlist=None
    if len(mids)>=3 and sum(mids[0::2])>=T:
        blocks=mids[0::2]
        tot=sum(blocks)
        # the template has one middle block of value tot (4*tot+26 steps); actual: 4*sum+26*r
        extra=26*(len(blocks)-1)
        midlist=mids
        zone=zone[:2]+["MID"]+zone[-4:]
    win=win[:zs]+zone
    env={}; tmpl=[]; key=[]
    for i,t in enumerate(win):
        if t=='MID':
            env['mid']=tot-T; tmpl.append(Lin('mid')+T); key.append('MID')
        elif i%2==0 and t>=T:
            v='v%d'%i; env[v]=t-T; tmpl.append(Lin(v)+T); key.append('B')
        else: tmpl.append(t); key.append(t)
    return (tuple(key),edge), tmpl, env, extra, midlist
def subst(t, env, midlist):
    out=[]
    for x in t:
        if isinstance(x,Lin) and 'mid' in x.c:
            if x!=Lin('mid')+T: raise Unknown('middle changed')
            out+=midlist
        else: out.append(x.subs(env) if isinstance(x,Lin) else x)
    return out
def rule(c):
    """one record (or a fused 2-record event) from config c: returns (c', steps, records)"""
    j=active(c)
    K=2
    while True:
        start = 0 if j is None else max(0, j-1-2*K)
        edge = (start==0)
        key,tmpl,env,extra,midlist=abstract(c,start,edge)
        prefix=c[:start]
        if key in CACHE:
            r=CACHE[key]
            if r=='TOUCH': K+=1; continue
            out,steps,nrec=r
            return prefix+subst(out,env,midlist), steps.subs(env)+extra, nrec
        try:
            out,steps=record(tmpl,edge)
            nrec=1
            # irregular intermediate (seps '1' twice near the end / '0 1 1 1' ...): fuse with the next record
            if not regular(out):
                out2,steps2=record(out,edge); out=out2; steps=steps+steps2; nrec=2
                if not regular(out): raise Unknown('irregular twice %s'%show(out))
            CACHE[key]=(out,steps,nrec)
            return prefix+subst(out,env,midlist), steps.subs(env)+extra, nrec
        except TouchContext:
            if edge: raise Unknown('touch at edge')
            CACHE[key]='TOUCH'; K+=1; continue
def regular(c):
    """heuristic: a config is regular if every separator other than the active one is S or 0/1 and the active is
    followed by a block >= ... ; we only reject the known irregular shapes"""
    s=[c[i] for i in range(1,len(c),2)]
    # irregular: two consecutive non-S separators with an empty block between, at the end
    n=len(c)
    if n>=5 and c[-2]=='1' and c[-4]=='1' and c[-3]==0: return False
    return True
if __name__=='__main__':
    c=[10,'S',14,'S',6,'S',12]; steps=3513; rec=0
    N=int(float(sys.argv[1]))
    out=open(sys.argv[2],'w') if len(sys.argv)>2 else None
    while rec<N:
        c2,s,r=rule(c)
        c=c2; steps+=s; rec+=r
        if out: out.write('%d %s\n'%(steps,' '.join(map(str,c))))
    print(rec, steps, len(CACHE))

def double(c):
    c1,s1,r1=rule(c); c2,s2,r2=rule(c1)
    return c2, s1+s2, r1+r2
def run_fast(c, steps, rec, maxrec, maxsteps=None, log=None, every=1):
    """accelerated run; returns (c, steps, rec). log(c,steps,rec) called after each macro move"""
    nmoves=0
    while rec<maxrec and (maxsteps is None or steps<maxsteps):
        if active(c) is None and c[-1]>=T+40:
            # left-edge regime: each record prepends 2 S and z -= 2; steps grow linearly
            c1,s1,r1=rule(c); c2,s2,r2=rule(c1); c3,s3,r3=rule(c2)
            if r1==r2==r3==1 and c1[2:]==c[:-1]+[c[-1]-2] and c2[2:]==c1[:-1]+[c1[-1]-2] and s3-s2==s2-s1:
                D=s2-s1
                k=(c3[-1]-T-20)//2
                k=min(k,maxrec-rec-3)
                if k>0:
                    st=k*(s3+D)+D*k*(k-1)//2
                    c=[2,'S']*k+c3[:-1]+[c3[-1]-2*k]
                    steps+=s1+s2+s3+st; rec+=3+k
                else:
                    c=c3; steps+=s1+s2+s3; rec+=3
                nmoves+=1
                if log and nmoves%every==0: log(c,steps,rec)
                continue
            c=c1; steps+=s1; rec+=r1
            continue
        c2,s,r=double(c)
        jumped=False
        if len(c2)==len(c) and all((i%2==1 and c[i]==c2[i]) or i%2==0 for i in range(len(c))):
            d=[(c2[i]-c[i]) if i%2==0 else 0 for i in range(len(c))]
            if any(d) and r==2:
                c3,s3,r3=double(c2)
                if r3==2 and len(c3)==len(c) and all(i%2==1 and c2[i]==c3[i] or i%2==0 and c3[i]-c2[i]==d[i] for i in range(len(c))):
                    D=s3-s
                    # k more doubles from c3, keeping decreasing values >= T+10
                    k=None
                    for i in range(0,len(c),2):
                        if d[i]<0:
                            kk=(c3[i]-T-10)//(-d[i])-1
                            k=kk if k is None else min(k,kk)
                    if k is None: k=10**6
                    k=min(k,(maxrec-rec-4)//2)
                    if k>0:
                        cs=[c3[i]+k*d[i] if i%2==0 else c3[i] for i in range(len(c))]
                        S0=s3+D   # steps of the first jumped double
                        st=k*S0+D*k*(k-1)//2
                        c=cs; steps+=s+s3+st; rec+=r+r3+2*k; jumped=True
                if not jumped:
                    c=c3; steps+=s+s3; rec+=r+r3; jumped=True
        if not jumped:
            c=c2; steps+=s; rec+=r
        nmoves+=1
        if log and nmoves%every==0: log(c,steps,rec)
    return c,steps,rec
