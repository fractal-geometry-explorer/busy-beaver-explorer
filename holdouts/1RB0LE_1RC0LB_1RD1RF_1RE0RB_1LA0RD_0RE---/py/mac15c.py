"""Run-length macro simulator for 1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE--- at E-records.
cfg = (groups, last): groups farthest-first, each [v, s, cnt] = cnt copies of block v then separator s; then block
`last`, then "1 E>0".  Rules: symbolic one-record (or fused two-record) runs on abstracted windows (symrec.record),
cached by key. Level 1: double-record linear jumps; level 2: cycle detection on run-length snapshots."""
import sys
from symrec import record, Lin, show
from bbtools.symtm import TouchContext
T=12
CACHE={}
class Unknown(Exception): pass
def norm_groups(gs):
    out=[]
    for g in gs:
        if g[2]==0: continue
        if out and out[-1][0]==g[0] and out[-1][1]==g[1]: out[-1][2]+=g[2]
        else: out.append(list(g))
    return out
def flat(groups,last):
    c=[]
    for v,s,k in groups: c+=[v,s]*k
    return c+[last]
def from_flat(c):
    gs=[[c[i],c[i+1],1] for i in range(0,len(c)-1,2)]
    return norm_groups(gs), c[-1]
def split_tail(groups, n):
    """make the last n units (block+sep) individual groups (count 1); returns new list"""
    gs=[list(g) for g in groups]
    need=n; i=len(gs)-1; out_tail=[]
    while need>0 and i>=0:
        v,s,k=gs[i]
        if k<=need:
            out_tail=[[v,s,1] for _ in range(k)]+out_tail; need-=k; gs.pop(); i-=1
        else:
            gs[i][2]=k-need; out_tail=[[v,s,1] for _ in range(need)]+out_tail; need=0
    return gs, out_tail
def regular(c):
    n=len(c)
    if n>=5 and c[-2]=='1' and c[-4]=='1' and c[-3]==0: return False
    return True
def core(win, edge, mid):
    """win: flat list (window .. defect .. y [MID] lastmid z); mid=(sum,count) if 'MID' in win."""
    env={}; tmpl=[]; key=[]
    for i,t in enumerate(win):
        if t=='MID':
            env['mid']=mid[0]-T; tmpl.append(Lin('mid')+T); key.append('MID')
        elif i%2==0 and t>=T:
            v='v%d'%i; env[v]=t-T; tmpl.append(Lin(v)+T); key.append('B')
        else: tmpl.append(t); key.append(t)
    key=(tuple(key),edge)
    if key in CACHE:
        r=CACHE[key]
        if r=='TOUCH': raise TouchContext('cached')
    else:
        try:
            out,steps=record(tmpl,edge); nrec=1
            if not regular(out):
                out,steps2=record(out,edge); steps=steps+steps2; nrec=2
                if not regular(out): raise Unknown('irregular twice')
            r=(out,steps,nrec); CACHE[key]=r
        except TouchContext:
            CACHE[key]='TOUCH'; raise
    out,steps,nrec=r
    res=[]
    for x in out:
        if isinstance(x,Lin) and 'mid' in x.c:
            if x!=Lin('mid')+T: raise Unknown('middle changed')
            res.append('MID')
        else: res.append(x.subs(env) if isinstance(x,Lin) else x)
    extra = 26*(mid[1]-1) if mid else 0
    return res, steps.subs(env)+extra, nrec
def rule(cfg):
    groups,last=cfg
    # active defect group index
    j=None
    for i in range(len(groups)-1,-1,-1):
        if groups[i][1]!='S': j=i; break
    K=2
    while True:
        if j is None:
            pre_units=len(groups) if True else 0
            # no defect: window = whole tape, zone = all; collapse middle
            prefix=[]; zone_groups=groups; wunits=[]; edge=True
        else:
            # split so that the defect group and K units before are single
            n_before=sum(g[2] for g in groups[:j])
            take=min(K, n_before)
            gs_pre, tail=split_tail(groups[:j], take)
            edge = (take==n_before)
            prefix=gs_pre; wunits=tail+[list(groups[j])]
            if wunits[-1][2]!=1:
                # defect group with count>1: split, the earlier copies go to the window/prefix
                k=wunits[-1][2]; wunits[-1]=[groups[j][0],groups[j][1],1]
                extra_units=[[groups[j][0],groups[j][1],1]]*(k-1)
                wunits=wunits[:-1]+extra_units+[wunits[-1]]
            zone_groups=groups[j+1:]
        # zone: groups (all with sep S) + last. y = first zone block, lastmid = last zone group block, z = last
        zflat_units=[]
        zg=[list(g) for g in zone_groups]
        # first unit (y) and last unit (lastmid) individual, middle collapsed
        n_zone=sum(g[2] for g in zg)
        mid=None; zwin=[]
        if n_zone>=4:
            # y unit
            first=zg[0][:2]; 
            zg2=[list(g) for g in zg]; zg2[0][2]-=1
            lastu=zg2[-1][:2]; zg2[-1][2]-=1
            mids=[g for g in zg2 if g[2]>0]
            msum=sum(g[0]*g[2] for g in mids); mcnt=sum(g[2] for g in mids)
            if msum>=T:
                mid=(msum,mcnt); zwin=[first[0],'S','MID','S',lastu[0],'S']
                midgroups=mids
            else:
                zwin=flat(zg,0)[:-1]; midgroups=None
        else:
            zwin=flat(zg,0)[:-1]; midgroups=None
        win=[]
        for u in wunits: win+=[u[0],u[1]]
        win+=zwin+[last]
        try:
            out,steps,nrec=core(win,edge,mid)
        except TouchContext:
            if j is None or edge: raise Unknown('touch at edge')
            K+=1; continue
        # rebuild groups
        if 'MID' in out:
            i=out.index('MID')
            left=out[:i]; right=out[i+1:]
            ng=from_flat(left+[0])[0] if len(left)>0 else []
            # left ends with a separator (S) before MID
            lg=[[left[t],left[t+1],1] for t in range(0,len(left)-1,2)]
            rg=[[right[t+1],right[t+2],1] for t in range(0,len(right)-2,2)] if len(right)>2 else []
            # right = ['S', lastmid, 'S', ..., z] : MID is followed by its separator 'S'
            assert right[0]=='S'
            rest=right[1:]
            rgs=[[rest[t],rest[t+1],1] for t in range(0,len(rest)-1,2)]
            newg=prefix+lg+[[g[0],g[1],g[2]] for g in midgroups[:-1]]+[[midgroups[-1][0],'S',midgroups[-1][2]]]+rgs
            newlast=rest[-1]
        else:
            fg,fl=from_flat(out)
            newg=prefix+fg; newlast=fl
        return (norm_groups(newg),newlast), steps, nrec
