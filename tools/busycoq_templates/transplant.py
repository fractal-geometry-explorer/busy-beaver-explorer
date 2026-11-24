"""Make one transplant job per (holdout, nearby proved machine, busycoq file): a copy of the busycoq file with the
neighbour's machine string replaced by the holdout (mirrored when the neighbour matched mirrored). Compile each
copy in busycoq's verify/ with coqc 8.20; jobs.json lists them. See holdouts/BUSYCOQ_TEMPLATES.md."""
import json,re,os,collections
out=json.load(open('near.json'))
skip=re.compile(r'^(Indv|CTLv|RWL_mod_v|CPS_LRU_v|RWLAccHaltv|TCv|NG_v|IndHaltv|FARv|RRBAv|RRBAHaltv|LongLoopv|RWLAcc_v|LongAccv|LongAccHaltv|CTL|CPS|RWL|Cubic|HaltingCryptid)')
def mirror(t): return t.replace('L','x').replace('R','L').replace('x','R')
def trans(t): return [t[i*7+b*3:i*7+b*3+3] for i in range(6) for b in range(2)]
def norm(x): return '---' if x[0]=='-' else x
def dist(a,b): return sum(1 for x,y in zip(map(norm,trans(a)),map(norm,trans(b))) if x!=y)
jobs=[];seen=set()
for h,d,t,fs in sorted(out,key=lambda o:o[1]):
    for f in fs:
        if skip.match(f): continue
        mir = dist(h,t)!=d
        key=(h,f)
        if sum(1 for j in jobs if j['h']==h and j['f']==f)>=2: continue
        jobs.append(dict(h=h,t=t,f=f,d=d,mirror=mir))
for i,j in enumerate(jobs): j['id']='TX%03d'%i
json.dump(jobs,open('jobs.json','w'),indent=0)
print(len(jobs), collections.Counter(j['mirror'] for j in jobs), collections.Counter(j['d'] for j in jobs))

# ---- write the job files ----
import json,os
import sys
V=sys.argv[1] if len(sys.argv)>1 else 'busycoq/verify'
jobs=json.load(open('jobs.json'))
def mirror(t): return t.replace('L','x').replace('R','L').replace('x','R')
for j in jobs:
    src=open(os.path.join(V,j['f']),errors='ignore').read()
    new=mirror(j['h']) if j['mirror'] else j['h']
    assert '"%s"'%j['t'] in src, j
    s=src.replace('"%s"'%j['t'],'"%s"'%new)
    open(os.path.join(V,j['id']+'.v'),'w').write(s)
print('ok')
