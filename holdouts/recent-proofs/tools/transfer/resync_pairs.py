import json,sys,collections
import os; sys.path.insert(0,os.path.join(os.path.dirname(os.path.abspath(__file__)),'../../../../tools/py'))
import syncpair
from multiprocessing import Pool
cand=json.load(open('cand_defined.json')); d=json.load(open('pool_raw.json'))
L='ABCDEF'
def relabel(P,mir,p):
    inv={int(p[s]):s for s in range(6)}
    rows=[]
    for s in range(6):
        r=''
        for b in range(2):
            x=P[int(p[s])*7+b*3:int(p[s])*7+b*3+3]
            if x!='---':
                dr=x[1]
                if mir: dr='L' if dr=='R' else 'R'
                x=x[0]+dr+L[inv[L.index(x[2])]]
            r+=x
        rows.append(r)
    return '_'.join(rows)
seen=set(); tasks=[]
for h,P,mir,p,k,hs,ps in cand:
    if p[0]!='0': continue
    Pp=relabel(P,mir,p)
    if (h,Pp) in seen: continue
    seen.add((h,Pp)); tasks.append((h,P,Pp,k,hs))
def job(t):
    h,P,Pp,k,hs=t
    assert sum(1 for i in range(12) if h[(i//2)*7+(i%2)*3:(i//2)*7+(i%2)*3+3]!=Pp[(i//2)*7+(i%2)*3:(i//2)*7+(i%2)*3+3])==1,(h,Pp)
    r=syncpair.resync(h,Pp,False,200000,K=60)
    return (h,P,Pp,L[k//2]+str(k%2),r[0],r[1],len(r[-1]),sum(r[-1].values()))
if __name__=='__main__':
    print(len(tasks),flush=True)
    with Pool(2) as pool:
        for r in pool.imap_unordered(job,tasks,chunksize=4):
            src=[f for f in d['busycoq'][r[1]] if not f.startswith('Eqv')]
            print(*r,src,flush=True)
