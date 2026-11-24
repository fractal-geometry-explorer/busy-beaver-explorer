"""Scan every undecided holdout for a driven end (see README.md): python3 pscan.py [STEPS] -> pscan.json"""
import subprocess,json,re,collections,sys
from concurrent.futures import ThreadPoolExecutor
import os
HERE=os.path.dirname(os.path.abspath(__file__))
fam=json.load(open(os.path.join(HERE,'..','..','holdouts','families.json')))
info={x['m']:(f['id'],x['st'],x['tc'],x['old']) for f in fam['families'] for x in f['machines']}
ms=sorted(info)
STEPS=sys.argv[1] if len(sys.argv)>1 else '100000000'
def analyze(m,es,side):
    try:
        out=subprocess.run([os.path.join(HERE,'pcross'),m,STEPS,es,side,'30'],capture_output=True,text=True,timeout=600).stdout.splitlines()
    except Exception as e: return None
    eras=[]
    for l in out:
        a=l.split()
        if len(a)<6 or a[0] in('HALT','OOB'): continue
        eras.append((int(a[0]),int(a[2]),int(a[3]),a[5]))
    if len(eras)<20: return None
    eras=eras[len(eras)//2:]  # second half
    units=collections.Counter(); pure=0; ncalls=[]; endsz=[]
    for e,sz,w,s in eras:
        ok = len(s)%2==0 and all(s[i].isupper() and s[i+1].islower() for i in range(0,len(s),2))
        if ok:
            pure+=1
            for i in range(0,len(s),2): units[s[i:i+2]]+=1
            ncalls.append(len(s)//2)
        endsz.append(sz)
    fun = len(set(u[0] for u in units))==len(units)
    return dict(m=m,es=es,side=side,eras=len(eras),pure=round(pure/len(eras),3),units=dict(units.most_common(6)),fun=fun,
                calls=(min(ncalls) if ncalls else 0, max(ncalls) if ncalls else 0, ncalls[-1] if ncalls else 0),
                endsz=(min(endsz),max(endsz),endsz[-1]))
jobs=[(m,es,side) for m in ms for es in 'LR' for side in 'LR']
with ThreadPoolExecutor(4) as ex:
    res=list(ex.map(lambda j: analyze(*j), jobs))
with open('pscan.json','w') as f: json.dump([r for r in res if r],f)
