import sys,time,collections
import mac15b
from mac15b import run_fast, CACHE, active
maxsteps=int(float(sys.argv[1])); out=open(sys.argv[2],'w')
USED=collections.Counter()
orig=mac15b.rule
def rule2(c):
    r=orig(c)
    return r
t0=time.time(); last=[0]
def log(c,steps,rec):
    if time.time()-last[0]>10:
        last[0]=time.time()
        nonS=''.join(c[i] for i in range(1,len(c),2) if c[i]!='S')
        out.write('t=%.0f rec=%d steps=%.4e blocks=%d nonS=%s cache=%d tail=%s\n'%(time.time()-t0,rec,steps,len(c)//2+1,nonS,len(CACHE),' '.join(map(str,c[-6:])))); out.flush()
c,steps,rec=run_fast([10,'S',14,'S',6,'S',12],3513,0,10**18,maxsteps=maxsteps,log=log)
out.write('END rec=%d steps=%d blocks=%d cache=%d\n'%(rec,steps,len(c)//2+1,len(CACHE)))
import pickle; pickle.dump((c,steps,rec,{k:v for k,v in CACHE.items() if v!='TOUCH'}),open(sys.argv[2]+'.pkl','wb'))
