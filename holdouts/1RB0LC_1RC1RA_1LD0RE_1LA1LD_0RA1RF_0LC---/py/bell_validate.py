"""validate bell_wsim against direct simulation (c/tapeat, build: gcc -O2 -o /tmp/tapeat ../c/tapeat.c):
python3 bell_validate.py M STEPS EVERY_SAMPLES [path-to-tapeat]"""
import sys, subprocess, hashlib, time, tempfile
import os, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
_sp = importlib.util.spec_from_file_location("bell_wsim", os.path.join(HERE, "bell_wsim.py"))
wsim = importlib.util.module_from_spec(_sp); _sp.loader.exec_module(wsim)

M=sys.argv[1]; N=float(sys.argv[2]); EV=int(sys.argv[3])
s=wsim.WSim(M)
recs=[]
orig=s.sample
cnt=[0]
def tape():
    its,h=s.items()
    a=''.join(w*n for w,n in its[:h]); b=''.join(w*n for w,n in its[h:])
    if s.f==1:
        b=b if b else '0'
        t=a+'['+b[0]+']'+b[1:]
    else:
        a=a if a else '0'
        t=a[:-1]+'['+a[-1]+']'+b
    # trim zeros outside, keep head
    i=t.index('['); j=t.index(']')
    left=t[:i].lstrip('0'); right=t[j+1:].rstrip('0')
    return left+t[i:j+1]+right
def samp():
    r=orig(); cnt[0]+=1
    if cnt[0]%EV==0:
        recs.append((s.steps,'ABCDEF'[s.q],hashlib.md5(tape().encode()).hexdigest()))
    return r
s.sample=samp
t0=time.time(); r=s.run(N); print('wsim',r,s.steps,'jumps',s.jumps,'%.1fs'%(time.time()-t0),'records',len(recs),flush=True)
VT=tempfile.mktemp(); TAPEAT=sys.argv[4] if len(sys.argv)>4 else '/tmp/tapeat'
open(VT,'w').write('\n'.join(str(x[0]) for x in recs)+'\n')
p=subprocess.run([TAPEAT,M,VT],capture_output=True,text=True)
bad=0
for rec,line in zip(recs,p.stdout.splitlines()):
    t,q,tp=line.split()
    if int(t)!=rec[0] or q!=rec[1] or hashlib.md5(tp.encode()).hexdigest()!=rec[2]:
        bad+=1
        if bad<5: print('MISMATCH at',rec[0],q,rec[1])
print('checked',len(recs),'bad',bad)
