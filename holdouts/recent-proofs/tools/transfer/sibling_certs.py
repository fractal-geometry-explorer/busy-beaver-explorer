# P's own certificate run on the open same-table holdout H, started late, at every block phase.
import json,subprocess,re,sys
from concurrent.futures import ThreadPoolExecutor
jobs=json.load(open('sibjobs.json'))
def run(m,cert,to=420):
    return subprocess.run(['./runcert.sh',m,cert,str(to)],capture_output=True,text=True).stdout.strip()
def positions(m,N):
    tr={}
    for i in range(6):
        for b in range(2):
            t=m[i*7+b*3:i*7+b*3+3]
            tr[(i,b)]=None if t[0]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
    tape={};pos=0;s=0;out=[0]
    for _ in range(N):
        w,d,ns=tr[(s,tape.get(pos,0))]; tape[pos]=w; pos+=d; s=ns; out.append(pos)
    return out
tasks=[]; posc={}
for h,P,mir,perm,f,c in jobs:
    m=re.match(r'solve_cert \((CPS_LRU|RWL_mod|NG) (.*)\)\.',c or '')
    if not m: continue
    kind=m.group(1); a=m.group(2).split()
    variants=[a]
    i,j={'CPS_LRU':(5,6),'RWL_mod':(7,8),'NG':(4,5)}[kind]
    if a[i]!=a[j]: b=a[:]; b[i],b[j]=a[j],a[i]; variants.append(b)
    bsz=max(1,int(a[3])) if kind!='NG' else 1
    if h not in posc: posc[h]=positions(h,100200)
    pos=posc[h]
    for v in variants:
        for base in (1001,100001):
            seen=set()
            for t in range(base,base+150):
                r=pos[t]%bsz
                if r in seen: continue
                seen.add(r)
                w=v[:]; w[0]=str(t)
                tasks.append((h,P,f,kind+' '+' '.join(w)))
                if len(seen)==bsz or bsz>4 or base==1001: break
tasks=list(dict.fromkeys(tasks))
done={(l.split(' | ')[0],l.split(' | ')[3]) for fn in ('coqsweep.second','coqsweep2.out.prev') for l in (open(fn) if __import__('os').path.exists(fn) else []) if l.count(' | ')>=4}
tasks=[t for t in tasks if (t[0],t[3]) not in done]
tasks.sort(key=lambda t:int(t[3].split()[1]))
print(len(tasks),flush=True)
def job(t):
    return t+(run(t[0],t[3]),)
with ThreadPoolExecutor(int(sys.argv[1]) if len(sys.argv)>1 else 2) as ex:
    for r in ex.map(job,tasks): print(*r,sep=' | ',flush=True)
