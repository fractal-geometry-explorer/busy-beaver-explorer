import sys, json, time, pickle
from lib import *
from mymodel import *
C=json.load(open('const.json')); LA={int(k):v for k,v in C['A'].items()}; LB={int(k):v for k,v in C['B'].items()}
keep=int(sys.argv[1]) if len(sys.argv)>1 else 1
V0=int(sys.argv[2]) if len(sys.argv)>2 else 3040
check=float(sys.argv[3]) if len(sys.argv)>3 else 0
row=[l for l in sim('',40000000,V0,V0,1) if l[0]=='V'][0]
m=Model(row[3],LA,LB,{'H':0,'V':0},keep); m.visits=int(row[1]); m.steps=int(row[2])
if check:
    # compare with direct run at every model checkpoint up to `check` steps
    exp={}
    while m.steps<check:
        r=m.hit(); assert r is None
        exp[m.visits]=(m.steps,len(m.lv),m.full_digits())
    open('vl2.txt','w').write('\n'.join(map(str,sorted(exp)))+'\n')
    import subprocess
    out=subprocess.run(['./sim2','-',str(int(check*1.2)),'1','0','1','vl2.txt'],capture_output=True,text=True).stdout.split('\n')
    got={int(l.split()[1]):(int(l.split()[2]),digits(l.split()[3])) for l in out if l.startswith('V')}
    ok=sum(1 for v in exp if v in got and got[v]==(exp[v][0],exp[v][2]))
    print([l for l in out if l.startswith(('L','HALT','LIMIT'))])
    print('keep=%d from visit %d: %d/%d checkpoints (direct visits found %d) have equal step counts; last visit %d step %d; peeled levels %d; unpeels %d'%(keep,V0,ok,len(exp),len(got),max(exp),exp[max(exp)][0],len(m.lv),m.unpeels))
    sys.exit()
t0=time.time()
while True:
    r=m.hit()
    if r: break
lv,tail=m.all_levels()
print('reduced hits',m.nhits,'unpeels',m.unpeels,'max unpeel depth in one hit',m.maxunpeel,'time %.0fs'%(time.time()-t0))
print('levels',len(lv),'tail',fmt(tail)); print('halt info (steps in reduced last visit, sig, head pos, kind):',r)
print('visit number at start of last visit:',m.visits); print('steps at start of last visit:',m.steps)
pickle.dump({'lv':lv,'tail':tail,'visits':m.visits,'steps':m.steps,'r':r,'top':m.lv[0] if m.lv else None},open('final_keep%d.pkl'%keep,'wb'))
