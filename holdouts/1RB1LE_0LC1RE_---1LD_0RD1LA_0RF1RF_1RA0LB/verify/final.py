import pickle,random,subprocess,sys,os
from lib import *
from mymodel import *
F=pickle.load(open(sys.argv[1],'rb')); lv=F['lv']; tail=F['tail']
def S(ns):
    d=FRONTD[KIND[lv[0][0]]][:]
    for (pos,_),n in zip(lv,ns): d+=[4]*n+list(SEP[pos])
    d+=tail
    out=subprocess.run(['./sim2',from_digits(d),'100000000','5','0','1'],capture_output=True,text=True).stdout.split('\n')
    assert not any(l.startswith('V') for l in out)
    h=[l for l in out if l.startswith('HALT')][0].split()
    assert h[2]=='C' and h[3]=='-2' and h[-1]=='1',h[:4]
    return int(h[1])
m=len(lv); one=[1]*m; S1=S(one)
a=[]
for i in range(m):
    v=one[:]; v[i]=2; a.append(S(v)-S1)
random.seed(3)
for t in range(40):
    v=[random.randint(1,9) for _ in range(m)]
    assert S(v)==S1+sum(ai*(x-1) for ai,x in zip(a,v))
print('levels',m,'S(1..1)=',S1,'distinct slopes',sorted(set(a)),'additivity ok on 40 random n-vectors')
last=S1+sum(ai*(n-1) for ai,(p,n) in zip(a,lv))
halt=F['steps']+last
print('visit',F['visits']); print('HALT step',halt, 'digits',len(str(halt)))
ht=open(os.path.join(HERE,'..','halt.txt')).read().split()
print('visit equals halt.txt:',int(ht[1])==F['visits'],' step equals halt.txt:',int(ht[3])==halt)
import re
readme=open(os.path.join(HERE,'..','README.md')).read()
nums=re.findall(r'((?:    \d+\n)+)',readme); nums=[int(''.join(x.split())) for x in nums]
print('README numbers equal:',nums[0]==halt,nums[1]==F['visits'])
print('top level',lv[0][0],len(str(lv[0][1])),'digits; position histogram',sorted({p:[q for q,_ in lv].count(p) for p,_ in lv}.items()))
