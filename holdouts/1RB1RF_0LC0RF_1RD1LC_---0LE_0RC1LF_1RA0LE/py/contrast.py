"""contrast.py: can a shallow decision tree tell (a) the tapes that halt below level M from those that do not, and
(b) the tapes that join the blank-tape orbit from those that join another surviving orbit?

    gcc -O2 -o fates c/fates.c && ./fates 32768 ex.bin hl.bin && python3 py/contrast.py ex.bin 32768

Labels are exhaustive (c/fates.c), tapes with x even only (no rule leads to x odd).  Features: u = 2x/n and its
distance to 1/2 and 2/3, the first six tent digits of u, n, the parity of y, and x, y, n, d = 2x - y, y - (2x + 1),
y - (6x + 8) modulo 3, 4, 5, 7, 8, 9, 16.  Trained on the even levels of a band, tested on the odd levels; balanced
accuracy (0.5 = no better than a coin).  Needs scikit-learn.
"""
import sys
import numpy as np
from sklearn.tree import DecisionTreeClassifier
from sklearn.ensemble import RandomForestClassifier
from sklearn.metrics import balanced_accuracy_score
M = int(sys.argv[2])
ex = np.memmap(sys.argv[1], dtype=np.uint32, mode='r')
ns=np.arange(2,M+2); off=np.concatenate([[0],np.cumsum(ns//2)])
blank=int(ex[0+0])   # level 2, x = 1: B(1, 0)
def feats(x,y):
    n=2*x+y; d=2*x-y; u=2*x/n
    F=[u, abs(u-0.5), abs(u-2/3), n, y%2]
    names=['u','|u-1/2|','|u-2/3|','n','y odd']
    for v,nm in ((x,'x'),(y,'y'),(n,'n'),(d,'d'),(y-2*x-1,'y-(2x+1)'),(y-6*x-8,'y-(6x+8)')):
        for m in (3,4,5,7,8,9,16):
            F.append(v%m); names.append('%s mod %d'%(nm,m))
    # tent digits of u: first 6
    t=u
    for k in range(6):
        F.append(t<0.5); names.append('tent digit %d'%(k+1)); t=np.where(t<0.5,2*t,2-2*t)
    return np.column_stack(F),names
for n0,n1 in ((512,640),(1024,1280),(4096,4352),(16384,16512)):
    X=[];E=[];lv=[]
    for n in range(n0,n1):
        e=np.array(ex[off[n-2]:off[n-2]+n//2]); x=np.arange(1,n//2+1); k=x%2==0
        f,names=feats(x[k],n-2*x[k]); X.append(f); E.append(e[k]); lv.append(np.full(k.sum(),n))
    X=np.vstack(X);E=np.concatenate(E);lv=np.concatenate(lv); tr=lv%2==0; te=~tr
    surv=E!=0
    u,c=np.unique(E[surv],return_counts=True); o=np.argsort(-c)
    print('band %d..%d: %d tapes (x even), halting %.4f, on the blank orbit %.4f, classes %d'%(n0,n1,len(E),1-surv.mean(),(E==blank).mean(),len(u)))
    tasks=[('halts below level M',E==0,np.ones(len(E),bool))]
    tasks.append(('joins the blank-tape orbit (among survivors)',E==blank,surv))
    for name,lab,sel in tasks:
        if lab[sel].min()==lab[sel].max(): print('   ',name,': one class only'); continue
        for depth in (3,6):
            t=DecisionTreeClassifier(max_depth=depth,class_weight='balanced',random_state=0).fit(X[sel&tr],lab[sel&tr])
            p=t.predict(X[sel&te]); 
            print('    %-45s depth %d: balanced accuracy train %.3f test %.3f; top features: %s'%(name,depth,balanced_accuracy_score(lab[sel&tr],t.predict(X[sel&tr])),balanced_accuracy_score(lab[sel&te],p),', '.join(names[i] for i in np.argsort(-t.feature_importances_)[:3])))
        rf=RandomForestClassifier(n_estimators=100,max_depth=12,class_weight='balanced',n_jobs=1,random_state=0).fit(X[sel&tr],lab[sel&tr])
        print('    %-45s forest of 100 trees, depth 12: test %.3f'%(name,balanced_accuracy_score(lab[sel&te],rf.predict(X[sel&te]))))
