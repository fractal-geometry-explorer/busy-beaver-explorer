import random, sys, json
import contractsat as cs, check
def rnd(S):
    cells=[]
    for i in range(2*S):
        cells.append('%d%s%s'%(random.randint(0,1),random.choice('LR'),chr(65+random.randrange(S))))
    cells[random.randrange(1,2*S)]='---'
    return '_'.join(cells[2*i]+cells[2*i+1] for i in range(S))
def run(m,N):
    t=cs.parse(m); tape={}; pos=0; s=0
    for i in range(N):
        tr=t[(s,tape.get(pos,0))]
        if tr is None: return i
        tape[pos]=tr[0]; pos+=tr[1]; s=tr[2]
    return None
if __name__=='__main__':
    random.seed(int(sys.argv[1]))
    found=0; tried=0
    while tried<int(sys.argv[2]):
        m=rnd(3)
        if run(m,2000) is not None: continue
        tried+=1
        for side in 'LR':
            for (n,W) in ((1,1),(2,2),(3,3),(4,4)):
                e=cs.Enc(m,side=='R',n,W,verbose=False); c=e.solve(tlimit=5)
                if isinstance(c,dict):
                    check.check(json.loads(json.dumps(c)))
                    h=run(m,300000)
                    print(m,side,n,W,'CERT','HALTS-LATER!!' if h is not None else '')
                    found+=1; break
            else: continue
            break
        else: print(m,'none')
    print(found,'of',tried)
