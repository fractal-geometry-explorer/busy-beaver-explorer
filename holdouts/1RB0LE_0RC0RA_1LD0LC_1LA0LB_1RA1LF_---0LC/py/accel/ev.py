from sim import *
from run1 import run
import sys
def allones(m): return [1 if i%2==0 else 3 for i in range(m)]
def event(L, m, n, K=3):
    s=config(L,allones(m),n)
    res=[]
    cnt=[0]
    def cb(t,tape,lo,pos):
        cnt[0]+=1
        s=bytes(tape[lo:pos]).translate(bytes.maketrans(b'\x00\x01',b'01')).decode()
        p=parseR(s)
        if p: res.append((cnt[0],t)+p); return True
        return cnt[0]>40
    r=run(s,10**7,cb)
    return r[0], res
if __name__=="__main__":
    L=expand(sys.argv[1]); m=int(sys.argv[2])
    for n in [1,2,3,5,10,20,37,64,100]:
        r,res=event(L,m,n)
        if res:
            c,t,L2,ds,n2=res[0]
            print(n, r, c, t, rle(L2), len(ds), set(ds), n2-n)
        else: print(n,r)
