from sim import *
import sys
def run(tape_str, maxsteps, cb):
    N=len(tape_str)+ 4*10**5
    off=2*10**5
    tape=bytearray(N)
    for i,c in enumerate(tape_str): tape[off+i]=int(c)
    lo=off; hi=off+len(tape_str)  # hi = head pos
    pos=hi; st=1; t=0
    while t<maxsteps:
        r=tape[pos]
        tr=T[(st,r)]
        if tr is None: return ('halt',t,tape,pos,st)
        w,d,ns=tr
        tape[pos]=w; pos+=d; st=ns; t+=1
        if pos<lo: lo=pos
        if pos>hi:
            hi=pos
            if st==1:
                if cb(t,tape,lo,pos): return ('stop',t,tape,pos,st)
    return ('max',t,tape,pos,st)
if __name__=="__main__":
    m=int(sys.argv[1]); n=int(sys.argv[2]); K=int(sys.argv[3])
    ds=[1]+[3,1]*((m-1)//2)
    s=config(expand(L0),ds,n)
    cnt=[0]
    def cb(t,tape,lo,pos):
        cnt[0]+=1
        if cnt[0]%3==0 or cnt[0]<=12:
            s=bytes(tape[lo:pos]).translate(bytes.maketrans(b'\x00\x01',b'01')).decode()
            print(cnt[0],t,len(s),rle(s.lstrip('0'))[:300])
        return cnt[0]>=K
    print(run(s,10**8,cb)[:2])
