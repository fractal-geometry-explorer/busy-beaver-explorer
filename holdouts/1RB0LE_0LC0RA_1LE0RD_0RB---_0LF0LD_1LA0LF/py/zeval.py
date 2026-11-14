import sys
sys.setrecursionlimit(100000)
# exact evaluation of the Z system on a list tape (in place), offsets absolute
def A(t,p):
    while len(t)<p+8: t.append(0)
    if t[p]==0: t[p]=1; return
    if t[p+1]==0 and t[p+2]==0: t[p]=0; A(t,p+3); return
    if t[p+1]==1 and t[p+2]==0: t[p]=0; t[p+1]=0; E(t,p+3); return
    if t[p+1:p+4]==[0,1,0]: A(t,p+4); A(t,p+4); return
    raise Exception('BAD A at %d: %s'%(p,t[p:p+6]))
def E(t,p):
    while len(t)<p+8: t.append(0)
    if t[p]==1 and t[p+1]==0: E(t,p+2); return
    if t[p]==0 and t[p+1]==0: t[p]=1; A(t,p+2); return
    if t[p:p+3]==[0,1,0]: t[p+1]=0; A(t,p+3); return
    raise Exception('BAD E at %d: %s'%(p,t[p:p+6]))
if __name__=='__main__':
    S=[]
    for k in range(1,int(sys.argv[1])+1):
        A(S,0); S=[1,0]+S
        while S and S[-1]==0: S.pop()
        print(k,''.join(map(str,S)))
