"""Token-level simulator of the Z system of 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF (mirrored tape).

Tokens L = 1010, O = 000, I = 100; defects x = 10, 1 = 1, z = 0; tail O^inf.  See the README of this folder.
usage: tokz.py ROUNDS [FILE written by zeval.py, compared cell for cell]
Prints every 500th round and every round in which the defect did not end in the usual way (I O -> L) or ended
within 5 tokens of the end; raises an exception if two defects ever become adjacent.
"""
import sys
sys.setrecursionlimit(1000000)
# token-level Z system: tokens 'L','O','I', markers 'x','1','z'; implicit tail O^inf
T=[]
stats={'die':[], 'adj':0}
def An(n,i):
    while n>0:
        if i==len(T): T.append('O')
        t=T[i]
        if t=='L': i+=1; n*=2; continue
        if t=='O' or t=='I':
            tot=(t=='I')+n; T[i]='I' if tot&1 else 'O'; n=tot>>1; i+=1; continue
        if t=='z': T[i]='1'; n-=1; continue
        if t=='x':
            if i+1==len(T): T[i]='I'; stats['die'].append(('x-end',n,i)); continue
            u=T[i+1]
            if u=='O': T[i]='O'; T[i+1]='x'; n-=1; continue
            if u=='I': T[i]='L'; T[i+1]='O'; Eh(i+2); n-=1; continue
            if u=='L': T[i]='L'; T[i+1]='x'; i+=1; n*=2; continue
            raise Exception('ADJ x %s at %d'%(u,i))
        if t=='1':
            if i+1==len(T): T[i]='I'; stats['die'].append(('1-end',n,i)); continue
            T[i]='O'; Eh(i+1); n-=1; continue
        raise Exception('?')
def Eh(i):
    while True:
        if i==len(T): T.append('I'); stats['die'].append(('Eh-end',0,i)); return
        t=T[i]
        if t=='L': i+=1; continue
        if t=='O': T[i]='1'; return
        if t=='I': del T[i]; break
        raise Exception('ADJ Eh %s at %d'%(t,i))
    if i==len(T): T.append('L'); stats['die'].append(('E0-end',0,i)); return
    t=T[i]
    if t=='O': T[i]='L'; stats['die'].append(('IO',0,i,len(T))); return
    if t=='L': T[i]='O'; T.insert(i+1,'x'); An(1,i+1); return
    if t=='I': T[i]='O'; T.insert(i+1,'1'); return
    raise Exception('ADJ E0 %s at %d'%(t,i))
def cells():
    d={'L':'1010','O':'000','I':'100','x':'10','1':'1','z':'0'}
    return ''.join(d[t] for t in T).rstrip('0')
def norm():
    # front: x L^m U
    i=1
    while i<len(T) and T[i]=='L': i+=1
    for j in range(1,i): T[j-1]='L'
    T[i-1]='x'
    if i<len(T) and T[i]=='I': T[i-1]='L'; T[i]='z'
    elif i<len(T) and T[i] in 'x1z': raise Exception('front ADJ '+T[i])
if __name__=='__main__':
    R=int(sys.argv[1]); ref=None
    if len(sys.argv)>2: ref=[l.split()[1] for l in open(sys.argv[2])]
    # start: S_1 = 10 1 ... use cell-level start: S1='101' = x 1 ; emulate: T=['x','1']
    T[:]=list('LLLzLLOLOI')
    for k in range(6,R+1):
        stats['die']=[]
        An(1,0); T.insert(0,'x'); norm()
        while T and T[-1]=='O': T.pop()
        nm=sum(1 for t in T if t in 'x1z')
        c=cells()
        ok='' if ref is None or k>len(ref) else ('ok' if ref[k-1].rstrip('0')==c else 'MISMATCH')
        mg=min([d[3]-d[2] for d in stats['die'] if d[0]=='IO']+[999]); kinds=[d[0] for d in stats['die']]
        if k%500==0 or nm!=1 or mg<5 or kinds!=['IO']: print(k,len(T),'markers',nm,stats['die'],ok,flush=True)
