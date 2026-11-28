"""fates.py: tables from the exhaustive fates of c/fates.c (every zigzag start t(a, 0, r), t = y or Y, with level
N = a + r <= M, under the pass map).

    gcc -O2 -o fates c/fates.c && ./fates 16384 ex.bin hl.bin && python3 py/fates.py ex.bin hl.bin 16384

Table 1: for bands of start levels, the fraction of starts that halt below level M and the number of different
orbits on which the others leave level M.  Table 2: F(L), the fraction of the starts of levels [L/2, L) whose last
zigzag start before the halt has level in [L, 2L).
"""
import sys
import numpy as np
M = int(sys.argv[3])
ex = np.memmap(sys.argv[1], dtype=np.uint32, mode='r'); hl = np.memmap(sys.argv[2], dtype=np.uint32, mode='r')
off=np.zeros(M+2,dtype=np.int64); t=0
for N in range(M+2):
    off[N]=t
    if 5<=N<=M: t+=N-4
tot=t
def lev(tag,N): b=(tot if tag else 0)+off[N]; return slice(b,b+N-4)
blank=int(ex[lev(0,8)][0])   # y(3, 0, 5)
print('blank id',blank, 'unassigned',int(((np.array(ex)==0)&(np.array(hl)==0)).sum()))
print('band: tapes, halting fraction below M | classes among survivors, top shares, blank-orbit share')
for n0 in [2**k for k in range(6, 40) if 2**k < M]:
    n1=int(n0*1.125)
    e=np.concatenate([np.array(ex[lev(tg,N)]) for tg in (0,1) for N in range(n0,n1)])
    sv=e[e!=0]; u,c=np.unique(sv,return_counts=True); c=np.sort(c)[::-1]
    print(n0,len(e),'%.4f'%(e==0).mean(),'|',len(u),np.round(c[:3]/len(e),3),'%.4f'%((e==blank).mean()))
print('F(L): fraction of starts in levels [L/2, L) that halt from a level in [L, 2L)')
for L in [2**k for k in range(4, 40) if 2**(k+1) <= M]:
    h=np.concatenate([np.array(hl[lev(tg,N)]) for tg in (0,1) for N in range(L//2,L) if N>=5])
    hv,hc=np.unique(h[(h>=L)&(h<2*L)],return_counts=True)
    print(L,len(h),'%.5f'%(((h>=L)&(h<2*L)).mean()),'halting levels with mass:',len(hv))
