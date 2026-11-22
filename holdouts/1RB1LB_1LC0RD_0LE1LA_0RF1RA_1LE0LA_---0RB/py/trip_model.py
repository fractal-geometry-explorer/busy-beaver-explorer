"""The whole machine as one map on tapes (lean/Trip.lean, lean/Token.lean), checked against the real run.

trip(c): c = cells from the trip's start cell (blank, head in A) to the last 1. Q = first 00. Output for cells
lo..Q+1: the automaton c'[p] = (c[p] == c[p+3]) with 1 1 0 imagined after Q, c'[Q+1] = 1; for each lone 1 at i < Q
with j words 110 after it, flip c'[i-2] and c'[i+1+3j] (the filled tape of Token.lean); 'HALT' if those words run
into a 0.

usage: python3 trip_model.py SNAPSHOTS, where each line is "step lo maxpos state cells" at every new leftmost cell
(as printed by tok-style simulators; see the README). Prints how many consecutive snapshot pairs the map reproduces.
"""
import sys
def trip(c):
    """c: cells from lo (head, 0) as string. returns predicted new cells list for positions lo..(q+1), or 'HALT'"""
    n=len(c); pad=c+'0'*12
    q=pad.find('00')
    ext=[int(x) for x in pad[:q+1]]+[1,1,0]
    out=[1 if ext[p]==ext[p+3] else 0 for p in range(q+1)]+[1]
    for i in range(1,q+1):
        if pad[i-1:i+2]=='010':
            j=0
            while pad[i+2+3*j:i+5+3*j]=='110': j+=1
            if pad[i+2+3*j]=='0': return 'HALT'
            out[i-2]^=1; out[i+1+3*j]^=1
    return out
if __name__=='__main__':
    L=[l.split() for l in open(sys.argv[1])]
    ok=bad=0
    for a,b in zip(L,L[1:]):
        loa=int(a[1]); ca_=a[4]; lob=int(b[1]); cb=b[4]; mx=int(b[2])
        if mx<=loa: continue
        out=trip(ca_)
        act=[int(cb[p+loa-lob]) if 0<=p+loa-lob<len(cb) else 0 for p in range(len(out))]
        rest_ok = cb[len(out)+loa-lob:] == ca_[len(out):].ljust(0)
        if out==act: ok+=1
        else:
            bad+=1
            if bad<6: print('bad',a[0],[p for p in range(len(out)) if out[p]!=act[p]][:10])
    print('ok',ok,'bad',bad)
