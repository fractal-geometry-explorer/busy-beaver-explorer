"""Compare the edge events of c/wrsim.cpp (mode 0) with those of c/plainev.c, cell for cell.

usage: python3 wrcheck.py WRSIM_OUT PLAINEV_OUT
"""
import sys
def expand(line):
    p=line.split(); st,side,q=p[0],p[1],p[2]; out=[]
    for tok in p[3:]:
        if tok in '<>': out.append('|'); continue
        w,_,c=tok.partition('^'); out.append(w*(int(c) if c else 1))
    return st,side,q,''.join(out)
a=[l for l in open(sys.argv[1]) if l[0].isdigit()]; b=[l for l in open(sys.argv[2]) if l[0].isdigit()]
n=min(len(a),len(b)); bad=0
for x,y in zip(a,b):
    ex=expand(x); py=y.split()
    # wrsim tape includes the blank cell? strip leading/trailing zeros outside visited is not needed
    if (ex[0],ex[1],ex[2],ex[3])!=(py[0],py[1],py[2],py[3]):
        bad+=1
        if bad<3: print('DIFF\n',x[:300],'\n',y[:300])
print('compared',n,'events, mismatches',bad)
